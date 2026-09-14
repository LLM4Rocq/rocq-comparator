(* The inner pipeline (DESIGN.md section 3, steps 1-5; section 16 for
   projects).

   The modules this depends on are injected as a record of functions so the
   orchestration can be tested on its own. *)

open Names

type hooks = {
  filter :
    strict:bool -> permitted_plugins:string list -> permitted_libraries:string list ->
    Vernacexpr.vernac_control -> (unit, string) result;
  assumptions :
    permitted:string list -> (string * Constant.t) list -> Verdict.target_report list ->
    ( Verdict.target_report list,
      Verdict.reason * string * Verdict.target_report list )
    result;
  envcheck :
    top:DirPath.t -> trusted_roots:string list -> permitted_libraries:string list ->
    impredicative_set:bool -> indices_matter:bool -> (unit, Verdict.reason * string) result;
  trusted_roots : Config.t -> string list;
  rocqchk :
    (top:DirPath.t -> norec:DirPath.t list -> vo_dir:string -> loadpath_args:string list ->
     deadline:float -> (unit, string) result)
    option;
      (** [None] = rocqchk unavailable, check "rocqchk" Skipped.  [norec]: the
          untrusted helper libraries to replay besides [top]; [vo_dir]: where
          the top .vo is saved. *)
  filter_status : Verdict.check_status;
  (** [Ok] normally; [Fail "..."] when the strict filter has been disabled by
      the test-only escape hatch, so that a verdict produced without the
      filter can never be mistaken for a normal one *)
}

let permissive_hooks =
  { filter = (fun ~strict:_ ~permitted_plugins:_ ~permitted_libraries:_ _ -> Result.Ok ());
    assumptions = (fun ~permitted:_ _ reports -> Result.Ok reports);
    envcheck =
      (fun ~top:_ ~trusted_roots:_ ~permitted_libraries:_ ~impredicative_set:_ ~indices_matter:_ ->
         Result.Ok ());
    trusted_roots = (fun _ -> []);
    rocqchk = None;
    filter_status = Verdict.Fail "permissive hooks" }

let check_names =
  [ "filter"; "challenge_compile"; "solution_compile"; "joined"; "statements"; "closure";
    "axioms"; "hygiene"; "libraries"; "rocqchk" ]

(* the verdict's [checks] field, in the fixed order, defaulting to Skipped *)
let build_checks (tbl : (string, Verdict.check_status) Hashtbl.t) =
  List.map
    (fun n -> (n, match Hashtbl.find_opt tbl n with Some s -> s | None -> Verdict.Skipped))
    check_names

let describe_error (e : Driver.sentence_error) =
  let loc = match e.Driver.line with Some l -> Printf.sprintf "line %d: " l | None -> "" in
  let text = if e.Driver.text = "" then "" else " [in: " ^ e.Driver.text ^ "]" in
  loc ^ e.Driver.msg ^ text

let dirpath_of_string s =
  match Libnames.dirpath_of_string s with
  | dp -> dp
  | exception _ -> DirPath.make [ Id.of_string_soft s ]

(* ---- libraries the comparator wrote in this run --------------------------- *)

(* A .vo this run saved into the scratch mirrors: its logical name, path and
   digest at save time.  The trusted ones are written by the trusted phase
   (a separate sandboxed process that alone may write scratch/trusted) and
   read back here; the untrusted ones are recorded as they are saved. *)
type saved = { s_name : string; s_path : string; s_digest : string; s_trusted : bool }

let libraries_file scratch = Filename.concat (Plan.trusted_dir scratch) "libraries.json"

let write_trusted_libraries ~scratch (l : saved list) =
  let j =
    `List
      (List.map
         (fun s -> `Assoc [ ("name", `String s.s_name); ("path", `String s.s_path); ("digest", `String s.s_digest) ])
         l)
  in
  let oc = open_out_bin (libraries_file scratch) in
  Yojson.Safe.to_channel oc j;
  close_out oc

let read_trusted_libraries ~scratch : saved list =
  match Yojson.Safe.from_file (libraries_file scratch) with
  | `List l ->
    List.filter_map
      (fun e ->
         let str k = match e with `Assoc a -> (match List.assoc_opt k a with Some (`String s) -> Some s | _ -> None) | _ -> None in
         match str "name", str "path", str "digest" with
         | Some s_name, Some s_path, Some s_digest -> Some { s_name; s_path; s_digest; s_trusted = true }
         | _ -> None)
      l
  | _ -> []
  | exception _ -> []

let digest_of path = try Digest.to_hex (Digest.file path) with _ -> ""

let located dp =
  match Loadpath.locate_absolute_library dp with
  | Result.Ok p -> Some p
  | Result.Error _ -> None
  | exception _ -> None

(* Every loaded library that lives under the run's scratch must be one this
   run saved, byte for byte (its digest now equals the digest at save time).
   Anything else under scratch, and any saved library that has changed since,
   is a library violation.  Installed libraries are left to Envcheck. *)
let scratch_libraries_ok ~scratch ~(saved : saved list) ~(top : DirPath.t) :
  (unit, Verdict.reason * string) result =
  let scratch = Config.normalize_path scratch in
  List.fold_left
    (fun acc dp ->
       match acc with
       | Result.Error _ -> acc
       | Result.Ok () ->
         if DirPath.equal dp top then acc
         else
           match located dp with
           | None -> acc
           | Some path ->
             if not (Config.is_under ~root:scratch path) then acc
             else
               let name = DirPath.to_string dp in
               match List.find_opt (fun s -> s.s_path = path) saved with
               | None ->
                 Result.Error
                   (Verdict.Library_violation,
                    "the library " ^ name ^ " was loaded from " ^ path
                    ^ ", which the comparator did not write in this run")
               | Some s when s.s_digest <> digest_of path ->
                 Result.Error
                   (Verdict.Library_violation,
                    "the library " ^ name ^ " at " ^ path ^ " was modified after the comparator wrote it")
               | Some _ -> acc)
    (Result.Ok ()) (Library.loaded_libraries ())

(* Reproducibility manifest (DESIGN-audit tier 4, feature 1).

   Snapshots the ambient inputs the run used and would otherwise discard: the
   OCaml compiler version, the comparator version, the trusted load-path roots,
   and every loaded .vo with its on-disk digest and where its trust comes
   from.  Called after a library has compiled, so [Library.loaded_libraries
   ()] reflects everything the run pulled in.  Deterministic: libraries and
   roots are sorted, digests are hex.  Any I/O failure degrades to an empty
   path/digest rather than aborting -- the manifest is an audit aid, never a
   gate (the gate is [scratch_libraries_ok]). *)
let build_manifest ~(trusted_roots : string list) ~(saved : saved list) : Verdict.manifest =
  let libs =
    List.map
      (fun dp ->
         let name = DirPath.to_string dp in
         let path = match located dp with Some p -> p | None -> "" in
         let digest = if path <> "" && Sys.file_exists path then digest_of path else "" in
         let trust =
           match List.find_opt (fun s -> s.s_path = path) saved with
           | Some { s_trusted = true; _ } -> "trusted"
           | Some _ -> "checked"
           | None -> "installed"
         in
         { Verdict.lib_name = name; lib_path = path; lib_digest = digest; lib_trust = trust })
      (Library.loaded_libraries ())
  in
  let libs =
    List.sort (fun a b -> String.compare a.Verdict.lib_name b.Verdict.lib_name) libs
  in
  { Verdict.ocaml_version = Sys.ocaml_version;
    comparator_version = Verdict.comparator_version;
    trusted_roots = List.sort_uniq String.compare trusted_roots;
    libraries = libs }

(* Pretty-print a kernel type for the human-facing validate report.  Never
   raises: a term that cannot be externalised prints as a placeholder. *)
let pp_type (env : Environ.env) (c : Constr.t) : string =
  try
    let sigma = Evd.from_env env in
    Pp.string_of_ppcmds (Printer.pr_ltype_env env sigma c)
  with _ -> "<unprintable>"

(* ---- shared pieces --------------------------------------------------------- *)

let filters (h : hooks) (cfg : Config.t) ~(plan : Plan.t) =
  (* a non-empty permitted_libraries must let the project's own prefixes
     through, or no helper could be Required at all *)
  let permitted_libraries =
    match cfg.Config.permitted_libraries with
    | [] -> []
    | l -> l @ Plan.binding_logicals plan
  in
  let lenient vc =
    h.filter ~strict:false ~permitted_plugins:cfg.Config.permitted_plugins ~permitted_libraries:[] vc
  in
  let strict vc =
    h.filter ~strict:true ~permitted_plugins:cfg.Config.permitted_plugins ~permitted_libraries vc
  in
  (lenient, strict, permitted_libraries)

let describe_outcome = function
  | Driver.Error e | Driver.Parse_error e -> describe_error e
  | Driver.Timeout t -> "timeout on: " ^ t
  | Driver.Forbidden (what, e) -> what ^ " (" ^ describe_error e ^ ")"
  | Driver.Done _ -> "ok"

(* Compile one side's helpers in dependency order, saving each .vo into its
   mirror.  An untrusted helper is scanned by the hygiene check under its own
   name before being saved (Envcheck only looks at the current top), and the
   scratch libraries it loaded are verified.  Returns the saved list. *)
let compile_helpers (h : hooks) (cfg : Config.t) ~plan ~scratch ~trusted ~deadline
    ~filter ~trusted_roots ~permitted_libraries ~(saved : saved list) :
  (saved list, Verdict.reason * string) result =
  let entries = if trusted then plan.Plan.trusted else plan.Plan.untrusted in
  List.fold_left
    (fun acc (e : Plan.entry) ->
       match acc with
       | Result.Error _ -> acc
       | Result.Ok saved -> (
         let where = e.Plan.name ^ " (" ^ e.Plan.path ^ ")" in
         match Driver.compile_library ~filter ~deadline ~top:e.Plan.logical ~file:e.Plan.path () with
         | Driver.Done _ -> (
           let hygiene =
             if trusted then Result.Ok ()
             else
               h.envcheck ~top:e.Plan.logical ~trusted_roots ~permitted_libraries
                 ~impredicative_set:cfg.Config.impredicative_set
                 ~indices_matter:cfg.Config.indices_matter
           in
           match hygiene with
           | Result.Error (r, d) -> Result.Error (r, where ^ ": " ^ d)
           | Result.Ok () -> (
             match scratch_libraries_ok ~scratch ~saved ~top:e.Plan.logical with
             | Result.Error (r, d) -> Result.Error (r, where ^ ": " ^ d)
             | Result.Ok () -> (
               match Rocqchk.save_vo ~top:e.Plan.logical ~dir:(Plan.vo_dir ~scratch ~trusted e) with
               | Result.Error d ->
                 Result.Error ((if trusted then Verdict.Challenge_error else Verdict.Internal_error), where ^ ": " ^ d)
               | Result.Ok path ->
                 Result.Ok
                   ({ s_name = e.Plan.name; s_path = path; s_digest = digest_of path; s_trusted = trusted }
                    :: saved))))
         | (Driver.Error _ | Driver.Parse_error _) as o ->
           Result.Error ((if trusted then Verdict.Challenge_error else Verdict.Compile_error),
                         where ^ ": " ^ describe_outcome o)
         | Driver.Timeout _ as o ->
           Result.Error ((if trusted then Verdict.Challenge_error else Verdict.Timeout),
                         where ^ ": " ^ describe_outcome o)
         | Driver.Forbidden (what, _) as o ->
           Result.Error ((if trusted then Verdict.Challenge_error else Verdict.Forbidden_command),
                         where ^ ": " ^ (if trusted then "uses a command the comparator cannot allow, " ^ what else describe_outcome o))))
    (Result.Ok saved) entries

let with_rocq_exceptions (finish : Verdict.reason -> string -> Verdict.t) f =
  try f () with
  | Sys.Break -> finish Verdict.Internal_error "interrupted"
  | e ->
    let e, info = Exninfo.capture e in
    finish Verdict.Internal_error (Pp.string_of_ppcmds (CErrors.iprint (e, info)))

(* ---- the trusted phase ------------------------------------------------------ *)

(* Compiles the trusted helpers (the challenge's project closure) into
   scratch/trusted and records what it wrote.  Runs in its own sandboxed
   process, the only one allowed to write there: once it has returned, the
   solution phase can read those .vo files but never change them.  A verdict
   with [ok = true] means "go on"; anything else is the run's verdict. *)
let run_trusted (h : hooks) (cfg : Config.t) ~(scratch : string) : Verdict.t =
  let checks = Hashtbl.create 16 in
  let timing = ref [] in
  let finish reason detail =
    { (Verdict.fail ~checks:(build_checks checks) ~timing:(List.rev !timing) reason detail)
      with Verdict.rocq_version = Driver.rocq_version () }
  in
  Hashtbl.replace checks "filter" h.filter_status;
  with_rocq_exceptions finish (fun () ->
      match Plan.make cfg with
      | Result.Error (r, d) -> finish r d
      | Result.Ok plan -> (
        Plan.mkdirs plan ~scratch ~trusted:true;
        let t0 = Unix.gettimeofday () in
        Driver.init ~args:(Config.rocq_args cfg @ Plan.mirror_args ~trusted_only:true plan ~scratch);
        timing := ("init", Unix.gettimeofday () -. t0) :: !timing;
        match Plan.check_installed plan with
        | Result.Error (r, d) ->
          Hashtbl.replace checks "libraries" (Verdict.Fail d);
          finish r d
        | Result.Ok () -> (
          let lenient, _, permitted_libraries = filters h cfg ~plan in
          let deadline = Unix.gettimeofday () +. cfg.Config.timeout_s in
          let t0 = Unix.gettimeofday () in
          let r =
            compile_helpers h cfg ~plan ~scratch ~trusted:true ~deadline ~filter:lenient
              ~trusted_roots:(h.trusted_roots cfg @ Plan.mirror_dirs plan ~scratch)
              ~permitted_libraries ~saved:[]
          in
          timing := ("trusted", Unix.gettimeofday () -. t0) :: !timing;
          match r with
          | Result.Error (r, d) ->
            Hashtbl.replace checks "challenge_compile" (Verdict.Fail d);
            finish r ("a trusted project file does not compile: " ^ d)
          | Result.Ok saved ->
            write_trusted_libraries ~scratch (List.rev saved);
            { (Verdict.pass ~checks:(build_checks checks) ~timing:(List.rev !timing) ())
              with Verdict.rocq_version = Driver.rocq_version () })))

(* The trusted phase's record, checked against the plan: the same files, on
   disk, unchanged. *)
let trusted_saved ~scratch (plan : Plan.t) : (saved list, string) result =
  if plan.Plan.trusted = [] then Result.Ok []
  else
    let saved = read_trusted_libraries ~scratch in
    let expected = List.map (fun (e : Plan.entry) -> (e.Plan.name, Plan.vo_path ~scratch ~trusted:true e)) plan.Plan.trusted in
    let missing =
      List.find_opt
        (fun (name, path) ->
           not (List.exists (fun s -> s.s_name = name && s.s_path = path && s.s_digest = digest_of path) saved))
        expected
    in
    match missing with
    | Some (name, _) -> Result.Error ("the trusted phase did not produce " ^ name ^ " as planned")
    | None ->
      if List.length saved <> List.length expected then
        Result.Error "the trusted phase produced libraries that are not in the plan"
      else Result.Ok saved

(* ---- the solution phase ------------------------------------------------------ *)

let run_inner (h : hooks) (cfg : Config.t) ~(scratch : string) : Verdict.t =
  let checks = Hashtbl.create 16 in
  let timing = ref [] in
  let time name f =
    let t0 = Unix.gettimeofday () in
    let r = f () in
    timing := (name, Unix.gettimeofday () -. t0) :: !timing;
    r
  in
  let finish ?(targets = []) reason detail =
    Verdict.fail ~checks:(build_checks checks) ~targets ~timing:(List.rev !timing) reason detail
  in
  (* The manifest is only meaningful once a library has actually loaded its
     dependencies, so it is filled in after the solution compiles and stamped
     onto every verdict returned from that point on. *)
  let manifest_ref = ref None in
  let with_version (v : Verdict.t) =
    { v with Verdict.rocq_version = Driver.rocq_version (); manifest = !manifest_ref }
  in
  let deadline = Unix.gettimeofday () +. cfg.Config.timeout_s in
  (* A signature-style challenge ("Parameter P : Prop.", "Axiom ax : ...",
     "Lemma helper : X. Admitted.") is part of the specification: the target's
     statement and proof are meant to rest on those declarations, so they are
     permitted assumptions and are pinned in the solution (same statement, and
     either still assumed or honestly proved). The challenge is trusted input,
     which is what makes this safe; a challenge that wants the strict
     behaviour turns it off. *)
  let permit_challenge_axioms = cfg.Config.permit_challenge_axioms in
  Hashtbl.replace checks "filter" h.filter_status;
  with_rocq_exceptions (fun r d -> with_version (finish r d)) (fun () ->
    (* 0. plan (empty without a project: everything below is then as before) *)
    match Plan.make cfg with
    | Result.Error (r, d) -> with_version (finish r d)
    | Result.Ok plan ->
    match trusted_saved ~scratch plan with
    | Result.Error d -> with_version (finish Verdict.Internal_error d)
    | Result.Ok saved ->
    Plan.mkdirs plan ~scratch ~trusted:false;
    (* 1. init *)
    time "init" (fun () -> Driver.init ~args:(Config.rocq_args cfg @ Plan.mirror_args plan ~scratch));
    let top = dirpath_of_string (Project.top_name cfg) in
    let trusted_roots = h.trusted_roots cfg @ Plan.mirror_dirs plan ~scratch in
    let lenient, strict, permitted_libraries = filters h cfg ~plan in
    match Plan.check_installed plan with
    | Result.Error (r, d) ->
      Hashtbl.replace checks "libraries" (Verdict.Fail d);
      with_version (finish r d)
    | Result.Ok () ->
    (* 2. challenge *)
    let challenge =
      time "challenge" (fun () ->
          Driver.compile_library ~filter:lenient ~deadline ~top ~file:(Config.challenge_path cfg) ())
    in
    (match challenge with
     | Driver.Done _ -> Hashtbl.replace checks "challenge_compile" Verdict.Ok
     | _ -> ());
    match challenge with
    | Driver.Error e | Driver.Parse_error e ->
      Hashtbl.replace checks "challenge_compile" (Verdict.Fail (describe_error e));
      with_version (finish Verdict.Challenge_error ("the challenge does not compile: " ^ describe_error e))
    | Driver.Timeout t ->
      Hashtbl.replace checks "challenge_compile" (Verdict.Fail "timeout");
      with_version (finish Verdict.Challenge_error ("the challenge timed out on: " ^ t))
    | Driver.Forbidden (what, e) ->
      Hashtbl.replace checks "challenge_compile" (Verdict.Fail what);
      with_version
        (finish Verdict.Challenge_error
           ("the challenge uses a command the comparator cannot allow (" ^ what ^ "): "
            ^ describe_error e))
    | Driver.Done _ -> (
      (* the challenge may only have loaded installed and trusted libraries
         (the untrusted mirrors are still empty at this point, so this cannot
         fail for a resolution reason; it is the digest gate) *)
      match scratch_libraries_ok ~scratch ~saved ~top with
      | Result.Error (r, d) ->
        Hashtbl.replace checks "libraries" (Verdict.Fail d);
        with_version (finish r d)
      | Result.Ok () ->
      (* 3. SPEC *)
      match
        Spec.extract ~trusted:(List.map (fun (e : Plan.entry) -> e.Plan.logical) plan.Plan.trusted)
          ~top ~theorem_names:cfg.Config.theorem_names
          ~definition_names:cfg.Config.definition_names
          ~permitted_axioms:cfg.Config.permitted_axioms ~permit_challenge_axioms ()
      with
      | Result.Error (r, d) -> with_version (finish r d)
      | Result.Ok spec -> (
        (* 4a. untrusted helpers, strict filter, same deadline as the solution *)
        let helpers =
          time "helpers" (fun () ->
              compile_helpers h cfg ~plan ~scratch ~trusted:false ~deadline ~filter:strict
                ~trusted_roots ~permitted_libraries ~saved)
        in
        match helpers with
        | Result.Error (r, d) ->
          Hashtbl.replace checks "solution_compile" (Verdict.Fail d);
          with_version (finish r d)
        | Result.Ok saved ->
        (* 4b. solution *)
        let solution =
          time "solution" (fun () ->
              Driver.compile_library ~filter:strict ~deadline ~top
                ~file:(Config.solution_path cfg) ())
        in
        match solution with
        | Driver.Error e | Driver.Parse_error e ->
          Hashtbl.replace checks "solution_compile" (Verdict.Fail (describe_error e));
          with_version (finish Verdict.Compile_error (describe_error e))
        | Driver.Timeout t ->
          Hashtbl.replace checks "solution_compile" (Verdict.Fail "timeout");
          with_version (finish Verdict.Timeout ("the solution timed out on: " ^ t))
        | Driver.Forbidden (what, e) ->
          Hashtbl.replace checks "solution_compile" (Verdict.Fail what);
          with_version (finish Verdict.Forbidden_command (what ^ " (" ^ describe_error e ^ ")"))
        | Driver.Done _ ->
          Hashtbl.replace checks "solution_compile" Verdict.Ok;
          manifest_ref := Some (build_manifest ~trusted_roots:(h.trusted_roots cfg) ~saved);
          let env_s = Global.env () in
          let joined = Safe_typing.is_joined_environment (Global.safe_env ()) in
          Hashtbl.replace checks "joined"
            (if joined then Verdict.Ok
             else Verdict.Fail "a delayed opaque proof was not joined");
          (* 5. compare *)
          let reports, cmp_error = time "compare" (fun () -> Compare.check_targets spec env_s) in
          (match cmp_error with
           | None ->
             Hashtbl.replace checks "statements" Verdict.Ok;
             Hashtbl.replace checks "closure" Verdict.Ok
           | Some (Verdict.Dependency_mismatch, d) ->
             Hashtbl.replace checks "statements" Verdict.Ok;
             Hashtbl.replace checks "closure" (Verdict.Fail d)
           | Some (_, d) -> Hashtbl.replace checks "statements" (Verdict.Fail d));
          if not joined then
            with_version
              (finish ~targets:reports Verdict.Unsafe_flags
                 "the environment is not joined: a delayed opaque proof remains unchecked")
          else (
            match cmp_error with
            | Some (r, d) -> with_version (finish ~targets:reports r d)
            | None -> (
              (* 6. axioms *)
              let proved =
                List.filter_map
                  (fun (t : Spec.target) ->
                     if List.exists
                         (fun (r : Verdict.target_report) ->
                            String.equal r.Verdict.name t.Spec.name
                            && String.equal r.Verdict.status "proved")
                         reports
                     then Some (t.Spec.name, t.Spec.kn)
                     else None)
                  spec.Spec.targets
              in
              (* Assumptions matches names by CANONICAL kernel name, so that
                 is the spelling the challenge's own axioms must be added
                 under: a constant reached through an alias is still the same
                 kernel object and must be recognised as permitted. *)
              let permitted =
                cfg.Config.permitted_axioms
                @ List.map
                    (fun (c, _) -> KerName.to_string (Constant.canonical c))
                    spec.Spec.challenge_axioms
                (* Imported policy: also permit any axiom defined in a library
                   the challenge Require'd, as a "<library>.*" wildcard. So a
                   challenge built on a classical library (mathcomp-analysis,
                   Reals, ...) accepts that library's axioms with no per-axiom
                   list, while an axiom the solution itself declares (in its own
                   top or in an untrusted helper) is still rejected. *)
                @ (match cfg.Config.axiom_policy with
                   | Config.Listed -> []
                   | Config.Imported ->
                     List.map (fun lib -> lib ^ ".*") spec.Spec.imported_libraries)
              in
              match h.assumptions ~permitted proved reports with
              | Result.Error (r, d, reports) ->
                Hashtbl.replace checks "axioms" (Verdict.Fail d);
                with_version (finish ~targets:reports r d)
              | Result.Ok reports -> (
                Hashtbl.replace checks "axioms" Verdict.Ok;
                (* 7. hygiene + libraries.  The shadowing check (a project
                   directory bound to an installed namespace) and the scratch
                   gate (every .vo under scratch is one this run wrote, and
                   is unchanged) are library violations and run first, before
                   the per-constant hygiene scan, because they invalidate the
                   meaning of every loaded name. *)
                match
                  match Shadowing.check ~top with
                  | Result.Error e -> Result.Error e
                  | Result.Ok () ->
                    match scratch_libraries_ok ~scratch ~saved ~top with
                    | Result.Error e -> Result.Error e
                    | Result.Ok () ->
                      h.envcheck ~top ~trusted_roots ~permitted_libraries
                        ~impredicative_set:cfg.Config.impredicative_set
                        ~indices_matter:cfg.Config.indices_matter
                with
                | Result.Error (Verdict.Library_violation, d) ->
                  Hashtbl.replace checks "hygiene" Verdict.Ok;
                  Hashtbl.replace checks "libraries" (Verdict.Fail d);
                  with_version (finish ~targets:reports Verdict.Library_violation d)
                | Result.Error (r, d) ->
                  Hashtbl.replace checks "hygiene" (Verdict.Fail d);
                  with_version (finish ~targets:reports r d)
                | Result.Ok () -> (
                  Hashtbl.replace checks "hygiene" Verdict.Ok;
                  Hashtbl.replace checks "libraries" Verdict.Ok;
                  (* 8. rocqchk (last: it ends the library) *)
                  match h.rocqchk with
                  | None ->
                    Hashtbl.replace checks "rocqchk" Verdict.Skipped;
                    with_version
                      (Verdict.pass ~checks:(build_checks checks) ~targets:reports
                         ~timing:(List.rev !timing) ())
                  | Some f -> (
                    let vo_dir = Filename.concat (Plan.untrusted_dir scratch) "top" in
                    let norec = List.map (fun (e : Plan.entry) -> e.Plan.logical) plan.Plan.untrusted in
                    let r =
                      time "rocqchk" (fun () ->
                          Plan.mkdir_p vo_dir;
                          f ~top ~norec ~vo_dir
                            ~loadpath_args:(Config.loadpath_args cfg @ Plan.mirror_args plan ~scratch)
                            ~deadline)
                    in
                    match r with
                    | Result.Ok () ->
                      Hashtbl.replace checks "rocqchk" Verdict.Ok;
                      with_version
                        (Verdict.pass ~checks:(build_checks checks) ~targets:reports
                           ~timing:(List.rev !timing) ())
                    | Result.Error d ->
                      Hashtbl.replace checks "rocqchk" (Verdict.Fail d);
                      with_version (finish ~targets:reports Verdict.Rocqchk_failed d)))))))))

(* Dry-run / validate-challenge (DESIGN-audit tier 4, feature 2).

   Compiles ONLY the challenge (with the lenient filter, since the challenge is
   trusted input just as in [run_inner]), after its trusted helpers were built
   by the trusted phase, extracts the SPEC and reports what an operator is
   about to publish -- each target's resolution, kind and type, and the
   axioms the challenge declares -- without needing a solution.  It reuses
   the same inner-side machinery; [bin/main.ml] runs it inside the same
   sandbox as [run_inner]. *)
let validate_inner (h : hooks) (cfg : Config.t) ~(scratch : string) : Verdict.validation =
  let rocq_version = Driver.rocq_version () in
  let top_name = Project.top_name cfg in
  let top = dirpath_of_string top_name in
  let mk ?(ok = false) ?error ?(targets = []) ?(axioms = []) ?manifest () =
    { Verdict.v_ok = ok; v_error = error; v_rocq_version = rocq_version; v_top = top_name;
      v_targets = targets; v_challenge_axioms = axioms; v_manifest = manifest }
  in
  try
    match Plan.make ~with_solution:false cfg with
    | Result.Error (_, d) -> mk ~error:d ()
    | Result.Ok plan ->
    match trusted_saved ~scratch plan with
    | Result.Error d -> mk ~error:d ()
    | Result.Ok saved ->
    Driver.init ~args:(Config.rocq_args cfg @ Plan.mirror_args ~trusted_only:true plan ~scratch);
    match Plan.check_installed plan with
    | Result.Error (_, d) -> mk ~error:d ()
    | Result.Ok () ->
    let lenient, _, _ = filters h cfg ~plan in
    match Driver.compile_library ~filter:lenient ~top ~file:(Config.challenge_path cfg) () with
    | Driver.Error e | Driver.Parse_error e ->
      mk ~error:("the challenge does not compile: " ^ describe_error e) ()
    | Driver.Timeout t -> mk ~error:("the challenge timed out on: " ^ t) ()
    | Driver.Forbidden (what, e) ->
      mk ~error:("the challenge uses a command the comparator cannot allow (" ^ what ^ "): "
                 ^ describe_error e) ()
    | Driver.Done _ -> (
      let env = Global.env () in
      let manifest = build_manifest ~trusted_roots:(h.trusted_roots cfg) ~saved in
      match
        Spec.extract ~trusted:(List.map (fun (e : Plan.entry) -> e.Plan.logical) plan.Plan.trusted)
          ~top ~theorem_names:cfg.Config.theorem_names
          ~definition_names:cfg.Config.definition_names
          ~permitted_axioms:cfg.Config.permitted_axioms
          ~permit_challenge_axioms:cfg.Config.permit_challenge_axioms ()
      with
      | Result.Ok spec ->
        let targets =
          List.map
            (fun (t : Spec.target) ->
               { Verdict.vt_name = t.Spec.name; vt_resolves = true;
                 vt_kind = (if t.Spec.hole then "definition_hole" else "theorem");
                 vt_type = Some (pp_type env t.Spec.typ) })
            spec.Spec.targets
        in
        let axioms =
          List.sort_uniq String.compare
            (List.map (fun (c, _) -> Names.Constant.to_string c) spec.Spec.challenge_axioms)
        in
        mk ~ok:true ~targets ~axioms ~manifest ()
      | Result.Error (_, d) ->
        (* SPEC extraction failed (usually a target that does not resolve).
           Report per-name resolution so the operator sees which names are the
           problem; the axiom list needs a clean SPEC, so it is left empty. *)
        let declared =
          List.map (fun n -> (n, false)) cfg.Config.theorem_names
          @ List.map (fun n -> (n, true)) cfg.Config.definition_names
        in
        let unresolved name =
          { Verdict.vt_name = name; vt_resolves = false; vt_kind = "unresolved"; vt_type = None }
        in
        let targets =
          List.map
            (fun (name, hole) ->
               match Spec.resolve_name ~top name with
               | Result.Ok kn when Spec.is_local ~top (Names.Constant.modpath kn) -> (
                 match Environ.lookup_constant_opt kn env with
                 | Some cb ->
                   { Verdict.vt_name = name; vt_resolves = true;
                     vt_kind = (if hole then "definition_hole" else "theorem");
                     vt_type = Some (pp_type env cb.Declarations.const_type) }
                 | None -> unresolved name)
               | _ -> unresolved name)
            declared
        in
        mk ~error:d ~targets ~manifest ())
  with
  | Sys.Break -> mk ~error:"interrupted" ()
  | e ->
    let e, info = Exninfo.capture e in
    mk ~error:(Pp.string_of_ppcmds (CErrors.iprint (e, info))) ()

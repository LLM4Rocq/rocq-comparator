(* The inner pipeline (DESIGN.md section 3, steps 1-5).

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
    (top:DirPath.t -> scratch:string -> loadpath_args:string list -> deadline:float ->
     (unit, string) result)
    option;
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
  let with_version (v : Verdict.t) = { v with Verdict.rocq_version = Driver.rocq_version () } in
  let deadline = Unix.gettimeofday () +. cfg.Config.timeout_s in
  (* A signature-style challenge ("Parameter P : Prop.", "Axiom ax : ...",
     "Lemma helper : X. Admitted.") is part of the specification: the target's
     statement and proof are meant to rest on those declarations, so they are
     permitted assumptions and are pinned in the solution (same statement, and
     either still assumed or honestly proved). The challenge is trusted input,
     which is what makes this safe; a challenge that wants the strict
     behaviour turns it off. The challenge is trusted input, which is what
     makes this safe. *)
  let permit_challenge_axioms = cfg.Config.permit_challenge_axioms in
  Hashtbl.replace checks "filter" h.filter_status;
  try
    (* 1. init *)
    time "init" (fun () -> Driver.init ~args:(Config.rocq_args cfg));
    let top = dirpath_of_string (Config.top_name cfg) in
    let lenient vc =
      h.filter ~strict:false ~permitted_plugins:cfg.Config.permitted_plugins
        ~permitted_libraries:[] vc
    in
    let strict vc =
      h.filter ~strict:true ~permitted_plugins:cfg.Config.permitted_plugins
        ~permitted_libraries:cfg.Config.permitted_libraries vc
    in
    (* 2. challenge *)
    let challenge =
      time "challenge" (fun () ->
          Driver.compile_library ~filter:lenient ~top ~file:(Config.challenge_path cfg) ())
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
      (* 3. SPEC *)
      match
        Spec.extract ~top ~theorem_names:cfg.Config.theorem_names
          ~definition_names:cfg.Config.definition_names
          ~permitted_axioms:cfg.Config.permitted_axioms ~permit_challenge_axioms
      with
      | Result.Error (r, d) -> with_version (finish r d)
      | Result.Ok spec -> (
        (* 4. solution *)
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
              in
              match h.assumptions ~permitted proved reports with
              | Result.Error (r, d, reports) ->
                Hashtbl.replace checks "axioms" (Verdict.Fail d);
                with_version (finish ~targets:reports r d)
              | Result.Ok reports -> (
                Hashtbl.replace checks "axioms" Verdict.Ok;
                (* 7. hygiene + libraries.  The shadowing check (a project
                   directory bound to an installed namespace) is a library
                   violation and is run first, before the per-constant
                   hygiene scan, because it invalidates the meaning of every
                   loaded name. *)
                match
                  match Shadowing.check ~top with
                  | Result.Error e -> Result.Error e
                  | Result.Ok () ->
                    h.envcheck ~top ~trusted_roots:(h.trusted_roots cfg)
                      ~permitted_libraries:cfg.Config.permitted_libraries
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
                    let r =
                      time "rocqchk" (fun () ->
                          f ~top ~scratch ~loadpath_args:(Config.loadpath_args cfg) ~deadline)
                    in
                    match r with
                    | Result.Ok () ->
                      Hashtbl.replace checks "rocqchk" Verdict.Ok;
                      with_version
                        (Verdict.pass ~checks:(build_checks checks) ~targets:reports
                           ~timing:(List.rev !timing) ())
                    | Result.Error d ->
                      Hashtbl.replace checks "rocqchk" (Verdict.Fail d);
                      with_version (finish ~targets:reports Verdict.Rocqchk_failed d))))))))
  with
  | Sys.Break -> with_version (finish Verdict.Internal_error "interrupted")
  | e ->
    let e, info = Exninfo.capture e in
    with_version
      (finish Verdict.Internal_error (Pp.string_of_ppcmds (CErrors.iprint (e, info))))

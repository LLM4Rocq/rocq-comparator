(* rocq-comparator CLI (DESIGN.md section 10).

   The process runs twice: an OUTER process resolves the configuration, picks
   a sandbox and re-execs itself inside it; the INNER process does the actual
   Rocq work and prints one JSON verdict on stdout.  The outer process owns
   the wall-clock timeout and is the only one that decides the exit code. *)

open Cmdliner
module C = Rocq_comparator

let version = "0.1.0"

let ( let* ) = Result.bind

(* ------------------------------------------------------------------ *)
(* -Q dir Logical / -R dir Logical / -I dir are multi-token options, which
   cmdliner does not model; pull them out of argv before cmdliner sees it. *)

let extract_loadpath (argv : string list) : C.Config.loadpath_entry list * string list =
  let rec go acc rest = function
    | [] -> (List.rev acc, List.rev rest)
    | "-Q" :: d :: l :: tl -> go (C.Config.Q (d, l) :: acc) rest tl
    | "-R" :: d :: l :: tl -> go (C.Config.R (d, l) :: acc) rest tl
    | "-I" :: d :: tl -> go (C.Config.I d :: acc) rest tl
    | x :: tl -> go acc (x :: rest) tl
  in
  go [] [] argv

(* ------------------------------------------------------------------ *)
(* configuration assembly: config file first, flags override *)

type flags = {
  f_config : string option;
  f_challenge : string option;
  f_solution : string option;
  f_theorems : string list;
  f_definitions : string list;
  f_axioms : string list;
  f_loadpath : C.Config.loadpath_entry list;
  f_coqproject : string option;
  f_top : string option;
  f_timeout : float option;
  f_sandbox : string option;
  f_no_rocqchk : bool;
}

let absolute p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p

let build_config (f : flags) : (C.Config.t, string) result =
  let* base =
    match f.f_config with
    | Some path -> C.Config.of_json_file path
    | None -> Result.Ok { C.Config.default with C.Config.config_dir = Sys.getcwd () }
  in
  (* flags are relative to the cwd, config entries to the config's directory *)
  let cwd = Sys.getcwd () in
  let c = base in
  let c =
    match f.f_challenge with
    | Some p ->
      { c with C.Config.challenge = (if Filename.is_relative p then Filename.concat cwd p else p) }
    | None -> c
  in
  let c =
    match f.f_solution with
    | Some p -> { c with C.Config.solution = (if Filename.is_relative p then Filename.concat cwd p else p) }
    | None -> c
  in
  let c = if f.f_theorems = [] then c else { c with C.Config.theorem_names = f.f_theorems } in
  let c =
    if f.f_definitions = [] then c else { c with C.Config.definition_names = f.f_definitions }
  in
  let c =
    if f.f_axioms = [] then c
    else { c with C.Config.permitted_axioms = c.C.Config.permitted_axioms @ f.f_axioms }
  in
  let c =
    if f.f_loadpath = [] then c
    else
      let abs = function
        | C.Config.Q (d, l) -> C.Config.Q (absolute d, l)
        | C.Config.R (d, l) -> C.Config.R (absolute d, l)
        | C.Config.I d -> C.Config.I (absolute d)
      in
      { c with C.Config.loadpath = c.C.Config.loadpath @ List.map abs f.f_loadpath }
  in
  let c = match f.f_coqproject with Some p -> { c with C.Config.coqproject = Some (absolute p) } | None -> c in
  let c = match f.f_top with Some t -> { c with C.Config.top = Some t } | None -> c in
  let c = match f.f_timeout with Some t -> { c with C.Config.timeout_s = t } | None -> c in
  let* c =
    match f.f_sandbox with
    | None -> Result.Ok c
    | Some s ->
      let* m = C.Config.sandbox_mode_of_string s in
      Result.Ok { c with C.Config.sandbox = m }
  in
  let c = if f.f_no_rocqchk then { c with C.Config.rocqchk = false } else c in
  if c.C.Config.theorem_names = [] && c.C.Config.definition_names = [] then
    Result.Error "no target: pass --theorem NAME (or theorem_names in the config file)"
  else if not (Sys.file_exists (C.Config.challenge_path c)) then
    Result.Error ("challenge file not found: " ^ C.Config.challenge_path c)
  else if not (Sys.file_exists (C.Config.solution_path c)) then
    Result.Error ("solution file not found: " ^ C.Config.solution_path c)
  else Result.Ok c

(* The config handed to the inner process: every path absolute, the
   _CoqProject already merged, the top name pinned. *)
let resolved_config (c : C.Config.t) : C.Config.t =
  { c with
    C.Config.challenge = C.Config.challenge_path c;
    solution = C.Config.solution_path c;
    loadpath = C.Config.resolve_loadpath c;
    coqproject = None;
    top = Some (C.Config.top_name c) }

(* ------------------------------------------------------------------ *)
(* scratch directories *)

let make_scratch () =
  let base = Filename.get_temp_dir_name () in
  let rec go n =
    if n > 100 then failwith "cannot create a scratch directory"
    else
      let d =
        Filename.concat base
          (Printf.sprintf "rocq-comparator-%d-%d" (Unix.getpid ()) (Random.int 1_000_000))
      in
      match Unix.mkdir d 0o700 with () -> d | exception Unix.Unix_error _ -> go (n + 1)
  in
  go 0

let rec rm_rf path =
  match Unix.lstat path with
  | { Unix.st_kind = Unix.S_DIR; _ } ->
    Array.iter (fun e -> rm_rf (Filename.concat path e)) (Sys.readdir path);
    (try Unix.rmdir path with _ -> ())
  | _ -> ( try Unix.unlink path with _ -> ())
  | exception _ -> ()

(* ------------------------------------------------------------------ *)
(* inner side *)

(* Test-only escape hatch: run the solution through the *lenient* filter, so
   the fixture suite can check that the kernel-level checks (typing flags,
   assumptions) catch on their own what the AST filter would have rejected.
   Never set this in production. *)
let filter_disabled () =
  match Sys.getenv_opt "ROCQ_COMPARATOR_UNSAFE_NO_FILTER" with
  | None | Some "" | Some "0" -> false
  | Some _ ->
    prerr_endline
      "rocq-comparator: WARNING: ROCQ_COMPARATOR_UNSAFE_NO_FILTER is set, the solution runs \
       without the strict vernacular filter";
    true

let real_hooks (cfg : C.Config.t) : C.Check.hooks =
  let no_filter = filter_disabled () in
  { C.Check.filter =
      (fun ~strict ~permitted_plugins ~permitted_libraries vc ->
         C.Filter.check
           { C.Filter.mode =
               (if strict && not no_filter then C.Filter.Strict else C.Filter.Lenient);
             permitted_plugins; permitted_libraries }
           vc);
    assumptions = C.Assumptions.check;
    envcheck = C.Envcheck.check;
    trusted_roots = C.Envcheck.trusted_roots;
    rocqchk =
      (if not cfg.C.Config.rocqchk then None
       else
         match C.Rocqchk.find_rocqchk () with
         | None -> None
         | Some exe ->
           Some
             (fun ~top ~scratch ~loadpath_args ~deadline ->
                (* The .vo was produced by a kernel running with these two
                   global typing flags; rocqchk defaults them both to off, so
                   without them it would re-check the library under different
                   rules than the ones it was built with (and reject a
                   perfectly good -impredicative-set development, or -- worse
                   -- accept one while believing it checked something else).
                   Config.loadpath_args does not carry them, so append them
                   here; Check.run_inner's hook signature only passes the load
                   path. *)
                let flags =
                  (if cfg.C.Config.impredicative_set then [ "-impredicative-set" ] else [])
                  @ (if cfg.C.Config.indices_matter then [ "-indices-matter" ] else [])
                in
                match C.Rocqchk.save_vo ~top ~dir:scratch with
                | Result.Error e -> Result.Error e
                | Result.Ok _ ->
                  C.Rocqchk.run ~rocqchk:exe ~top ~vo_dir:scratch
                    ~loadpath_args:(loadpath_args @ flags) ~deadline));
    filter_status =
      (if no_filter then C.Verdict.Fail "DISABLED by ROCQ_COMPARATOR_UNSAFE_NO_FILTER"
       else C.Verdict.Ok) }

(* The verdict is handed to the outer process through a file, not only through
   stdout.

   Why: the inner process compiles an adversarial file, and Rocq gives a
   solution several ways to emit text (tactic messages, plugin output, an
   [idtac "..."], anything a plugin writes with Printf).  If the outer process
   recovered the verdict by scanning the child's stdout, a solution that
   printed a well-formed {"ok":true,...} line would be attempting to dictate
   the verdict.  The file is written by us, once, *after* the whole pipeline
   has run, so anything the solution may have put there earlier is overwritten,
   and the outer process prefers it over stdout. *)
let verdict_file scratch = Filename.concat scratch "verdict.json"

let write_verdict_file scratch (v : C.Verdict.t) =
  try
    let path = verdict_file scratch in
    let tmp = path ^ ".tmp" in
    let oc = open_out_bin tmp in
    output_string oc (C.Verdict.to_string ~pretty:false v);
    output_char oc '\n';
    close_out oc;
    (* rename is atomic: the outer process never sees a half-written verdict *)
    Sys.rename tmp path
  with _ ->
    (* the outer process falls back to stdout and says so in the verdict *)
    ()

let read_verdict_file scratch : C.Verdict.t option =
  match open_in_bin (verdict_file scratch) with
  | exception _ -> None
  | ic ->
    let s = try really_input_string ic (in_channel_length ic) with _ -> "" in
    close_in_noerr ic;
    (match Yojson.Safe.from_string s with
     | j -> ( match C.Verdict.of_json j with Result.Ok v -> Some v | Result.Error _ -> None)
     | exception _ -> None)

let run_inner ~pretty (config_path : string) =
  match C.Config.of_json_file config_path with
  | Result.Error m ->
    let v = C.Verdict.fail C.Verdict.Config_error m in
    write_verdict_file (absolute (Filename.dirname config_path)) v;
    C.Verdict.print ~pretty v;
    C.Verdict.exit_code v
  | Result.Ok cfg ->
    (* absolute, because we are about to chdir into it: every later use of
       [scratch] (the verdict file, the saved .vo) must keep pointing at the
       same directory *)
    let scratch = absolute (Filename.dirname config_path) in
    (* tactic caches (.lia.cache, .nra.cache) are written to the cwd: keep
       them in the scratch directory, which is also the only writable place
       inside the sandbox *)
    (try Sys.chdir scratch with Sys_error _ -> ());
    let v = C.Check.run_inner (real_hooks cfg) cfg ~scratch in
    write_verdict_file scratch v;
    C.Verdict.print ~pretty v;
    C.Verdict.exit_code v

(* ------------------------------------------------------------------ *)
(* outer side *)

let tail n s =
  let s = String.trim s in
  let len = String.length s in
  if len <= n then s else "..." ^ String.sub s (len - n) n

(* Fallback only: used when <scratch>/verdict.json is missing (see
   write_verdict_file).  The child's stdout is NOT trustworthy input -- a
   solution can make the inner process emit text -- so this path is only ever
   taken when the real verdict file could not be produced, and the verdict it
   recovers is labelled as such in the detail. *)
let parse_verdict (out : string) : C.Verdict.t option =
  let lines = String.split_on_char '\n' out in
  let rec go best = function
    | [] -> best
    | l :: tl ->
      let l = String.trim l in
      if String.length l > 1 && l.[0] = '{' then
        match Yojson.Safe.from_string l with
        | j -> ( match C.Verdict.of_json j with Result.Ok v -> go (Some v) tl | Result.Error _ -> go best tl)
        | exception _ -> go best tl
      else go best tl
  in
  go None lines

let self_exe () = absolute Sys.executable_name

(* Run one solution through the sandboxed inner process. Never raises. *)
let run_outer_once ?(quiet = false) (cfg : C.Config.t) ~keep_scratch : C.Verdict.t =
  let kind, reason = C.Sandbox.detect cfg.C.Config.sandbox in
  if kind = C.Sandbox.No_sandbox && cfg.C.Config.sandbox = C.Config.Auto && not quiet then
    prerr_endline ("rocq-comparator: warning: " ^ reason);
  let scratch = make_scratch () in
  let finally v =
    if not keep_scratch then rm_rf scratch;
    { v with C.Verdict.sandboxed = kind <> C.Sandbox.No_sandbox; sandbox = C.Sandbox.name kind }
  in
  match
    let cfg = resolved_config cfg in
    let config_path = Filename.concat scratch "config.json" in
    let oc = open_out_bin config_path in
    Yojson.Safe.to_channel oc (C.Config.to_json cfg);
    output_char oc '\n';
    close_out oc;
    let argv =
      C.Sandbox.wrap kind ~scratch
        ~argv:[ self_exe (); "check"; "--inner"; config_path ]
    in
    (* the inner process gets an allow-listed environment only: see
       Sandbox.inner_env for why *)
    C.Sandbox.run ~env:(C.Sandbox.inner_env ()) ~timeout_s:(cfg.C.Config.timeout_s +. 30.) argv
  with
  | exception e ->
    finally (C.Verdict.fail C.Verdict.Sandbox_error ("cannot start the sandbox: " ^ Printexc.to_string e))
  | r -> (
    (* the verdict written by the inner process wins over anything on stdout *)
    let from_file = read_verdict_file scratch in
    let v =
      match from_file with
      | Some _ -> from_file
      | None ->
        (* degraded mode: say so, so that nobody reads an "ok" recovered from
           a stream the solution can write to as if it were authoritative *)
        Stdlib.Option.map
          (fun (v : C.Verdict.t) ->
             let note =
               "the inner process did not write " ^ verdict_file scratch
               ^ "; this verdict was recovered from its stdout"
             in
             { v with
               C.Verdict.detail =
                 Some (match v.C.Verdict.detail with Some d -> d ^ " [" ^ note ^ "]" | None -> note) })
          (parse_verdict r.C.Sandbox.stdout)
    in
    match v with
    | Some v when not r.C.Sandbox.timed_out -> finally v
    | _ ->
      if r.C.Sandbox.timed_out then
        finally
          (C.Verdict.fail C.Verdict.Timeout
             (Printf.sprintf "no verdict after %.0fs (the sandboxed process was killed)"
                (cfg.C.Config.timeout_s +. 30.)))
      else if r.C.Sandbox.signaled then
        finally
          (C.Verdict.fail C.Verdict.Internal_error
             (Printf.sprintf "the sandboxed process died on signal %d: %s"
                (r.C.Sandbox.exit_code - 128) (tail 500 r.C.Sandbox.stderr)))
      else
        finally
          (C.Verdict.fail C.Verdict.Sandbox_error
             (Printf.sprintf "the sandboxed process exited with %d without printing a verdict: %s"
                r.C.Sandbox.exit_code (tail 500 (r.C.Sandbox.stderr ^ " " ^ r.C.Sandbox.stdout)))))

(* ------------------------------------------------------------------ *)
(* subcommands *)

(* The inner side is selected by the [--inner] flag and by nothing else.  An
   environment marker would be inherited: a caller (or a parent shell) with
   ROCQ_COMPARATOR_INNER=1 in its environment would make the *outer* invocation
   run the pipeline in-process, unsandboxed, which is exactly the situation the
   sandbox exists to prevent.  The flag is passed by the outer process itself,
   so it cannot be set by accident. *)
let cmd_check (f : flags) ~inner ~pretty ~keep_scratch =
  if inner then
    match f.f_config with
    | Some path -> run_inner ~pretty path
    | None ->
      prerr_endline "rocq-comparator: --inner needs a config file";
      2
  else
    match build_config f with
    | Result.Error m ->
      let v = C.Verdict.fail C.Verdict.Config_error m in
      C.Verdict.print ~pretty v;
      C.Verdict.exit_code v
    | Result.Ok cfg ->
      let v = run_outer_once cfg ~keep_scratch in
      C.Verdict.print ~pretty v;
      C.Verdict.exit_code v

let cmd_batch (f : flags) ~solutions ~jobs ~pretty ~keep_scratch =
  match build_config { f with f_solution = (match solutions with s :: _ -> Some s | [] -> None) } with
  | Result.Error m ->
    prerr_endline ("rocq-comparator: " ^ m);
    2
  | Result.Ok base ->
    let sols = Array.of_list solutions in
    let n = Array.length sols in
    let results = Array.make n None in
    let cfg_for i =
      let p = sols.(i) in
      { base with C.Config.solution = (if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p) }
    in
    let run_one i = results.(i) <- Some (run_outer_once ~quiet:true (cfg_for i) ~keep_scratch) in
    if jobs <= 1 then
      for i = 0 to n - 1 do
        run_one i;
        match results.(i) with
        | Some v ->
          let v = { v with C.Verdict.solution = Some sols.(i) } in
          print_string (C.Verdict.to_string ~pretty v);
          print_newline ();
          flush stdout
        | None -> ()
      done
    else begin
      let next = Atomic.make 0 in
      let worker () =
        let rec loop () =
          let i = Atomic.fetch_and_add next 1 in
          if i < n then (run_one i; loop ())
        in
        loop ()
      in
      let threads = List.init (min jobs n) (fun _ -> Thread.create worker ()) in
      List.iter Thread.join threads;
      Array.iteri
        (fun i r ->
           match r with
           | Some v ->
             let v = { v with C.Verdict.solution = Some sols.(i) } in
             print_string (C.Verdict.to_string ~pretty v);
             print_newline ()
           | None -> ())
        results
    end;
    (* exit 0 as long as every solution produced a verdict *)
    let infra =
      Array.exists
        (function Some (v : C.Verdict.t) -> C.Verdict.exit_code v = 2 | None -> true)
        results
    in
    if infra then 2 else 0

let cmd_sandbox_info (mode : string option) =
  let m =
    match mode with
    | None -> C.Config.Auto
    | Some s -> ( match C.Config.sandbox_mode_of_string s with Result.Ok m -> m | Result.Error _ -> C.Config.Auto)
  in
  let kind, reason = C.Sandbox.detect m in
  Printf.printf "sandbox: %s\nreason: %s\n" (C.Sandbox.name kind) reason;
  0

(* ------------------------------------------------------------------ *)
(* cmdliner plumbing *)

let loadpath_ref : C.Config.loadpath_entry list ref = ref []

let docs_loadpath = "LOAD PATH"

let man_loadpath =
  [ `S docs_loadpath;
    `P "These are parsed before the other options, exactly as $(b,rocq c) does:";
    `I ("$(b,-Q) $(i,DIR) $(i,LOGICAL)", "map $(i,DIR) to the logical path $(i,LOGICAL)");
    `I ("$(b,-R) $(i,DIR) $(i,LOGICAL)", "same, recursively");
    `I ("$(b,-I) $(i,DIR)", "add $(i,DIR) to the ML load path") ]

let config_arg =
  Arg.(value & pos 0 (some string) None & info [] ~docv:"CONFIG.json" ~doc:"Configuration file.")

let challenge_arg =
  Arg.(value & opt (some string) None & info [ "challenge" ] ~docv:"FILE" ~doc:"The trusted challenge file.")

let solution_arg =
  Arg.(value & opt (some string) None & info [ "solution" ] ~docv:"FILE" ~doc:"The solution file to judge.")

let theorem_arg =
  Arg.(value & opt_all string [] & info [ "theorem" ] ~docv:"NAME" ~doc:"A theorem to check. Repeatable.")

let definition_arg =
  Arg.(value & opt_all string [] & info [ "definition" ] ~docv:"NAME" ~doc:"A definition hole to check. Repeatable.")

let axiom_arg =
  Arg.(
    value & opt_all string []
    & info [ "axiom" ] ~docv:"NAME"
        ~doc:
          "A permitted axiom, fully qualified (a trailing $(b,.*) is a prefix wildcard). \
           Repeatable.")

let coqproject_arg =
  Arg.(value & opt (some string) None & info [ "coqproject" ] ~docv:"FILE" ~doc:"A _CoqProject to take the load path from.")

let top_arg =
  Arg.(value & opt (some string) None & info [ "top" ] ~docv:"NAME" ~doc:"Logical name of the library (default: derived from the load path).")

let timeout_arg =
  Arg.(value & opt (some float) None & info [ "timeout" ] ~docv:"SECONDS" ~doc:"Wall-clock budget for the solution.")

let sandbox_arg =
  Arg.(
    value & opt (some string) None
    & info [ "sandbox" ] ~docv:"MODE"
        ~doc:"One of $(b,auto), $(b,none), $(b,sandbox-exec), $(b,landrun), $(b,bwrap).")

let no_rocqchk_arg = Arg.(value & flag & info [ "no-rocqchk" ] ~doc:"Skip the rocqchk replay.")
let pretty_arg = Arg.(value & flag & info [ "pretty" ] ~doc:"Pretty-print the JSON verdict.")
let json_arg = Arg.(value & flag & info [ "json" ] ~doc:"Print the verdict as one JSON line (the default).")
let inner_arg = Arg.(value & flag & info [ "inner" ] ~doc:"Internal: run the checking pipeline in this process.")
let keep_scratch_arg = Arg.(value & flag & info [ "keep-scratch" ] ~doc:"Do not delete the scratch directory.")

let flags_term =
  let mk f_config f_challenge f_solution f_theorems f_definitions f_axioms f_coqproject f_top
      f_timeout f_sandbox f_no_rocqchk =
    { f_config; f_challenge; f_solution; f_theorems; f_definitions; f_axioms;
      f_loadpath = !loadpath_ref; f_coqproject; f_top; f_timeout; f_sandbox; f_no_rocqchk }
  in
  Term.(
    const mk $ config_arg $ challenge_arg $ solution_arg $ theorem_arg $ definition_arg
    $ axiom_arg $ coqproject_arg $ top_arg $ timeout_arg $ sandbox_arg $ no_rocqchk_arg)

let check_cmd =
  let doc = "Judge one solution against one challenge." in
  let man =
    [ `S Manpage.s_description;
      `P "Compiles the challenge and then the solution in one Rocq process, inside an OS \
          sandbox, and prints one JSON verdict on stdout.";
      `P "Exit code: 0 accepted, 1 rejected, 2 infrastructure error.";
      `Blocks man_loadpath ]
  in
  let run f inner pretty _json keep_scratch = cmd_check f ~inner ~pretty ~keep_scratch in
  Cmd.v (Cmd.info "check" ~doc ~man)
    Term.(const run $ flags_term $ inner_arg $ pretty_arg $ json_arg $ keep_scratch_arg)

let batch_cmd =
  let doc = "Judge several solutions against one challenge (JSON lines)." in
  let man =
    [ `S Manpage.s_description;
      `P "Runs the $(b,check) pipeline once per solution and prints one JSON verdict per line, \
          each with a $(b,solution) field.";
      `P "The challenge is recompiled for every solution: each solution gets its own sandboxed \
          process. Sharing one compiled challenge across solutions (by forking after the \
          challenge is compiled) is future work.";
      `P "Exit code: 0 if every solution produced a verdict (whatever the verdict), 2 on an \
          infrastructure error.";
      `Blocks man_loadpath ]
  in
  let solutions =
    Arg.(value & pos_right 0 string [] & info [] ~docv:"SOLUTION.v" ~doc:"The solutions to judge.")
  in
  let jobs = Arg.(value & opt int 1 & info [ "j"; "jobs" ] ~docv:"N" ~doc:"Concurrent solutions.") in
  let run f solutions jobs pretty keep_scratch = cmd_batch f ~solutions ~jobs ~pretty ~keep_scratch in
  Cmd.v (Cmd.info "batch" ~doc ~man)
    Term.(const run $ flags_term $ solutions $ jobs $ pretty_arg $ keep_scratch_arg)

let sandbox_info_cmd =
  let doc = "Print which sandbox would be used, and why." in
  Cmd.v (Cmd.info "sandbox-info" ~doc) Term.(const cmd_sandbox_info $ sandbox_arg)

let version_cmd =
  let doc = "Print the version of rocq-comparator and of the linked Rocq." in
  let run () =
    Printf.printf "rocq-comparator %s (rocq-runtime %s)\n" version (C.Driver.rocq_version ());
    0
  in
  Cmd.v (Cmd.info "version" ~doc) Term.(const run $ const ())

let main_cmd =
  let doc = "a trustworthy judge for Rocq proofs" in
  let man =
    [ `S Manpage.s_description;
      `P "Checks that a solution file proves the same statements as a trusted challenge file, \
          using no more axioms than permitted, with the proof accepted by the Rocq kernel.";
      `Blocks man_loadpath ]
  in
  Cmd.group
    (Cmd.info "rocq-comparator" ~version ~doc ~man)
    [ check_cmd; batch_cmd; sandbox_info_cmd; version_cmd ]

let () =
  Random.self_init ();
  let argv = Array.to_list Sys.argv in
  let lp, rest = extract_loadpath argv in
  loadpath_ref := lp;
  exit (Cmd.eval' ~argv:(Array.of_list rest) main_cmd)

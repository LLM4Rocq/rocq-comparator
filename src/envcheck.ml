(* Environment hygiene after the solution has compiled (DESIGN.md section 8). *)

open Names

(* The roots a loaded .vo is allowed to come from.

   [Envars.coqpath ()] reads COQPATH, which the inner process does not
   inherit any more (bin/main.ml builds the child environment from an
   allow-list, precisely so that COQPATH/ROCQPATH/ROCQLIB/... cannot redirect
   the load path).  It is kept here only because it costs nothing: inside the
   sandboxed inner process it is always empty, so the trusted roots are the
   compiled-in coqlib/corelib/user-contrib plus the -Q/-R directories the
   caller configured.  That is the intended set. *)
let trusted_roots (c : Config.t) : string list =
  let boot =
    match Boot.Env.initialized () with
    | Some (Boot.Env.Env e) ->
      [ Boot.Env.Path.to_string (Boot.Env.coqlib e);
        Boot.Env.Path.to_string (Boot.Env.corelib e);
        Boot.Env.Path.to_string (Boot.Env.user_contrib e) ]
    | Some Boot.Env.Boot | None -> []
  in
  let from_path = try Envars.coqpath () with _ -> [] in
  let configured =
    List.filter_map
      (function Config.Q (d, _) -> Some d | Config.R (d, _) -> Some d | Config.I _ -> None)
      (Config.resolve_loadpath c)
  in
  List.sort_uniq String.compare (boot @ from_path @ configured)

let safety_ok (f : Declarations.typing_flags) ~impredicative_set ~indices_matter =
  f.Declarations.check_guarded && f.Declarations.check_positive
  && f.Declarations.check_universes
  && (not f.Declarations.allow_uip)
  && f.Declarations.impredicative_set = impredicative_set
  && f.Declarations.indices_matter = indices_matter

let check ~(top : DirPath.t) ~(trusted_roots : string list)
    ~(permitted_libraries : string list) ~(impredicative_set : bool)
    ~(indices_matter : bool) : (unit, Verdict.reason * string) result =
  let env = Global.env () in
  let err = ref None in
  let set r d = match !err with Some _ -> () | None -> err := Some (r, d) in
  if Global.rewrite_rules_allowed () then
    set Verdict.Unsafe_flags "rewrite rules are enabled in the solution environment";
  (* Section / module hygiene.

     A solution that never closes a [Section] leaves its theorems *inside* the
     section: they still carry the section hypotheses in [const_hyps], and the
     statement the kernel stores is the un-discharged one, which can be much
     weaker than the challenge's (proving [foo] under a local [Variable H :
     False] is trivial).  The same goes for a [Module] or [Module Type] left
     open at end of file: the objects are not yet interpreted into the library
     and the environment we inspect is not the environment the library would
     have.  Both are pathological in a file that is supposed to be a finished
     development, so reject them outright rather than try to reason about a
     half-built library. *)
  if Lib.sections_are_opened () then
    set Verdict.Unsafe_flags
      "the solution ends with a section still open: its theorems are not discharged, so their \
       statements still depend on the section's hypotheses";
  (match Lib.current_mp () with
   | ModPath.MPfile dp when DirPath.equal dp top -> ()
   | mp ->
     set Verdict.Unsafe_flags
       ("the solution ends inside " ^ ModPath.to_string mp
        ^ ": a module or module type is still open at end of file"));
  Environ.fold_constants
    (fun c cb () ->
       if Spec.is_local ~top (Constant.modpath c) then begin
         (match cb.Declarations.const_body with
          | Declarations.Symbol _ ->
            set Verdict.Unsafe_flags (Constant.to_string c ^ " is a rewrite-rule symbol")
          | Declarations.Undef _ | Declarations.Def _ | Declarations.OpaqueDef _
          | Declarations.Primitive _ -> ());
         (* A non-empty [const_hyps] means the constant was declared inside a
            section that was never closed: what the kernel holds is the
            un-discharged constant, whose statement is only valid under those
            hypotheses.  Comparing it to the challenge's closed statement
            would compare two different things. *)
         (match cb.Declarations.const_hyps with
          | [] -> ()
          | hyps ->
            set Verdict.Unsafe_flags
              (Constant.to_string c ^ " still depends on the section hypotheses "
               ^ String.concat ", "
                   (List.map
                      (fun d -> Id.to_string (Context.Named.Declaration.get_id d))
                      hyps)));
         if not (safety_ok cb.Declarations.const_typing_flags ~impredicative_set ~indices_matter)
         then
           set Verdict.Unsafe_flags
             (Constant.to_string c ^ " was declared with a kernel check disabled")
       end)
    env ();
  Environ.fold_inductives
    (fun m mb () ->
       if Spec.is_local ~top (MutInd.modpath m) then begin
         (* same rationale as [const_hyps] above *)
         (match mb.Declarations.mind_hyps with
          | [] -> ()
          | _ ->
            set Verdict.Unsafe_flags
              (MutInd.to_string m ^ " was declared inside a section that is still open"));
         if not (safety_ok mb.Declarations.mind_typing_flags ~impredicative_set ~indices_matter)
         then
           set Verdict.Unsafe_flags
             (MutInd.to_string m ^ " was declared with a kernel check disabled")
       end)
    env ();
  if not (Safe_typing.is_joined_environment (Global.safe_env ())) then
    set Verdict.Unsafe_flags "the environment is not joined (a delayed opaque proof remains)";
  if (Environ.typing_flags env).Declarations.enable_native_compiler then
    set Verdict.Unsafe_flags "the native compiler is enabled";
  (* every loaded library must come from a trusted root *)
  List.iter
    (fun dp ->
       if not (DirPath.equal dp top) then begin
         let name = DirPath.to_string dp in
         (match permitted_libraries with
          | [] -> ()
          | l ->
            if not (List.exists (fun p ->
                String.equal name p
                || (String.length name > String.length p
                    && String.sub name 0 (String.length p + 1) = p ^ ".")) l)
            then set Verdict.Library_violation ("the solution required " ^ name
                                                ^ ", which is not in permitted_libraries"));
         match Loadpath.locate_absolute_library dp with
         | Result.Ok path ->
           if not (List.exists (fun root -> Config.is_under ~root path) trusted_roots) then
             set Verdict.Library_violation
               ("the library " ^ name ^ " was loaded from " ^ path
                ^ ", which is outside the trusted load path")
         | Result.Error _ ->
           set Verdict.Library_violation ("cannot locate the loaded library " ^ name)
         | exception _ ->
           set Verdict.Library_violation ("cannot locate the loaded library " ^ name)
       end)
    (Library.loaded_libraries ());
  match !err with None -> Result.Ok () | Some e -> Result.Error e

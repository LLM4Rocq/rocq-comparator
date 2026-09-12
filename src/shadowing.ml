(* Library-shadowing detection.

   Rocq resolves [From Stdlib Require Import Arith] by logical name, and a
   configured [-Q dir ""] can provide a *fake* [Stdlib.Arith] (a [nat] with
   a single constructor, say) that shadows the installed one for both the
   challenge and the solution.  Every other check then passes consistently
   -- rocqchk included -- so the only defence is to refuse it outright: a
   library whose logical root is a namespace installed in the switch
   ([Corelib], [Stdlib], [Ltac2], [mathcomp], ...) must have been loaded from
   the switch's own directories, never from a project directory.

   Trusting the load path is an assumption of the comparator (like the
   lakefile in Lean's), but operators do point it at submitted projects;
   this check turns that mistake into a [library_violation] instead of a
   false pass. *)

open Names

(* The switch's own library roots: coqlib/theories (Corelib), user-contrib
   (Stdlib and every installed package). *)
let system_roots () : string list =
  match Boot.Env.initialized () with
  | Some (Boot.Env.Env e) ->
    let p f = Boot.Env.Path.to_string (f e) in
    let coqlib = p Boot.Env.coqlib in
    List.sort_uniq String.compare
      [ Filename.concat coqlib "theories"; p Boot.Env.corelib; p Boot.Env.user_contrib ]
  | Some Boot.Env.Boot | None -> []

(* Top-level namespaces provided by the system roots (directory names and
   bare .vo files directly under them), plus the kernel's own prelude
   namespaces which must be reserved even if a root is missing. *)
let installed_namespaces () : string list =
  let of_root root =
    match Sys.readdir root with
    | entries ->
      Array.to_list entries
      |> List.filter_map (fun e ->
          if String.length e > 0 && e.[0] = '.' then None
          else if Filename.check_suffix e ".vo" then Some (Filename.chop_suffix e ".vo")
          else if Sys.is_directory (Filename.concat root e) then Some e
          else None)
    | exception Sys_error _ -> []
  in
  List.sort_uniq String.compare
    ([ "Corelib"; "Stdlib"; "Ltac2" ] @ List.concat_map of_root (system_roots ()))

let root_component (dp : DirPath.t) : string =
  match List.rev (DirPath.repr dp) with
  | [] -> ""
  | first :: _ -> Id.to_string first

let check ~(top : DirPath.t) : (unit, Verdict.reason * string) result =
  let roots = system_roots () in
  let reserved = installed_namespaces () in
  let err = ref None in
  List.iter
    (fun dp ->
       if (not (DirPath.equal dp top)) && !err = None then begin
         let ns = root_component dp in
         if List.mem ns reserved then
           match Loadpath.locate_absolute_library dp with
           | Result.Ok path ->
             if not (List.exists (fun r -> Config.is_under ~root:r path) roots) then
               err :=
                 Some
                   ( Verdict.Library_violation,
                     Printf.sprintf
                       "%s was loaded from %s, shadowing the installed namespace %s \
                        (installed libraries must come from the switch, not from a \
                        project directory)"
                       (DirPath.to_string dp) path ns )
           | Result.Error _ | (exception _) ->
             err :=
               Some
                 ( Verdict.Library_violation,
                   "cannot locate the loaded library " ^ DirPath.to_string dp )
       end)
    (Library.loaded_libraries ());
  match !err with None -> Result.Ok () | Some e -> Result.Error e

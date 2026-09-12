(* Library-shadowing detection — generic, with no maintained lists.

   A configured project load path (-Q/-R) can bind a project directory to the
   logical namespace of an installed library, so that a fake [Stdlib/Arith.v]
   is loaded under the name [Stdlib.Arith] instead of the switch's real one
   (the talks/2026_caia/collatz cheat).  The fake is loaded once into the
   shared process and seen identically by the challenge and the solution, so
   every content-level check (statement, closure, axioms, even rocqchk) passes
   consistently.  The only ground truth is the switch's own installation.

   The rule is list-free.  It never enumerates "trusted" namespaces: the set
   of protected namespaces is exactly the (non-empty) logical paths that the
   switch's OWN load-path entries claim, read from Rocq at run time.  A
   library install adds new namespaces to the switch, and this check protects
   them automatically the next time it runs — nothing to update by hand.

   The rule: no project load-path entry (a physical directory outside the
   switch's installation roots) may be bound to a logical namespace that
   overlaps one the switch itself owns.  Adding genuinely new namespaces is
   fine; intruding into an installed one is not.

   This is a defence in depth over the load-path trust assumption (§1): the
   load path is nominally the operator's responsibility, but operators do
   point it at submitted projects, and this turns that mistake into a
   [library_violation] instead of a silent false pass. *)

open Names

let switch_roots () : string list =
  match Boot.Env.initialized () with
  | Some (Boot.Env.Env e) ->
    let p f = Boot.Env.Path.to_string (f e) in
    let coqlib = p Boot.Env.coqlib in
    List.sort_uniq String.compare
      [ coqlib; Filename.concat coqlib "theories";
        p Boot.Env.corelib; p Boot.Env.user_contrib ]
  | Some Boot.Env.Boot | None -> []

(* logical path as an outer-to-inner list of identifiers *)
let fwd (dp : DirPath.t) : Id.t list = List.rev (DirPath.repr dp)

(* [a] and [b] overlap when one is a prefix of the other (equal paths too):
   then the two directories claim intersecting logical namespaces. *)
let overlaps (a : DirPath.t) (b : DirPath.t) =
  let rec prefix x y =
    match (x, y) with
    | [], _ | _, [] -> true
    | u :: x', v :: y' -> Id.equal u v && prefix x' y'
  in
  prefix (fwd a) (fwd b)

let check ~(top : DirPath.t) : (unit, Verdict.reason * string) result =
  let roots = switch_roots () in
  let lps = Loadpath.get_load_paths () in
  let is_switch e =
    List.exists (fun r -> Config.is_under ~root:r (Loadpath.physical e)) roots
  in
  (* protected namespaces: every non-empty logical path a switch entry owns *)
  let switch_logical =
    List.filter_map
      (fun e ->
         if is_switch e then
           let l = Loadpath.logical e in
           if DirPath.is_empty l then None else Some l
         else None)
      lps
  in
  let violation =
    List.find_map
      (fun e ->
         if is_switch e then None
         else
           let l = Loadpath.logical e in
           (* the empty root and the challenge's own namespace are not
              intrusions; an empty-root project dir that actually contains an
              installed namespace is expanded by Rocq into a child entry whose
              logical path is that namespace, and that child is caught here *)
           if DirPath.is_empty l || DirPath.equal l top then None
           else
             match List.find_opt (fun s -> overlaps l s) switch_logical with
             | Some s -> Some (e, l, s)
             | None -> None)
      lps
  in
  match violation with
  | None -> Result.Ok ()
  | Some (e, l, s) ->
    Result.Error
      ( Verdict.Library_violation,
        Printf.sprintf
          "the project directory %s is on the load path under the logical name \
           %s, which shadows the installed namespace %s; an installed library \
           must be provided by the switch, not by a submitted directory"
          (Loadpath.physical e) (DirPath.to_string l) (DirPath.to_string s) )

(* SPEC extraction from the challenge environment (DESIGN.md section 5).

   The result is a plain immutable OCaml value, so it survives
   [Vernacstate.unfreeze_full_state root] and cannot be tampered with while
   the solution is compiled. *)

open Names

type target = {
  name : string;
  kn : Constant.t;
  hole : bool;  (** a definition hole rather than a theorem *)
  typ : Constr.t;
  univs : Declarations.universes;
}

type const_entry = {
  c : Constant.t;
  cb : Declarations.constant_body;
  body : Constr.t option;  (** forced body for Def / OpaqueDef *)
}

type ind_entry = { m : MutInd.t; mb : Declarations.mutual_inductive_body }

type t = {
  top : DirPath.t;
  targets : target list;
  local_consts : const_entry list;
  local_inds : ind_entry list;
  external_consts : const_entry list;
  external_inds : ind_entry list;
  graph : UGraph.t;
  permitted_present : (Constant.t * Constr.t) list;
  challenge_axioms : (Constant.t * Constr.t) list;
      (** Constants the *challenge* declares without a body (Parameter, Axiom,
          a helper lemma left Admitted) and which are not themselves targets.
          A signature-style challenge is built out of these, so its own
          declarations must be usable by the solution; they are pinned (same
          type, still an assumption or an honest proof of it) and permitted as
          assumptions. Empty when [~permit_challenge_axioms:false]. *)
}

let is_local ~(top : DirPath.t) (mp : ModPath.t) =
  match mp with
  | ModPath.MPbound _ -> false
  | _ -> DirPath.equal (ModPath.dp mp) top

let accessor = (Library.indirect_accessor [@alert "-deprecated"])

let force_body (cb : Declarations.constant_body) : Constr.t option =
  match cb.Declarations.const_body with
  | Declarations.Undef _ | Declarations.Primitive _ | Declarations.Symbol _ -> None
  | Declarations.Def c -> Some c
  | Declarations.OpaqueDef _ -> (
    match Global.body_of_constant_body accessor cb with
    | Some (c, _, _) -> Some c
    | None -> None
    | exception _ -> None)

exception Section_variable of Id.t

(* Worklist traversal collecting every constant / inductive a term mentions. *)
let closure_of ~(top : DirPath.t) (roots : Constr.t list) =
  let consts : (Constant.t, unit) Hashtbl.t = Hashtbl.create 97 in
  let inds : (MutInd.t, unit) Hashtbl.t = Hashtbl.create 97 in
  let pending_c = ref [] and pending_i = ref [] in
  let add_const c =
    let k = Constant.canonical c in
    if not (Hashtbl.mem consts c) then begin
      ignore k;
      Hashtbl.add consts c ();
      pending_c := c :: !pending_c
    end
  in
  let add_mind m =
    if not (Hashtbl.mem inds m) then begin
      Hashtbl.add inds m ();
      pending_i := m :: !pending_i
    end
  in
  let rec scan t =
    (match Constr.kind t with
     | Constr.Var id -> raise (Section_variable id)
     | Constr.Const (c, _) -> add_const c
     | Constr.Ind ((m, _), _) -> add_mind m
     | Constr.Construct (((m, _), _), _) -> add_mind m
     | Constr.Proj (p, _, _) ->
       add_mind (Projection.mind p);
       add_const (Projection.constant p)
     | Constr.Case (ci, _, _, _, _, _, _) -> add_mind (fst ci.Constr.ci_ind)
     | Constr.Rel _ | Constr.Meta _ | Constr.Evar _ | Constr.Sort _ | Constr.Cast _
     | Constr.Prod _ | Constr.Lambda _ | Constr.LetIn _ | Constr.App _
     | Constr.Fix _ | Constr.CoFix _ | Constr.Int _ | Constr.Float _
     | Constr.String _ | Constr.Array _ -> ());
    Constr.iter scan t
  in
  List.iter scan roots;
  let local_c = ref [] and local_i = ref [] and ext_c = ref [] and ext_i = ref [] in
  let rec drain () =
    match !pending_c, !pending_i with
    | c :: tl, _ ->
      pending_c := tl;
      (match Environ.lookup_constant_opt c (Global.env ()) with
       | None -> ()
       | Some cb ->
         let body = force_body cb in
         let e = { c; cb; body } in
         if is_local ~top (Constant.modpath c) then local_c := e :: !local_c
         else ext_c := e :: !ext_c;
         scan cb.Declarations.const_type;
         (match body with Some b -> scan b | None -> ()));
      drain ()
    | [], m :: tl ->
      pending_i := tl;
      (match Environ.lookup_mind m (Global.env ()) with
       | exception Not_found -> ()
       | mb ->
         let e = { m; mb } in
         if is_local ~top (MutInd.modpath m) then local_i := e :: !local_i
         else ext_i := e :: !ext_i;
         Array.iter
           (fun (p : Declarations.one_inductive_body) ->
              scan p.Declarations.mind_user_arity;
              Array.iter scan p.Declarations.mind_user_lc)
           mb.Declarations.mind_packets;
         List.iter
           (fun d -> List.iter scan (Context.Rel.Declaration.to_tuple d |> fun (_, b, t) ->
                                     match b with Some b -> [ b; t ] | None -> [ t ]))
           mb.Declarations.mind_params_ctxt);
      drain ()
    | [], [] -> ()
  in
  drain ();
  (List.rev !local_c, List.rev !local_i, List.rev !ext_c, List.rev !ext_i)

(* [Nametab.locate] resolves *true* global references only.
   [Smartlocate.global_with_alias] additionally follows abbreviations
   ("Notation foo := bar"), so a solution could satisfy the target name [foo]
   without ever declaring a constant called [foo] -- the comparison would then
   be about [bar]. A target must name a kernel constant, so we resolve it the
   strict way. *)
let locate_global (s : string) : GlobRef.t option =
  match Nametab.locate (Libnames.qualid_of_string s) with
  | gr -> Some gr
  | exception _ -> None

let resolve_name ~(top : DirPath.t) (name : string) : (Constant.t, string) result =
  let try_one s =
    match locate_global s with
    | Some (GlobRef.ConstRef c) -> Some (Result.Ok c)
    | Some (GlobRef.IndRef _ | GlobRef.ConstructRef _ | GlobRef.VarRef _) ->
      Some (Result.Error (s ^ " is not a constant"))
    | None -> None
  in
  let qualified = DirPath.to_string top ^ "." ^ name in
  match try_one name with
  | Some r -> r
  | None -> (
    match try_one qualified with
    | Some r -> r
    | None -> Result.Error ("target " ^ name ^ " not found in the challenge"))

(* Every local constant of the challenge that has no body and is not a target:
   the axioms and admitted helpers the challenge itself is built out of. *)
let collect_challenge_axioms ~(top : DirPath.t) (env : Environ.env)
    (targets : target list) : (Constant.t * Constr.t) list =
  let is_target c = List.exists (fun t -> Constant.CanOrd.equal t.kn c) targets in
  Environ.fold_constants
    (fun c (cb : Declarations.constant_body) acc ->
       match cb.Declarations.const_body with
       | Declarations.Undef _
         when is_local ~top (Constant.modpath c) && not (is_target c) ->
         (c, cb.Declarations.const_type) :: acc
       | Declarations.Undef _ | Declarations.Def _ | Declarations.OpaqueDef _
       | Declarations.Primitive _ | Declarations.Symbol _ -> acc)
    env []

let extract ~(top : DirPath.t) ~(theorem_names : string list)
    ~(definition_names : string list) ~(permitted_axioms : string list)
    ~(permit_challenge_axioms : bool) : (t, Verdict.reason * string) result =
  let env = Global.env () in
  let rec resolve acc = function
    | [] -> Result.Ok (List.rev acc)
    | (name, hole) :: tl -> (
      match resolve_name ~top name with
      | Result.Error m -> Result.Error (Verdict.Target_not_found, m)
      | Result.Ok kn ->
        if not (is_local ~top (Constant.modpath kn)) then
          Result.Error
            (Verdict.Target_not_found,
             name ^ " does not live in the challenge library " ^ DirPath.to_string top)
        else (
          match Environ.lookup_constant_opt kn env with
          | None -> Result.Error (Verdict.Target_not_found, name ^ " has no kernel declaration")
          | Some cb ->
            resolve
              ({ name; kn; hole; typ = cb.Declarations.const_type;
                 univs = cb.Declarations.const_universes }
               :: acc)
              tl))
  in
  match
    resolve []
      (List.map (fun n -> (n, false)) theorem_names
       @ List.map (fun n -> (n, true)) definition_names)
  with
  | Result.Error e -> Result.Error e
  | Result.Ok targets -> (
    (* the permitted axioms that actually exist in the challenge *)
    let permitted_present =
      List.filter_map
        (fun a ->
           if String.length a > 2 && String.sub a (String.length a - 2) 2 = ".*" then None
           else
             (* strict resolution again: an abbreviation must not be able to
                turn a permitted-axiom name into some other constant *)
             match locate_global a with
             | Some (GlobRef.ConstRef c) -> (
               match Environ.lookup_constant_opt c env with
               | Some cb -> Some (c, cb.Declarations.const_type)
               | None -> None)
             | Some _ | None -> None)
        permitted_axioms
    in
    let challenge_axioms =
      if permit_challenge_axioms then collect_challenge_axioms ~top env targets else []
    in
    (* The challenge's own axioms are part of the specification, so their
       statements go into the closure too: the solution may not restate them. *)
    let roots =
      List.map (fun t -> t.typ) targets
      @ List.map snd permitted_present
      @ List.map snd challenge_axioms
    in
    match closure_of ~top roots with
    | exception Section_variable id ->
      Result.Error
        (Verdict.Statement_mismatch,
         "the challenge statement depends on the section variable " ^ Id.to_string id)
    | local_consts, local_inds, external_consts, external_inds ->
      Result.Ok
        { top; targets; local_consts; local_inds; external_consts; external_inds;
          graph = Global.universes (); permitted_present; challenge_axioms })

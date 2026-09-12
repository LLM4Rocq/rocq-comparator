(* Statement and dependency-closure comparison (DESIGN.md section 5).

   Terms are compared structurally, modulo a bijective renaming of the
   universe levels that are local to the library under comparison (a solution
   that declares an extra Type-using definition shifts every later anonymous
   level name). *)

open Names

type ren = (Univ.Level.t * Univ.Level.t) list ref

(* --- universe levels modulo a bijection --- *)

let local_level ~(top : DirPath.t) (l : Univ.Level.t) =
  match Univ.Level.name l with
  | None -> false
  | Some g ->
    let dp, _, _ = Univ.UGlobal.repr g in
    DirPath.equal dp top

let level_eq ~top (ren : ren) (a : Univ.Level.t) (b : Univ.Level.t) =
  if Univ.Level.is_set a || Univ.Level.is_set b then Univ.Level.equal a b
  else
    match (Univ.Level.var_index a, Univ.Level.var_index b) with
    | Some i, Some j -> Int.equal i j
    | Some _, None | None, Some _ -> false
    | None, None ->
      let la = local_level ~top a and lb = local_level ~top b in
      if la && lb then (
        match List.find_opt (fun (x, _) -> Univ.Level.equal x a) !ren with
        | Some (_, y) -> Univ.Level.equal y b
        | None ->
          if List.exists (fun (_, y) -> Univ.Level.equal y b) !ren then false
          else (ren := (a, b) :: !ren; true))
      else if (not la) && not lb then Univ.Level.equal a b
      else false

let universe_eq ~top ren (u : Univ.Universe.t) (v : Univ.Universe.t) =
  let lu = Univ.Universe.repr u and lv = Univ.Universe.repr v in
  List.length lu = List.length lv
  && List.for_all2 (fun (l1, n1) (l2, n2) -> Int.equal n1 n2 && level_eq ~top ren l1 l2) lu lv

let sort_eq ~top ren (s1 : Sorts.t) (s2 : Sorts.t) =
  match (s1, s2) with
  | Sorts.SProp, Sorts.SProp | Sorts.Prop, Sorts.Prop | Sorts.Set, Sorts.Set -> true
  | Sorts.Type u, Sorts.Type v -> universe_eq ~top ren u v
  | Sorts.QSort (q1, u), Sorts.QSort (q2, v) ->
    Sorts.QVar.equal q1 q2 && universe_eq ~top ren u v
  | (Sorts.SProp | Sorts.Prop | Sorts.Set | Sorts.Type _ | Sorts.QSort _), _ -> false

let instance_eq ~top ren _ (i1 : UVars.Instance.t) (i2 : UVars.Instance.t) =
  let q1, l1 = UVars.Instance.to_array i1 and q2, l2 = UVars.Instance.to_array i2 in
  Array.length q1 = Array.length q2
  && Array.length l1 = Array.length l2
  && (let ok = ref true in
      Array.iteri (fun i q -> if not (Sorts.Quality.equal q q2.(i)) then ok := false) q1;
      Array.iteri (fun i l -> if not (level_eq ~top ren l l2.(i)) then ok := false) l1;
      !ok)

let rec cmp ~top ~ren nargs c1 c2 =
  Constr.compare_head_gen (instance_eq ~top ren) (sort_eq ~top ren)
    (fun _ _ -> false)
    (cmp ~top ~ren) nargs c1 c2

let eq_constr_mod_univ ~top ~ren c1 c2 = cmp ~top ~ren 0 c1 c2

(* --- universe declarations --- *)

let eq_abstract_context a1 a2 =
  let (qs1, us1) = UVars.AbstractContext.size a1 and (qs2, us2) = UVars.AbstractContext.size a2 in
  Int.equal qs1 qs2 && Int.equal us1 us2
  &&
  let c1 = UVars.AbstractContext.repr a1 and c2 = UVars.AbstractContext.repr a2 in
  Univ.UnivConstraints.equal (UVars.UContext.univ_constraints c1) (UVars.UContext.univ_constraints c2)
  && Sorts.ElimConstraints.equal
       (UVars.UContext.elim_constraints c1) (UVars.UContext.elim_constraints c2)

let eq_univs (u1 : Declarations.universes) (u2 : Declarations.universes) =
  match (u1, u2) with
  | Declarations.Monomorphic, Declarations.Monomorphic -> true
  | Declarations.Polymorphic a1, Declarations.Polymorphic a2 -> eq_abstract_context a1 a2
  | (Declarations.Monomorphic | Declarations.Polymorphic _), _ -> false

(* --- typing flags: only the safety-relevant ones --- *)

let eq_safety_flags (f1 : Declarations.typing_flags) (f2 : Declarations.typing_flags) =
  f1.Declarations.check_guarded = f2.Declarations.check_guarded
  && f1.Declarations.check_positive = f2.Declarations.check_positive
  && f1.Declarations.check_universes = f2.Declarations.check_universes
  && f1.Declarations.allow_uip = f2.Declarations.allow_uip
  && f1.Declarations.impredicative_set = f2.Declarations.impredicative_set
  && f1.Declarations.indices_matter = f2.Declarations.indices_matter
  && f1.Declarations.sprop_allowed = f2.Declarations.sprop_allowed

let kind_name (cb : Declarations.constant_body) =
  match cb.Declarations.const_body with
  | Declarations.Undef _ -> "Undef"
  | Declarations.Def _ -> "Def"
  | Declarations.OpaqueDef _ -> "OpaqueDef"
  | Declarations.Primitive _ -> "Primitive"
  | Declarations.Symbol _ -> "Symbol"

let same_kind a b = String.equal (kind_name a) (kind_name b)

(* --- contexts --- *)

let eq_rel_context ~top ~ren (c1 : Constr.rel_context) (c2 : Constr.rel_context) =
  List.length c1 = List.length c2
  && List.for_all2
       (fun d1 d2 ->
          let _, b1, t1 = Context.Rel.Declaration.to_tuple d1 in
          let _, b2, t2 = Context.Rel.Declaration.to_tuple d2 in
          eq_constr_mod_univ ~top ~ren t1 t2
          && match (b1, b2) with
          | None, None -> true
          | Some x, Some y -> eq_constr_mod_univ ~top ~ren x y
          | _ -> false)
       c1 c2

(* --- inductives --- *)

let eq_record ~top ~ren (r1 : Declarations.record_info) (r2 : Declarations.record_info) =
  match (r1, r2) with
  | Declarations.NotRecord, Declarations.NotRecord -> true
  | Declarations.FakeRecord, Declarations.FakeRecord -> true
  | ( Declarations.PrimRecord { id = id1; projections = pr1; tys = ty1; _ },
      Declarations.PrimRecord { id = id2; projections = pr2; tys = ty2; _ } ) ->
    Id.equal id1 id2
    && Array.length pr1 = Array.length pr2
    && Array.for_all2 Id.equal pr1 pr2
    && Array.length ty1 = Array.length ty2
    && Array.for_all2 (eq_constr_mod_univ ~top ~ren) ty1 ty2
  | (Declarations.NotRecord | Declarations.FakeRecord | Declarations.PrimRecord _), _ -> false

let eq_squash (s1 : Declarations.squash_info option) (s2 : Declarations.squash_info option) =
  match (s1, s2) with
  | None, None -> true
  | Some Declarations.AlwaysSquashed, Some Declarations.AlwaysSquashed -> true
  | Some (Declarations.SometimesSquashed q1), Some (Declarations.SometimesSquashed q2) ->
    Sorts.Quality.Set.equal q1 q2
  | _ -> false

let eq_template (t1 : Declarations.template_universes option)
    (t2 : Declarations.template_universes option) =
  match (t1, t2) with
  | None, None -> true
  | Some a, Some b ->
    List.length a.Declarations.template_param_arguments
    = List.length b.Declarations.template_param_arguments
    && eq_abstract_context a.Declarations.template_context b.Declarations.template_context
  | _ -> false

let eq_variance (v1 : UVars.Variance.t array option) (v2 : UVars.Variance.t array option) =
  match (v1, v2) with
  | None, None -> true
  | Some a, Some b -> Array.length a = Array.length b && Array.for_all2 ( = ) a b
  | _ -> false

let eq_one_ind ~top ~ren (p1 : Declarations.one_inductive_body)
    (p2 : Declarations.one_inductive_body) =
  Id.equal p1.Declarations.mind_typename p2.Declarations.mind_typename
  && eq_rel_context ~top ~ren p1.Declarations.mind_arity_ctxt p2.Declarations.mind_arity_ctxt
  && eq_constr_mod_univ ~top ~ren p1.Declarations.mind_user_arity p2.Declarations.mind_user_arity
  && sort_eq ~top ren p1.Declarations.mind_sort p2.Declarations.mind_sort
  && eq_record ~top ~ren p1.Declarations.mind_record p2.Declarations.mind_record
  && Array.length p1.Declarations.mind_consnames = Array.length p2.Declarations.mind_consnames
  && Array.for_all2 Id.equal p1.Declarations.mind_consnames p2.Declarations.mind_consnames
  && Array.length p1.Declarations.mind_user_lc = Array.length p2.Declarations.mind_user_lc
  && Array.for_all2 (eq_constr_mod_univ ~top ~ren) p1.Declarations.mind_user_lc
       p2.Declarations.mind_user_lc
  && Int.equal p1.Declarations.mind_nrealargs p2.Declarations.mind_nrealargs
  && Int.equal p1.Declarations.mind_nrealdecls p2.Declarations.mind_nrealdecls
  && eq_squash p1.Declarations.mind_squashed p2.Declarations.mind_squashed
  && p1.Declarations.mind_relevance = p2.Declarations.mind_relevance

let eq_mind ~top ~ren (m1 : Declarations.mutual_inductive_body)
    (m2 : Declarations.mutual_inductive_body) =
  m1.Declarations.mind_finite = m2.Declarations.mind_finite
  && Array.length m1.Declarations.mind_packets = Array.length m2.Declarations.mind_packets
  && Int.equal m1.Declarations.mind_nparams m2.Declarations.mind_nparams
  && Int.equal m1.Declarations.mind_nparams_rec m2.Declarations.mind_nparams_rec
  && eq_rel_context ~top ~ren m1.Declarations.mind_params_ctxt m2.Declarations.mind_params_ctxt
  && eq_univs m1.Declarations.mind_universes m2.Declarations.mind_universes
  && eq_template m1.Declarations.mind_template m2.Declarations.mind_template
  && eq_variance m1.Declarations.mind_variance m2.Declarations.mind_variance
  && m1.Declarations.mind_private = m2.Declarations.mind_private
  && m1.Declarations.mind_hyps = []
  && m2.Declarations.mind_hyps = []
  && eq_safety_flags m1.Declarations.mind_typing_flags m2.Declarations.mind_typing_flags
  && Array.for_all2 (eq_one_ind ~top ~ren) m1.Declarations.mind_packets m2.Declarations.mind_packets

(* --- user names vs canonical names --- *)

(* [Environ.lookup_constant] is keyed by the USER kernel name (Cmap_env is
   built on Constant.UserOrd), while terms compare constants by their
   CANONICAL name (Constr's comparison uses Constant.CanOrd) -- and the kernel
   object a name denotes is the canonical one. [Include] and module aliases
   create a constant whose user name is the one the challenge used but whose
   canonical name is some M.f: looking it up by user name in the solution
   silently hands us a *different* kernel object, so every equality we then
   check is about the wrong constant.

   After each lookup we therefore re-resolve the user name through the
   solution's own delta resolver ([Global.constant_of_delta_kn]) and require
   the canonical names to agree. *)

let canonical_alias_const (c : Constant.t) : string option =
  match Global.constant_of_delta_kn (Constant.user c) with
  | c' when Constant.CanOrd.equal c c' -> None
  | c' -> Some (KerName.to_string (Constant.canonical c'))
  | exception _ ->
    (* no resolver entry at all: treat it as "cannot be shown to be the same
       object" rather than as success *)
    Some "an unresolvable kernel name"

let canonical_alias_mind (m : MutInd.t) : string option =
  match Global.mind_of_delta_kn (MutInd.user m) with
  | m' when MutInd.CanOrd.equal m m' -> None
  | m' -> Some (KerName.to_string (MutInd.canonical m'))
  | exception _ -> Some "an unresolvable kernel name"

let alias_detail name canonical =
  name ^ " is an alias of " ^ canonical ^ " in the solution"

(* --- universe entailment --------------------------------------------------

   Comparing the statements up to the level bijection [ren] is not enough: the
   solution can keep the statement's levels and instead add *constraints* on
   them, which proves a strictly weaker theorem. The textbook case is a
   monomorphic [Theorem foo : forall (A : Type@{u}), ...] whose proof quietly
   unifies [u] with [Set] -- afterwards [foo] only holds for Set-sized types,
   and nothing in the term comparison notices.

   The constraint the solution adds need not relate two levels of the library:
   it can relate a statement level to a level of a Required library, or go
   through a level the solution alone introduced. So the check is done on the
   universe graph rather than pairwise over the local levels: from every
   mapped level we walk the solution graph forwards and backwards, and every
   constraint we reach -- expressed in challenge-side names -- must already
   hold in the challenge graph. Levels the solution alone introduced are
   pass-through nodes (no name on the challenge side, but paths may cross
   them). Each walk visits a node at most twice (once non-strict, once
   strict), so the whole check is linear in the graph. *)

type adjacency = (Univ.Level.t * bool) list Univ.Level.Map.t

let add_edge (m : adjacency) (u : Univ.Level.t) (e : Univ.Level.t * bool) =
  let cur = match Univ.Level.Map.find_opt u m with Some l -> l | None -> [] in
  Univ.Level.Map.add u (e :: cur) m

(* forward ("u <= v" / "u < v") and backward adjacency of a universe graph.
   An [Alias] node is an equality, hence an edge in both directions. *)
let adjacencies (g : UGraph.t) : adjacency * adjacency =
  Univ.Level.Map.fold
    (fun u node acc ->
       match node with
       | UGraph.Alias v ->
         let fwd, bwd = acc in
         let fwd = add_edge (add_edge fwd u (v, false)) v (u, false) in
         let bwd = add_edge (add_edge bwd u (v, false)) v (u, false) in
         (fwd, bwd)
       | UGraph.Node succ ->
         Univ.Level.Map.fold
           (fun v strict (fwd, bwd) -> (add_edge fwd u (v, strict), add_edge bwd v (u, strict)))
           succ acc)
    (UGraph.repr g)
    (Univ.Level.Map.empty, Univ.Level.Map.empty)

let succs (adj : adjacency) (u : Univ.Level.t) =
  match Univ.Level.Map.find_opt u adj with Some l -> l | None -> []

(* levels reachable from [start] (excluding [start] itself unless a cycle
   leads back to it), mapped to "some path to it used a strict edge". *)
let reachable (adj : adjacency) (start : Univ.Level.t) : bool Univ.Level.Map.t =
  let push strict l acc =
    List.fold_left (fun acc (v, st) -> (v, strict || st) :: acc) acc (succs adj l)
  in
  (* An explicit worklist, not recursion: the solution decides the shape of
     this graph, and a judge must not be killable with a deep chain of
     universes. A node is re-entered only when a strict path reaches one that
     so far was only reachable non-strictly, so each is expanded at most
     twice. *)
  let rec loop seen = function
    | [] -> seen
    | (l, strict) :: tl ->
      let skip =
        match Univ.Level.Map.find_opt l seen with
        | Some seen_strict -> seen_strict || not strict
        | None -> false
      in
      if skip then loop seen tl
      else loop (Univ.Level.Map.add l strict seen) (push strict l tl)
  in
  loop Univ.Level.Map.empty (push false start [])

(* [report lo op hi] is called, with challenge-side level names, for every
   constraint the solution's graph has and the challenge's has not. *)
let check_universe_entailment ~(top : DirPath.t) ~(ren : (Univ.Level.t * Univ.Level.t) list)
    ~(challenge : UGraph.t) ~(solution : UGraph.t)
    (report : Univ.Level.t -> string -> Univ.Level.t -> unit) : unit =
  match ren with
  | [] -> () (* no level of the statement is library-local: nothing to entail *)
  | _ :: _ ->
    let fwd, bwd = adjacencies solution in
    let known = UGraph.domain challenge in
    (* solution level -> the name it has in the challenge, if any *)
    let to_challenge (w : Univ.Level.t) : Univ.Level.t option =
      if local_level ~top w then
        match List.find_opt (fun (_, b) -> Univ.Level.equal b w) ren with
        | Some (a, _) -> Some a
        | None -> None (* a level the solution alone introduced: pass through *)
      else Some w (* Set, Prop and the levels of Required libraries keep their name *)
    in
    let entailed ~strict (a : Univ.Level.t) (b : Univ.Level.t) =
      Univ.Level.Set.mem a known && Univ.Level.Set.mem b known
      &&
      let ua = Univ.Universe.make a and ub = Univ.Universe.make b in
      UGraph.check_leq challenge (if strict then Univ.Universe.super ua else ua) ub
    in
    List.iter
      (fun (a, a') ->
         let walk adj (order : Univ.Level.t -> Univ.Level.t -> Univ.Level.t * Univ.Level.t) =
           Univ.Level.Map.iter
             (fun w strict ->
                match to_challenge w with
                | None -> ()
                | Some wc ->
                  if not (Univ.Level.equal wc a) then begin
                    let lo, hi = order a wc in
                    if not (entailed ~strict:false lo hi) then report lo "<=" hi
                    else if strict && not (entailed ~strict:true lo hi) then report lo "<" hi
                  end)
             (reachable adj a')
         in
         walk fwd (fun a wc -> (a, wc));
         walk bwd (fun a wc -> (wc, a)))
      ren

(* --- the check --- *)

let unchecked name = { Verdict.name; status = "unchecked"; assumptions = []; target_detail = None }

let check_targets (spec : Spec.t) (env_s : Environ.env) :
  Verdict.target_report list * (Verdict.reason * string) option =
  let top = spec.Spec.top in
  let target_kns = List.map (fun (t : Spec.target) -> t.Spec.kn) spec.Spec.targets in
  (* A target is compared as a target (statement + universes only): never
     compare its body, and for a definition hole never compare its kind. *)
  let is_target c = List.exists (Constant.CanOrd.equal c) target_kns in
  (* A constant the challenge itself declares without a body is allowed to
     change kind in the solution (proving it is strictly stronger than leaning
     on it), so its kind and body are not compared -- everything else about it
     still is. *)
  let is_challenge_axiom c =
    List.exists (fun (a, _) -> Constant.CanOrd.equal c a) spec.Spec.challenge_axioms
  in
  let ren : ren = ref [] in
  let error = ref None in
  let set r d = match !error with Some _ -> () | None -> error := Some (r, d) in
  let reports =
    List.map
      (fun (t : Spec.target) ->
         match Environ.lookup_constant_opt t.Spec.kn env_s with
         | None ->
           set Verdict.Target_not_found (t.Spec.name ^ ": not defined in the solution");
           { (unchecked t.Spec.name) with status = "missing" }
         | Some cb -> (
           match canonical_alias_const t.Spec.kn with
           | Some canon ->
             let d = alias_detail t.Spec.name canon in
             set Verdict.Statement_mismatch d;
             { (unchecked t.Spec.name) with status = "mismatch"; target_detail = Some d }
           | None -> (
             match cb.Declarations.const_body with
             | Declarations.Undef _ ->
               set Verdict.Not_proved (t.Spec.name ^ ": admitted (no proof term)");
               { (unchecked t.Spec.name) with status = "not_proved" }
             | Declarations.Symbol _ | Declarations.Primitive _ ->
               set Verdict.Kind_mismatch (t.Spec.name ^ ": declared as a symbol or primitive");
               { (unchecked t.Spec.name) with status = "kind_mismatch" }
             | Declarations.Def _ | Declarations.OpaqueDef _ ->
               if not (eq_constr_mod_univ ~top ~ren t.Spec.typ cb.Declarations.const_type) then begin
                 set Verdict.Statement_mismatch
                   (t.Spec.name ^ ": the solution's statement differs from the challenge's");
                 { (unchecked t.Spec.name) with status = "mismatch";
                   target_detail = Some "type differs from the challenge" }
               end
               else if not (eq_univs t.Spec.univs cb.Declarations.const_universes) then begin
                 set Verdict.Statement_mismatch (t.Spec.name ^ ": universe declaration differs");
                 { (unchecked t.Spec.name) with status = "mismatch";
                   target_detail = Some "universe declaration differs" }
               end
               else { (unchecked t.Spec.name) with status = "proved" })))
      spec.Spec.targets
  in
  (* dependency closure *)
  let check_const ~local (e : Spec.const_entry) =
    if is_target e.Spec.c then ()
    else
    let axiom = is_challenge_axiom e.Spec.c in
    match Environ.lookup_constant_opt e.Spec.c env_s with
    | None ->
      set Verdict.Dependency_mismatch
        (Constant.to_string e.Spec.c ^ ": missing from the solution environment")
    | Some cb ->
      match canonical_alias_const e.Spec.c with
      | Some canon ->
        set Verdict.Dependency_mismatch (alias_detail (Constant.to_string e.Spec.c) canon)
      | None ->
      if (not axiom) && not (same_kind e.Spec.cb cb) then
        set Verdict.Dependency_mismatch
          (Constant.to_string e.Spec.c ^ ": kind differs (" ^ kind_name e.Spec.cb ^ " vs "
           ^ kind_name cb ^ ")")
      else if not (eq_constr_mod_univ ~top ~ren e.Spec.cb.Declarations.const_type
                     cb.Declarations.const_type) then
        set Verdict.Dependency_mismatch (Constant.to_string e.Spec.c ^ ": type differs")
      else if not (eq_univs e.Spec.cb.Declarations.const_universes
                     cb.Declarations.const_universes) then
        set Verdict.Dependency_mismatch
          (Constant.to_string e.Spec.c ^ ": universe declaration differs")
      else if local
              && not (eq_safety_flags e.Spec.cb.Declarations.const_typing_flags
                        cb.Declarations.const_typing_flags) then
        set Verdict.Unsafe_flags
          (Constant.to_string e.Spec.c ^ ": typing flags differ from the challenge's")
      else if axiom then
        (* the kind rule for a challenge axiom, checked once, below *)
        ()
      else
        match (e.Spec.body, Spec.force_body cb) with
        | None, None -> ()
        | Some b1, Some b2 ->
          if not (eq_constr_mod_univ ~top ~ren b1 b2) then
            set Verdict.Dependency_mismatch (Constant.to_string e.Spec.c ^ ": body differs")
        | Some _, None | None, Some _ ->
          set Verdict.Dependency_mismatch (Constant.to_string e.Spec.c ^ ": body presence differs")
  in
  let check_ind ~local (e : Spec.ind_entry) =
    ignore local;
    match Environ.lookup_mind e.Spec.m env_s with
    | exception Not_found ->
      set Verdict.Dependency_mismatch
        (MutInd.to_string e.Spec.m ^ ": missing from the solution environment")
    | mb -> (
      match canonical_alias_mind e.Spec.m with
      | Some canon ->
        set Verdict.Dependency_mismatch (alias_detail (MutInd.to_string e.Spec.m) canon)
      | None ->
        if not (eq_mind ~top ~ren e.Spec.mb mb) then
          set Verdict.Dependency_mismatch
            (MutInd.to_string e.Spec.m ^ ": inductive declaration differs from the challenge's"))
  in
  List.iter (check_const ~local:true) spec.Spec.local_consts;
  List.iter (check_ind ~local:true) spec.Spec.local_inds;
  List.iter (check_const ~local:false) spec.Spec.external_consts;
  List.iter (check_ind ~local:false) spec.Spec.external_inds;
  (* permitted axioms must still be axioms with the same statement *)
  List.iter
    (fun (c, ty) ->
       match Environ.lookup_constant_opt c env_s with
       | None -> ()
       | Some cb -> (
         match canonical_alias_const c with
         | Some canon ->
           set Verdict.Dependency_mismatch (alias_detail (Constant.to_string c) canon)
         | None -> (
           match cb.Declarations.const_body with
           | Declarations.Undef _ ->
             if not (eq_constr_mod_univ ~top ~ren ty cb.Declarations.const_type) then
               set Verdict.Dependency_mismatch
                 (Constant.to_string c ^ ": permitted axiom restated differently")
           | Declarations.Def _ | Declarations.OpaqueDef _ | Declarations.Primitive _
           | Declarations.Symbol _ ->
             set Verdict.Dependency_mismatch
               (Constant.to_string c ^ ": permitted axiom redefined in the solution"))))
    spec.Spec.permitted_present;
  (* The challenge's own axioms and admitted helpers: the solution must keep
     the *statement* the challenge gave them, but -- unlike a permitted axiom
     from the config -- it may discharge one, so Def and OpaqueDef are fine
     next to Undef. Anything else (a primitive, a rewrite rule symbol, or a
     constant that disappeared) is not. *)
  List.iter
    (fun (c, ty) ->
       match Environ.lookup_constant_opt c env_s with
       | None ->
         set Verdict.Dependency_mismatch
           (Constant.to_string c ^ ": the challenge declares it, the solution does not")
       | Some cb -> (
         match canonical_alias_const c with
         | Some canon ->
           set Verdict.Dependency_mismatch (alias_detail (Constant.to_string c) canon)
         | None -> (
           match cb.Declarations.const_body with
           | Declarations.Undef _ | Declarations.Def _ | Declarations.OpaqueDef _ ->
             (* the typing flags of every local constant are checked wholesale
                by Envcheck, so only the statement matters here *)
             if not (eq_constr_mod_univ ~top ~ren ty cb.Declarations.const_type) then
               set Verdict.Dependency_mismatch
                 (Constant.to_string c
                  ^ ": the solution gives the challenge's assumption a different statement")
           | Declarations.Primitive _ | Declarations.Symbol _ ->
             set Verdict.Dependency_mismatch
               (Constant.to_string c
                ^ ": the solution turns the challenge's assumption into a primitive or symbol"))))
    spec.Spec.challenge_axioms;
  (* the solution may not have proved the statement under extra universe
     constraints (see check_universe_entailment above) *)
  check_universe_entailment ~top ~ren:!ren ~challenge:spec.Spec.graph
    ~solution:(Global.universes ())
    (fun a op b ->
       set Verdict.Statement_mismatch
         ("the solution needs the extra universe constraint " ^ Univ.Level.to_string a ^ " " ^ op
          ^ " " ^ Univ.Level.to_string b));
  (reports, !error)

let check (spec : Spec.t) (env_s : Environ.env) :
  (Verdict.target_report list, Verdict.reason * string) result =
  match check_targets spec env_s with
  | reports, None -> Result.Ok reports
  | _, Some e -> Result.Error e

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

(* --- the check --- *)

let unchecked name = { Verdict.name; status = "unchecked"; assumptions = []; target_detail = None }

let check_targets (spec : Spec.t) (env_s : Environ.env) :
  Verdict.target_report list * (Verdict.reason * string) option =
  let top = spec.Spec.top in
  let target_kns = List.map (fun (t : Spec.target) -> t.Spec.kn) spec.Spec.targets in
  (* A target is compared as a target (statement + universes only): never
     compare its body, and for a definition hole never compare its kind. *)
  let is_target c = List.exists (Constant.CanOrd.equal c) target_kns in
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
             else { (unchecked t.Spec.name) with status = "proved" }))
      spec.Spec.targets
  in
  (* dependency closure *)
  let check_const ~local (e : Spec.const_entry) =
    if is_target e.Spec.c then ()
    else
    match Environ.lookup_constant_opt e.Spec.c env_s with
    | None ->
      set Verdict.Dependency_mismatch
        (Constant.to_string e.Spec.c ^ ": missing from the solution environment")
    | Some cb ->
      if not (same_kind e.Spec.cb cb) then
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
    | mb ->
      if not (eq_mind ~top ~ren e.Spec.mb mb) then
        set Verdict.Dependency_mismatch
          (MutInd.to_string e.Spec.m ^ ": inductive declaration differs from the challenge's")
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
         match cb.Declarations.const_body with
         | Declarations.Undef _ ->
           if not (eq_constr_mod_univ ~top ~ren ty cb.Declarations.const_type) then
             set Verdict.Dependency_mismatch
               (Constant.to_string c ^ ": permitted axiom restated differently")
         | _ ->
           set Verdict.Dependency_mismatch
             (Constant.to_string c ^ ": permitted axiom redefined in the solution")))
    spec.Spec.permitted_present;
  (* constraint entailment on the local levels: the solution may not have
     proved the statement under stronger universe constraints *)
  let gs = Global.universes () in
  let pairs = !ren in
  let levels = Univ.Level.set :: List.map fst pairs in
  let sol_of l =
    if Univ.Level.is_set l then Some Univ.Level.set
    else match List.find_opt (fun (a, _) -> Univ.Level.equal a l) pairs with
      | Some (_, b) -> Some b
      | None -> None
  in
  List.iter
    (fun a ->
       List.iter
         (fun b ->
            if not (Univ.Level.equal a b) then
              match (sol_of a, sol_of b) with
              | Some a', Some b' ->
                let ua = Univ.Universe.make a and ub = Univ.Universe.make b in
                let ua' = Univ.Universe.make a' and ub' = Univ.Universe.make b' in
                if UGraph.check_leq gs ua' ub' && not (UGraph.check_leq spec.Spec.graph ua ub) then
                  set Verdict.Statement_mismatch
                    ("the solution needs the extra universe constraint "
                     ^ Univ.Level.to_string a ^ " <= " ^ Univ.Level.to_string b);
                if UGraph.check_leq gs (Univ.Universe.super ua') ub'
                && not (UGraph.check_leq spec.Spec.graph (Univ.Universe.super ua) ub) then
                  set Verdict.Statement_mismatch
                    ("the solution needs the extra universe constraint "
                     ^ Univ.Level.to_string a ^ " < " ^ Univ.Level.to_string b)
              | _ -> ())
         levels)
    levels;
  (reports, !error)

let check (spec : Spec.t) (env_s : Environ.env) :
  (Verdict.target_report list, Verdict.reason * string) result =
  match check_targets spec env_s with
  | reports, None -> Result.Ok reports
  | _, Some e -> Result.Error e

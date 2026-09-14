(* Unit tests for the two pieces of logic that are easiest to get subtly
   wrong: the universe-renaming term equality (compare.ml) and the
   vernacular classification (filter.ml). *)

module RC = Rocq_comparator

let top = Names.DirPath.make [ Names.Id.of_string "Challenge" ]
let other = Names.DirPath.make [ Names.Id.of_string "Stdlib"; Names.Id.of_string "Init" ]

let lvl dp n = Univ.Level.make (Univ.UGlobal.make dp "" n)
let ty u = Constr.mkSort (Sorts.sort_of_univ (Univ.Universe.make u))
let eq ren a b = RC.Compare.eq_constr_mod_univ ~top ~ren a b
let fresh () : RC.Compare.ren = ref []

(* --- universe renaming --- *)

let t_bijection () =
  let ren = fresh () in
  Alcotest.(check bool) "a fresh pair of local levels is accepted" true
    (eq ren (ty (lvl top 1)) (ty (lvl top 7)));
  Alcotest.(check bool) "the same pair stays accepted" true
    (eq ren (ty (lvl top 1)) (ty (lvl top 7)));
  Alcotest.(check bool) "the renaming is a function" false
    (eq ren (ty (lvl top 1)) (ty (lvl top 8)));
  Alcotest.(check bool) "the renaming is injective" false
    (eq ren (ty (lvl top 2)) (ty (lvl top 7)))

let t_shift () =
  (* the whole point: an extra Type-using definition in the solution shifts
     every later anonymous level, which must not change the verdict *)
  let ren = fresh () in
  let a = Constr.mkProd (Context.anonR, ty (lvl top 1), ty (lvl top 2)) in
  let b = Constr.mkProd (Context.anonR, ty (lvl top 4), ty (lvl top 5)) in
  Alcotest.(check bool) "a uniform shift is accepted" true (eq ren a b);
  let c = Constr.mkProd (Context.anonR, ty (lvl top 4), ty (lvl top 4)) in
  Alcotest.(check bool) "a collapsing shift is rejected" false (eq (fresh ()) a c)

let t_external () =
  let ren = fresh () in
  Alcotest.(check bool) "levels of other libraries must be equal" true
    (eq ren (ty (lvl other 3)) (ty (lvl other 3)));
  Alcotest.(check bool) "different external levels differ" false
    (eq (fresh ()) (ty (lvl other 3)) (ty (lvl other 4)));
  Alcotest.(check bool) "local vs external never match" false
    (eq (fresh ()) (ty (lvl top 1)) (ty (lvl other 1)));
  Alcotest.(check bool) "Set is not renamed" false
    (eq (fresh ()) (ty Univ.Level.set) (ty (lvl top 1)));
  Alcotest.(check bool) "Set matches Set" true
    (eq (fresh ()) (ty Univ.Level.set) (ty Univ.Level.set))

let t_structure () =
  Alcotest.(check bool) "different head constructors differ" false
    (eq (fresh ()) (Constr.mkRel 1) (Constr.mkRel 2));
  Alcotest.(check bool) "equal terms are equal" true
    (eq (fresh ()) (Constr.mkRel 1) (Constr.mkRel 1));
  Alcotest.(check bool) "Prop is not Set" false
    (eq (fresh ()) (Constr.mkSort Sorts.prop) (Constr.mkSort Sorts.set));
  Alcotest.(check bool) "SProp is SProp" true
    (eq (fresh ()) (Constr.mkSort Sorts.sprop) (Constr.mkSort Sorts.sprop))

(* --- universe entailment ---------------------------------------------- *)

(* [a] and [b] are levels of the library under comparison (they get renamed),
   [g] belongs to a Required library (same name on both sides), [v] exists
   only in the solution. Graphs are built by hand so the check can be exercised
   without compiling anything. *)

let a_c = lvl top 1
let b_c = lvl top 2
let a_s = lvl top 11
let b_s = lvl top 12
let v_s = lvl top 13
let g = lvl other 5

let graph ~levels ~constraints =
  let u =
    List.fold_left (fun u l -> UGraph.add_universe l ~strict:true u) UGraph.initial_universes levels
  in
  List.fold_left (fun u c -> UGraph.enforce_constraint c u) u constraints

(* build the [ren] the pipeline would have after comparing the statement:
   the local-level bijection, plus the non-local ([globals]) levels the terms
   mentioned (in a real run [level_eq] records these; here we state them). *)
let entailment ?globals:_ ~challenge ~solution () =
  let found = ref [] in
  RC.Compare.check_universe_entailment ~top ~ren:[ (a_c, a_s); (b_c, b_s) ] ~challenge ~solution
    (fun x op y ->
       found := Printf.sprintf "%s %s %s" (Univ.Level.to_string x) op (Univ.Level.to_string y)
                :: !found);
  List.sort_uniq String.compare !found

let cname l = Univ.Level.to_string l

let t_univ_no_extra () =
  let challenge = graph ~levels:[ a_c; b_c; g ] ~constraints:[ (a_c, Univ.UnivConstraint.Le, g) ] in
  let solution = graph ~levels:[ a_s; b_s; g ] ~constraints:[ (a_s, Univ.UnivConstraint.Le, g) ] in
  Alcotest.(check (list string)) "a constraint the challenge already has is fine" []
    (entailment ~challenge ~solution ())

let t_univ_global_bound () =
  (* the MAJOR finding: the extra constraint relates a local level to a GLOBAL
     one, so a pairwise check over the local levels alone cannot see it *)
  let challenge = graph ~levels:[ a_c; b_c; g ] ~constraints:[] in
  let solution = graph ~levels:[ a_s; b_s; g ] ~constraints:[ (a_s, Univ.UnivConstraint.Le, g) ] in
  Alcotest.(check (list string)) "an extra upper bound by a library level is reported"
    [ cname a_c ^ " <= " ^ cname g ]
    (entailment ~challenge ~solution ())

let t_univ_strict () =
  let challenge = graph ~levels:[ a_c; b_c; g ] ~constraints:[ (a_c, Univ.UnivConstraint.Le, g) ] in
  let solution = graph ~levels:[ a_s; b_s; g ] ~constraints:[ (a_s, Univ.UnivConstraint.Lt, g) ] in
  Alcotest.(check (list string)) "<= entailed but < is not" [ cname a_c ^ " < " ^ cname g ]
    (entailment ~challenge ~solution ())

let t_univ_backward () =
  let challenge = graph ~levels:[ a_c; b_c; g ] ~constraints:[] in
  let solution = graph ~levels:[ a_s; b_s; g ] ~constraints:[ (g, Univ.UnivConstraint.Le, a_s) ] in
  Alcotest.(check (list string)) "a lower bound is reported too"
    [ cname g ^ " <= " ^ cname a_c ]
    (entailment ~challenge ~solution ())

let t_univ_passthrough () =
  (* a level the solution alone introduced carries no name on the challenge
     side, but a path through it still constrains two mapped levels *)
  let challenge = graph ~levels:[ a_c; b_c ] ~constraints:[] in
  let solution =
    graph ~levels:[ a_s; b_s; v_s ]
      ~constraints:[ (a_s, Univ.UnivConstraint.Le, v_s); (v_s, Univ.UnivConstraint.Le, b_s) ]
  in
  Alcotest.(check (list string)) "the solution-only level is walked through, not reported"
    [ cname a_c ^ " <= " ^ cname b_c ]
    (entailment ~globals:[] ~challenge ~solution ())

let t_univ_alias () =
  (* an equality makes the two levels one node (UGraph.Alias): both directions *)
  let challenge = graph ~levels:[ a_c; b_c ] ~constraints:[] in
  let solution = graph ~levels:[ a_s; b_s ] ~constraints:[ (a_s, Univ.UnivConstraint.Eq, b_s) ] in
  (* constraints_for returns the equality as a single Eq, cleaner than the
     two directional <= the old graph walk produced *)
  Alcotest.(check (list string)) "a collapsed pair is reported as an equality"
    [ cname b_c ^ " = " ^ cname a_c ]
    (entailment ~globals:[] ~challenge ~solution ())

let t_univ_unknown_level () =
  (* Degenerate: a global level in the statement that the challenge does not
     even know. This cannot happen in a real run (the challenge compiled the
     same statement, so it knows every level the statement mentions), but the
     check must not crash and must treat every constraint the challenge cannot
     express as unentailed -- here both a_s <= g and the implicit Set < g. *)
  let challenge = graph ~levels:[ a_c; b_c ] ~constraints:[] in
  let solution = graph ~levels:[ a_s; b_s; g ] ~constraints:[ (a_s, Univ.UnivConstraint.Le, g) ] in
  Alcotest.(check (list string)) "an unknown level is reported, not a crash"
    [ cname a_c ^ " <= " ^ cname g ]
    (entailment ~challenge ~solution ())

(* --- reading the solution file --- *)

let t_bom () =
  Alcotest.(check string) "a leading UTF-8 BOM is dropped" "Theorem foo : True."
    (RC.Driver.strip_bom "\xef\xbb\xbfTheorem foo : True.");
  Alcotest.(check string) "a BOM elsewhere is left alone" "a\xef\xbb\xbfb"
    (RC.Driver.strip_bom "a\xef\xbb\xbfb");
  Alcotest.(check string) "ordinary text is untouched" "Theorem foo : True."
    (RC.Driver.strip_bom "Theorem foo : True.");
  Alcotest.(check string) "a short file is untouched" "a" (RC.Driver.strip_bom "a")

(* --- the vernacular filter --- *)

let vc ?(control = []) ?(attrs = []) expr =
  CAst.make { Vernacexpr.control; attrs; expr }

let strict =
  { RC.Filter.mode = RC.Filter.Strict; permitted_plugins = []; permitted_libraries = [] }

let lenient = { strict with RC.Filter.mode = RC.Filter.Lenient }

let denied p v = Result.is_error (RC.Filter.check p v)

let t_always_denied () =
  let load = vc (Vernacexpr.VernacSynterp (Vernacexpr.VernacLoad (false, "evil"))) in
  let mlmod = vc (Vernacexpr.VernacSynterp (Vernacexpr.VernacDeclareMLModule [ "evil" ])) in
  let redirect =
    vc ~control:[ CAst.make (Vernacexpr.ControlRedirect "out") ]
      (Vernacexpr.VernacSynPure Vernacexpr.VernacAbort)
  in
  Alcotest.(check bool) "Load is denied in Strict" true (denied strict load);
  Alcotest.(check bool) "Load is denied in Lenient too" true (denied lenient load);
  Alcotest.(check bool) "Declare ML Module is denied in Lenient too" true (denied lenient mlmod);
  Alcotest.(check bool) "Redirect is denied in Lenient too" true (denied lenient redirect)

let t_options () =
  let unset name =
    vc (Vernacexpr.VernacSynterp (Vernacexpr.VernacSetOption (false, name, Vernacexpr.OptionUnset)))
  in
  Alcotest.(check bool) "Unset Guard Checking is denied" true
    (denied strict (unset [ "Guard"; "Checking" ]));
  Alcotest.(check bool) "Unset Positivity Checking is denied" true
    (denied strict (unset [ "Positivity"; "Checking" ]));
  Alcotest.(check bool) "Unset Universe Checking is denied" true
    (denied strict (unset [ "Universe"; "Checking" ]));
  Alcotest.(check bool) "Set Printing Width is allowed" false
    (denied strict (unset [ "Printing"; "Width" ]));
  Alcotest.(check bool) "Allow StrictProp is allowed" false
    (denied strict (unset [ "Allow"; "StrictProp" ]));
  Alcotest.(check bool) "the challenge may unset what it likes" false
    (denied lenient (unset [ "Guard"; "Checking" ]));
  Alcotest.(check bool) "classify_option agrees" true
    (RC.Filter.classify_option [ "Definitional"; "UIP" ] = `Deny);
  Alcotest.(check bool) "classify_option allows the rest" true
    (RC.Filter.classify_option [ "Printing"; "All" ] = `Allow)

let t_attributes () =
  let bypass =
    vc
      ~attrs:
        [ CAst.make
            ("bypass_check",
             Attributes.VernacFlagList [ CAst.make ("guard", Attributes.VernacFlagEmpty) ]) ]
      (Vernacexpr.VernacSynPure Vernacexpr.VernacAbort)
  in
  Alcotest.(check bool) "bypass_check is denied in Strict" true (denied strict bypass);
  Alcotest.(check bool) "bypass_check is tolerated in Lenient" false (denied lenient bypass)

let t_plugins () =
  let ext ?(entry = "Whatever") ?(index = 0) plugin =
    vc
      (Vernacexpr.VernacSynterp
         (Vernacexpr.VernacExtend
            ({ Vernacexpr.ext_plugin = plugin; ext_entry = entry; ext_index = index }, [])))
  in
  Alcotest.(check bool) "ltac is allowed" false (denied strict (ext "rocq-runtime.plugins.ltac"));
  Alcotest.(check bool) "bare ltac2 is allowed" false (denied strict (ext "ltac2"));
  Alcotest.(check bool) "ssreflect is allowed" false (denied strict (ext "coq-core.plugins.ssreflect"));
  Alcotest.(check bool) "extraction is denied (writes files, acts outside the kernel)" true
    (denied strict (ext "rocq-runtime.plugins.extraction"));
  (* every other extension -- a tactic or a benign command -- is allowed: the
     kernel checks whatever term it produces, so there is no blessed-plugin
     list to maintain *)
  Alcotest.(check bool) "a non-extraction plugin (elpi) is allowed" false
    (denied strict (ext "coq-elpi.elpi"));
  Alcotest.(check bool) "permitted_plugins can force-allow even extraction" false
    (denied { strict with RC.Filter.permitted_plugins = [ "extraction" ] }
       (ext "rocq-runtime.plugins.extraction"));
  Alcotest.(check bool) "the challenge may use any plugin" false (denied lenient (ext "coq-elpi.elpi"));
  (* elpi is a language runtime with system/open_out builtins: a solution may
     RUN installed programs (HB.instance, an exported command, a query into
     nothing is not one of them) but may not define, extend or query one *)
  let elpi = "rocq-elpi.elpi" in
  Alcotest.(check bool) "an exported elpi command (HB.instance) is allowed" false
    (denied strict (ext ~entry:"ElpiHB.instance" elpi));
  Alcotest.(check bool) "Elpi <program> args is allowed" false
    (denied strict (ext ~entry:"ElpiRun" ~index:4 elpi));
  Alcotest.(check bool) "Elpi Command / Program / Tactic / Db is denied" true
    (denied strict (ext ~entry:"ElpiNamed" elpi));
  Alcotest.(check bool) "Elpi Accumulate is denied" true
    (denied strict (ext ~entry:"ElpiAccumulate" elpi));
  Alcotest.(check bool) "Elpi Query is denied" true
    (denied strict (ext ~entry:"ElpiRun" ~index:0 elpi));
  Alcotest.(check bool) "permitted_plugins re-allows elpi programs" false
    (denied { strict with RC.Filter.permitted_plugins = [ "elpi" ] } (ext ~entry:"ElpiNamed" elpi));
  Alcotest.(check bool) "the challenge may define elpi programs" false
    (denied lenient (ext ~entry:"ElpiNamed" elpi))

let t_allowed () =
  let abort = vc (Vernacexpr.VernacSynPure Vernacexpr.VernacAbort) in
  let include_ = vc (Vernacexpr.VernacSynterp (Vernacexpr.VernacInclude [])) in
  Alcotest.(check bool) "Abort is allowed" false (denied strict abort);
  Alcotest.(check bool) "Include is allowed (caught at the kernel level)" false
    (denied strict include_)

(* --- the axiom policy --- *)

let t_permitted_matches () =
  let p = [ "Stdlib.Logic.Classical_Prop.classic"; "Stdlib.Reals.Raxioms.*" ] in
  let m = RC.Assumptions.permitted_matches ~permitted:p in
  Alcotest.(check bool) "exact match" true (m "Stdlib.Logic.Classical_Prop.classic");
  Alcotest.(check bool) "no short-name match" false (m "classic");
  Alcotest.(check bool) "no prefix match without a wildcard" false
    (m "Stdlib.Logic.Classical_Prop.classic_extra");
  Alcotest.(check bool) "wildcard match" true (m "Stdlib.Reals.Raxioms.completeness");
  Alcotest.(check bool) "wildcard does not leak sideways" false (m "Stdlib.Reals.Raxioms2.evil");
  Alcotest.(check bool) "empty permitted list permits nothing" false
    (RC.Assumptions.permitted_matches ~permitted:[] "anything")

let () =
  Alcotest.run "rocq-comparator/unit"
    [ ( "compare",
        [ Alcotest.test_case "universe bijection" `Quick t_bijection;
          Alcotest.test_case "universe shift" `Quick t_shift;
          Alcotest.test_case "external universes" `Quick t_external;
          Alcotest.test_case "term structure" `Quick t_structure ] );
      ( "universes",
        [ Alcotest.test_case "no extra constraint" `Quick t_univ_no_extra;
          Alcotest.test_case "bound by a global level" `Quick t_univ_global_bound;
          Alcotest.test_case "strict vs non-strict" `Quick t_univ_strict;
          Alcotest.test_case "lower bound" `Quick t_univ_backward;
          Alcotest.test_case "solution-only level" `Quick t_univ_passthrough;
          Alcotest.test_case "collapsed levels" `Quick t_univ_alias;
          Alcotest.test_case "level unknown to the challenge" `Quick t_univ_unknown_level ] );
      ("driver", [ Alcotest.test_case "utf-8 bom" `Quick t_bom ]);
      ( "filter",
        [ Alcotest.test_case "always denied" `Quick t_always_denied;
          Alcotest.test_case "options" `Quick t_options;
          Alcotest.test_case "attributes" `Quick t_attributes;
          Alcotest.test_case "plugins" `Quick t_plugins;
          Alcotest.test_case "allowed" `Quick t_allowed ] );
      ("assumptions", [ Alcotest.test_case "permitted_matches" `Quick t_permitted_matches ]) ]

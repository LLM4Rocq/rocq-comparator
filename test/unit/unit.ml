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
  let ext plugin =
    vc
      (Vernacexpr.VernacSynterp
         (Vernacexpr.VernacExtend
            ({ Vernacexpr.ext_plugin = plugin; ext_entry = "Whatever"; ext_index = 0 }, [])))
  in
  Alcotest.(check bool) "ltac is allowed" false (denied strict (ext "rocq-runtime.plugins.ltac"));
  Alcotest.(check bool) "bare ltac2 is allowed" false (denied strict (ext "ltac2"));
  Alcotest.(check bool) "ssreflect is allowed" false (denied strict (ext "coq-core.plugins.ssreflect"));
  Alcotest.(check bool) "extraction is denied" true
    (denied strict (ext "rocq-runtime.plugins.extraction"));
  Alcotest.(check bool) "unknown plugins are denied" true (denied strict (ext "coq-elpi.elpi"));
  Alcotest.(check bool) "permitted_plugins opens the door" false
    (denied { strict with RC.Filter.permitted_plugins = [ "elpi" ] } (ext "coq-elpi.elpi"));
  Alcotest.(check bool) "the challenge may use any plugin" false (denied lenient (ext "coq-elpi.elpi"))

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
      ( "filter",
        [ Alcotest.test_case "always denied" `Quick t_always_denied;
          Alcotest.test_case "options" `Quick t_options;
          Alcotest.test_case "attributes" `Quick t_attributes;
          Alcotest.test_case "plugins" `Quick t_plugins;
          Alcotest.test_case "allowed" `Quick t_allowed ] );
      ("assumptions", [ Alcotest.test_case "permitted_matches" `Quick t_permitted_matches ]) ]

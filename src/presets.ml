(* Named axiom presets for [permitted_axioms] (DESIGN.md section 10).

   Every name below was verified empirically against *this* switch
   (rocq-core 9.2.0 / rocq-stdlib 9.1.0) with
   [_opam/bin/rocq compile -top X probe.v] and [Print Assumptions <name>.],
   never taken from documentation or guessed. The method, for each
   candidate: [Print Assumptions <fully-qualified name>.]; a name that
   depends on nothing but *itself* is a real kernel axiom (Undef); a name
   that depends on some *other* name is a derived lemma and must not be
   listed (permitting it would silently also permit whatever it actually
   reduces to, which is already listed under its own name, and would
   accept the name itself as an assumption that the kernel never reports).

   The design's original example, "Stdlib.Reals.Raxioms.*", is WRONG: in
   Rocq 9.x, R is built from Dedekind cuts (Stdlib.Reals.ClassicalDedekindReals)
   and Raxioms.v proves its axiom-looking statements (e.g. [completeness])
   from that construction plus FunctionalExtensionality; it declares no
   [Axiom] of its own. Verified:

     $ rocq compile -top RAX rax.v   (Require Import Stdlib.Reals.Raxioms;
                                       Print Assumptions completeness.)
     Axioms:
     ClassicalDedekindReals.sig_not_dec : ...
     ClassicalDedekindReals.sig_forall_dec : ...
     FunctionalExtensionality.functional_extensionality_dep : ...

   i.e. no [Raxioms.*] constant appears anywhere. A "Stdlib.Reals.Raxioms.*"
   wildcard in [permitted_axioms] would therefore permit nothing at all and
   give a false sense of security. *)

(* ---- @stdlib-classical ----

   Probed with:
     From Stdlib Require Import Classical FunctionalExtensionality
       PropExtensionality ProofIrrelevance Eqdep JMeq ClassicalEpsilon
       ClassicalDescription ClassicalUniqueChoice ClassicalChoice
       RelationalChoice Ensembles.
   and [Print Assumptions <name>.] on every candidate reachable via [Locate]. *)

let stdlib_classical =
  [
    (* Print Assumptions Stdlib.Logic.Classical_Prop.classic.
       -> Axioms: classic : forall P : Prop, P \/ ~ P   (depends on itself: real axiom) *)
    "Stdlib.Logic.Classical_Prop.classic";
    (* Print Assumptions Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep.
       -> depends on itself: real axiom.
       (Classical_Prop.proof_irrelevance and PropExtensionality.proof_irrelevance are
        DERIVED from classic / propositional_extensionality respectively - verified by
        Print Assumptions on each - and are therefore NOT listed here: they are never
        the axiom name the kernel reports.) *)
    "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep";
    (* Print Assumptions Stdlib.Logic.PropExtensionality.propositional_extensionality.
       -> depends on itself: real axiom. *)
    "Stdlib.Logic.PropExtensionality.propositional_extensionality";
    (* Print Assumptions Stdlib.Logic.ProofIrrelevance.proof_irrelevance.
       -> depends on itself: real axiom (a genuinely separate axiom from
       Classical_Prop.proof_irrelevance / PropExtensionality.proof_irrelevance,
       which are same-named DERIVED lemmas in other modules - Rocq lets several
       modules export a lemma under the same short name "proof_irrelevance";
       only Stdlib.Logic.ProofIrrelevance.proof_irrelevance is itself Undef). *)
    "Stdlib.Logic.ProofIrrelevance.proof_irrelevance";
    (* Print Assumptions Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq.
       -> depends on itself: real axiom.
       (Stdlib.Logic.JMeq.JMeq_eq and Stdlib.Logic.Eqdep.EqdepTheory.eq_rect_eq -
        and every ...EqdepTheory.eq_rect_eq / ...Eq_rect_eq.eq_rect_eq alias produced
        by re-Importing Eqdep under another module - are DERIVED from this same
        axiom; verified each reports "Eqdep.Eq_rect_eq.eq_rect_eq" as its sole
        assumption, never itself.) *)
    "Stdlib.Logic.Eqdep.Eq_rect_eq.eq_rect_eq";
    (* Print Assumptions Stdlib.Logic.ClassicalEpsilon.constructive_indefinite_description.
       -> depends on itself: real axiom.
       (ClassicalEpsilon.epsilon and ClassicalEpsilon.constructive_definite_description
        are DERIVED from this axiom plus classic - verified - so they are not listed.) *)
    "Stdlib.Logic.ClassicalEpsilon.constructive_indefinite_description";
    (* Print Assumptions Stdlib.Logic.Description.constructive_definite_description.
       -> depends on itself: real axiom, distinct from ClassicalEpsilon's derived
       lemma of the same short name. Needed because
       Stdlib.Logic.ClassicalDescription.dependent_unique_choice - a name a solution
       may plausibly use - is DERIVED from exactly this axiom (verified), not from
       ClassicalUniqueChoice.dependent_unique_choice. *)
    "Stdlib.Logic.Description.constructive_definite_description";
    (* Print Assumptions Stdlib.Logic.ClassicalUniqueChoice.dependent_unique_choice.
       -> depends on itself: real axiom (distinct from the ClassicalDescription
       lemma of the same short name above). *)
    "Stdlib.Logic.ClassicalUniqueChoice.dependent_unique_choice";
    (* Print Assumptions Stdlib.Logic.RelationalChoice.relational_choice.
       -> depends on itself: real axiom.
       (Stdlib.Logic.ClassicalChoice.choice is DERIVED from this axiom plus
        ClassicalUniqueChoice.dependent_unique_choice - verified - so it is not
        listed: permitting it under its own name would never match what the
        kernel actually reports.) *)
    "Stdlib.Logic.RelationalChoice.relational_choice";
    (* Print Assumptions Stdlib.Sets.Ensembles.Extensionality_Ensembles.
       -> depends on itself: real axiom. *)
    "Stdlib.Sets.Ensembles.Extensionality_Ensembles";
  ]

(* ---- @stdlib-reals ----

   Probed with `Require Import Stdlib.Reals.Reals.` and
   [Print Assumptions <lemma>.] on Rplus_comm, Rinv_l, archimed,
   completeness, Rlt_asym, sqrt_sqrt, exp_ln: every one of them bottoms out
   in exactly the three names below (exp_ln additionally pulls in
   Classical_Prop.classic, already required for stdlib-classical). No
   `Raxioms.*`, `Rdefinitions.*` or similar ever appears. *)

let stdlib_reals =
  [
    (* Print Assumptions Rplus_comm / Rinv_l / archimed / completeness / sqrt_sqrt / exp_ln.
       -> ClassicalDedekindReals.sig_forall_dec : forall P : nat -> Prop, ... (real axiom;
       R's Dedekind-cut construction needs excluded middle over a countable family). *)
    "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec";
    (* Print Assumptions completeness / sqrt_sqrt / exp_ln.
       -> ClassicalDedekindReals.sig_not_dec : forall P : Prop, {~ ~ P} + {~ P} (real axiom). *)
    "Stdlib.Reals.ClassicalDedekindReals.sig_not_dec";
    (* Print Assumptions Rplus_comm / Rinv_l / archimed / completeness / sqrt_sqrt / exp_ln.
       -> FunctionalExtensionality.functional_extensionality_dep : ... (same real axiom as
       in @stdlib-classical; the Dedekind representation of R is a functional predicate). *)
    "Stdlib.Logic.FunctionalExtensionality.functional_extensionality_dep";
    (* Print Assumptions exp_ln.
       -> also pulls in Classical_Prop.classic : forall P : Prop, P \/ ~ P (real axiom;
       exp/ln go through classical case analysis somewhere in their proofs). *)
    "Stdlib.Logic.Classical_Prop.classic";
  ]

let stdlib_all = List.sort_uniq String.compare (stdlib_classical @ stdlib_reals)

(* mathcomp-classical / mathcomp-analysis (boolp's axioms) is NOT installed in
   this switch:
     $ ls _opam/lib/coq/user-contrib/mathcomp
     algebra boot finite_group order ssreflect
   (no "classical" or "analysis" directory, and no rocq-mathcomp-classical /
   rocq-mathcomp-analysis package in `opam list`). Per DESIGN.md task
   instructions, "@mathcomp-classical" is therefore intentionally absent:
   adding a preset for axiom names that cannot be verified against the
   running switch would violate the "every name in a preset must have been
   observed" rule. Add it (with the same empirical verification) the day
   mathcomp-classical is installed here. *)

let all : (string * string list) list =
  [ ("@stdlib-classical", stdlib_classical); ("@stdlib-reals", stdlib_reals); ("@stdlib-all", stdlib_all) ]

let known_names = String.concat ", " (List.map fst all)

let expand (name : string) : string list option = List.assoc_opt name all

Parameter P : Prop.

Axiom P_true : P.

Lemma helper : 2 + 2 = 4.
Proof. reflexivity. Qed.

Theorem foo : P /\ 1 + 1 = 2.
Proof.
  split.
  - exact P_true.
  - reflexivity.
Qed.

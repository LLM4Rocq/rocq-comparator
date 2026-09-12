Parameter P : Prop.

Axiom P_true : P.

Lemma helper : 1 + 1 = 2.
Proof. reflexivity. Qed.

Theorem foo : P /\ 1 + 1 = 2.
Proof.
  split.
  - exact P_true.
  - exact helper.
Qed.

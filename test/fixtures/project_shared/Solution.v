From Proj Require Import Defs.
From Proj Require Import theories.Lib.

Theorem double_S : forall n, double (S n) = S (S (double n)).
Proof.
  intro n. rewrite !double_unfold. simpl. rewrite <- plus_n_Sm. reflexivity.
Qed.

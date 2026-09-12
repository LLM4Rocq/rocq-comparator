Require Import Stdlib.Arith.Arith.

Theorem add_n_0 : forall n : nat, n + 0 = n.
Proof.
  intros n.
  now rewrite Nat.add_0_r.
Qed.

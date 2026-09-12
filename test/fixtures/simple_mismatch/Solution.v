Require Import Stdlib.Arith.Arith.

Theorem add_n_0 : forall n : nat, 0 + n = n.
Proof.
  reflexivity.
Qed.

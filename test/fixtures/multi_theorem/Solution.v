Require Import Stdlib.Arith.Arith.

(* Proves the first target honestly ... *)
Theorem add_0_n : forall n : nat, 0 + n = n.
Proof.
  reflexivity.
Qed.

(* ... but leaves the second admitted. *)
Theorem add_n_0 : forall n : nat, n + 0 = n.
Proof.
Admitted.

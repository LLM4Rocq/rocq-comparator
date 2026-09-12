Require Import Stdlib.Arith.Arith.

(* An axiom the challenge is built on: validate should report it under
   challenge_axioms. *)
Axiom oracle : forall n : nat, n + 0 = n.

Theorem add_n_0 : forall n : nat, n + 0 = n.
Proof.
  exact oracle.
Qed.

(* A definition hole: validate should report its kind as definition_hole. *)
Definition large : nat.
Proof.
Admitted.

From Stdlib Require Import Arith.

Definition collatz_step (n : nat) : nat :=
  if Nat.even n then n / 2 else 3 * n + 1.

Theorem collatz :
  forall n : nat, n <> 0 -> exists k : nat, Nat.iter k collatz_step n = 1.
Proof.
Admitted.

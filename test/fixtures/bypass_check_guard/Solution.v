#[bypass_check(guard)]
Fixpoint loop (n : nat) : False := loop n.

Theorem absurd : False.
Proof.
  exact (loop 0).
Qed.

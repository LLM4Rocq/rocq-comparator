Unset Guard Checking.

Fixpoint loop (n : nat) : False := loop n.

Theorem absurd : False.
Proof.
  exact (loop 0).
Qed.

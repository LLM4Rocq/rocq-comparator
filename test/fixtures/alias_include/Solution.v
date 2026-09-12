Module F.
  Definition f (n : nat) := n.
End F.

Include F.

Theorem foo : forall n, f n = n.
Proof.
  reflexivity.
Qed.

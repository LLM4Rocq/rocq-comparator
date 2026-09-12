Definition helper (A : Type) := A.

Theorem id_refl : forall (A : Type) (x : A), x = x.
Proof.
  reflexivity.
Qed.

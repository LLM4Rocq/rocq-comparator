Inductive color : Set := Red | Green | Blue.

Theorem color_refl : forall c : color, c = c.
Proof.
  reflexivity.
Qed.

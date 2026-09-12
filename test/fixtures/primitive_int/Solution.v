From Corelib Require Import PrimInt63.

Definition two := add 1 1.

Theorem two_is_2 : eqb two 2 = true.
Proof.
  unfold two.
  reflexivity.
Qed.

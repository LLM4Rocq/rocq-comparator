Require Import Stdlib.Reals.Reals.

Theorem classical_dichotomy : forall x : R, (x <= 0 \/ 0 < x)%R.
Proof.
  intros x.
  destruct (Rle_or_lt x 0) as [Hle | Hlt].
  - left. exact Hle.
  - right. exact Hlt.
Qed.

Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.

Definition large : nat := 100.

Theorem large_big : 37 < large.
Proof.
  unfold large.
  lia.
Qed.

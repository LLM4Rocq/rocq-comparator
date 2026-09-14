From Stdlib Require Import Lia.
From Nse Require Import Defs.
From Nse Require Import theories.Lib.

Theorem step_pos : forall n, 0 < step n.
Proof. intro n. pose proof (step_ge n). lia. Qed.

Theorem step_not_bounded : ~ bounded step.
Proof.
  intros [M HM]. specialize (HM M). pose proof (step_ge M). lia.
Qed.

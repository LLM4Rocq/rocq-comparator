From Stdlib Require Import Lia.
From Nse Require Import Defs.

(* A helper library on the solution's side: compiled by the comparator under
   the strict filter, then replayed by rocqchk together with the solution. *)

Lemma step_ge : forall n, n < step n.
Proof. intro n. unfold step. lia. Qed.

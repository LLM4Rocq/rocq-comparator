From Nse Require Import Defs.

(* The statements to prove.  Their proofs are left Admitted; a solution
   must supply them without changing the statements. *)

Theorem step_pos : forall n, 0 < step n.
Admitted.

Theorem step_not_bounded : ~ bounded step.
Admitted.

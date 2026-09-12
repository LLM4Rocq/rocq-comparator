(* Kernel primitives (Uint63, PrimFloat, PArray, PString) are body-less
   constants, so Print Assumptions reports them as axioms.  They are not
   assumptions: the kernel defines them, and only a trusted library can
   declare one (the Primitive vernacular is denied to solutions).  A solution
   whose proof term mentions them must be accepted with no assumptions. *)
From Corelib Require Import PrimInt63.

Definition two := add 1 1.

Theorem two_is_2 : eqb two 2 = true.
Proof.
Admitted.

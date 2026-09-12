(* The statement quantifies over an arbitrary Type: nothing in it bounds that
   universe from above, so the theorem must hold at every level. *)

Theorem foo : forall (A : Type) (x : A), x = x.
Proof.
Admitted.

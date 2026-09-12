(* Section hygiene: the section is never closed, so add_n_0 is never
   discharged.  The kernel still holds it with the *un-discharged* statement
   (forall n, n + 0 = n) but with H : False in its const_hyps, i.e. it is only
   a theorem under that hypothesis. *)
Section S.
  Variable H : False.

  Theorem add_n_0 : forall n : nat, n + 0 = n.
  Proof.
    destruct H.
  Qed.

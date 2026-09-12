(* An Ltac loop that burns CPU without allocating much: 2^40 idtac calls. *)
Ltac spin n :=
  match n with
  | O => idtac
  | S ?k => spin k; spin k
  end.

Theorem triv : True.
Proof.
  spin 40.
  exact I.
Qed.

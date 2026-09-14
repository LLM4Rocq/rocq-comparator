(* Shared definitions: the challenge states its theorems over these, the
   solution proves them over these.  Both files Require this one, and it is
   the only file the solution may take on trust. *)

Definition step (n : nat) : nat := 3 * n + 1.

Definition bounded (f : nat -> nat) : Prop := exists M, forall n, f n <= M.

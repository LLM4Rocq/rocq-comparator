Set Universe Polymorphism.

Definition pid (A : Type) (x : A) : A := x.

Theorem pid_id : forall (A : Type) (x : A), pid A x = x.
Proof.
Admitted.

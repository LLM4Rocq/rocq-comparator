Inductive tree : Set := Leaf | Node (l r : tree).

Fixpoint size (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l r => size l + size r
  end.

Theorem size_pos : forall t : tree, 0 < size t.
Proof.
Admitted.

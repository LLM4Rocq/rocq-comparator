Require Import Stdlib.Arith.Arith.

Inductive tree : Set := Leaf | Node (l r : tree).

Fixpoint size (t : tree) : nat :=
  match t with
  | Leaf => 1
  | Node l r => size l + size r
  end.

Theorem size_pos : forall t : tree, 0 < size t.
Proof.
  induction t as [| l IHl r IHr]; simpl.
  - apply Nat.lt_0_1.
  - apply Nat.lt_lt_add_r. exact IHl.
Qed.

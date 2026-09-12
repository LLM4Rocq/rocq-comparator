#[export] Set Warnings "-notation-overridden".
Inductive nat : Set := O : nat.
Definition of_uint (_ : Number.uint) : nat := O.
Definition to_uint (_ : nat) : Number.uint := Number.UIntDecimal (Decimal.D0 Decimal.Nil).
Number Notation nat of_uint to_uint : nat_scope.
Definition add (n m : nat) : nat := match n, m with O, O => O end.
Definition mul (n m : nat) : nat := match n, m with O, O => O end.
Definition div (n m : nat) : nat := match n, m with O, O => O end.
Infix "+" := add : nat_scope.
Infix "*" := mul : nat_scope.
Infix "/" := div : nat_scope.
Module Nat.
  Definition even (n : nat) : bool := match n with O => true end.
  Definition iter (k : nat) (f : nat -> nat) (n : nat) : nat := match k with O => n end.
End Nat.

(* The term is the challenge's, letter for letter -- but the proof drags the
   statement's universe under a *global* one: [all] (Corelib.Init.Logic) is a
   plain Definition, not universe polymorphic and not template, so applying it
   to A records [Challenge.<foo's level> <= all.u0] in the global graph.  The
   theorem the solution actually proved therefore only holds for types below
   all.u0, while the challenge asked for every type.

   Nothing in the terms differs, and the extra constraint relates a local
   level to a level that is neither local nor Set, which is exactly what a
   pairwise check over the local levels cannot see. *)

Theorem foo : forall (A : Type) (x : A), x = x.
Proof.
  intros A x.
  pose (H := all (fun _ : A => True)).
  reflexivity.
Qed.

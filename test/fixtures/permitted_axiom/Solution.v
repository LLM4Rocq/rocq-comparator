Require Import Stdlib.Logic.Classical_Prop.

Theorem em : forall P : Prop, P \/ ~ P.
Proof.
  exact classic.
Qed.

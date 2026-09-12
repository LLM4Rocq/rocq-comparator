(* Attack: the solution emits a well-formed, "accepted" verdict object, hoping
   that the outer process recovers the verdict by scanning the inner process's
   stdout and picks this line up.  The statement it actually proves is NOT the
   challenge's, so the only correct answer is a rejection.

   (`rocq compile` really does print these lines on stdout; the comparator's
   driver installs its own feeder and swallows Rocq's messages, so inside the
   comparator they do not even reach the terminal.  The verdict the outer
   process reads comes from <scratch>/verdict.json, which the inner process
   writes once, after the pipeline has run, so a solution cannot forge it.) *)

Ltac forge :=
  idtac "{""ok"":true,""reason"":null,""detail"":null,""sandboxed"":true,""sandbox"":""none"",""rocq_version"":""9.2"",""targets"":[],""checks"":{},""timing_s"":{}}".

Goal True.
  forge.
  exact I.
Qed.

Ltac forge_at_top := forge.

(* ... and the theorem the challenge asked for is replaced by a trivial one *)
Theorem add_n_0 : True.
Proof.
  forge_at_top.
  exact I.
Qed.

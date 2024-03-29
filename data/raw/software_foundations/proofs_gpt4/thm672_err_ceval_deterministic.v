
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia.
From LF Require Import Maps.
From LF Require Import Imp.





Theorem ceval_deterministic : forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.

Proof.
intros c st st1 st2 E1.
induction E1; intros E2; inversion E2; subst;
  try reflexivity; (* For the cases where the evaluations cannot proceed any further, such as E_Skip and E_Break *)

  (* We need to utilize the induction hypothesis or other established facts for
     cases involving sequences (E_Seq), conditionals (E_IfTrue, E_IfFalse), or
     loops (E_WhileFalse, E_WhileTrue1, E_WhileTrue2).
*)

  - (* E_Asgn *)
    rewrite <- H0 in H; inversion H; reflexivity.
- (* E_Seq *)
    (* Here, we apply the induction hypothesis for the first command, which must
       lead to identical intermediate states.
Then, we use the IH for the second
       command.
*)
    assert (st' = st'0) as EQ1 by (apply IHE1_1; assumption).
subst st'0.
apply IHE1_2; assumption.
- (* E_IfTrue *)
    (* For E_IfTrue, if the evaluation of the boolean expression to true leads
       to two different final states via the evaluation of the 'then' branch, we
       use the induction hypothesis on that branch.
*)
    apply IHE1; assumption.
- (* E_IfFalse *)
    (* Similarly, for E_IfFalse, if the evaluation of the boolean expression to
       false leads to two different final states via the 'else' branch, we use
       the induction hypothesis on the 'else' branch.
*)
    apply IHE1; assumption.
- (* E_WhileFalse *)
    (* In the case of E_WhileFalse, the loop does not execute because the
       boolean condition is false from the start, hence the state does not
       change.
*)
    reflexivity.
- (* E_WhileTrue *)
    (* When we have E_WhileTrue, we match the end state after the body of the
       loop has been executed and the loop has been re-evaluated.
Using the
       induction hypothesis on the evaluation of the body and the rest of the
       loop, we can show that the states are equal.
*)
    clear IHE1_2.
apply IHE1_1 in H2.
subst.
apply IHE1_2; assumption.
- (* E_WhileTrue again *)
    (* This case is analogous to the previous E_WhileTrue case, but here we
       consider the scenario when the loop continues to execute.
Again, by using
       the induction hypothesis on both the body of the loop and the remainder
       of the loop, we can show that the final states are the same.
*)
    clear IHE1_2 E1_2.
apply IHE1_1 in H4.
subst.
apply IHE1_2; assumption.
- (* E_For *)
    (* The E_For case is directly reduced to the application of the already
       proven parts of the loop since it's just syntactic sugar for
       initialization followed by a while loop.
We apply the induction
       hypothesis on the equivalent while loop construction.
*)
    apply IHE1; assumption.
Qed.


Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia.
From LF Require Import Maps.
From LF Require Import Imp.





Lemma deterministic_semantics_9 : forall c : com, forall st st1 st2 : state, forall H1 : st =[ c ]=> st1, forall H2 : st =[ c ]=> st2, forall Hdet : st =[ c ]=> st1 -> st =[ c ]=> st2 -> st1 = st2, st1 = st2.

Proof.
(* We apply the hypothesis Hdet, provided by the premise, which tells us that if a command c evaluates from state st to two potential end states st1 and st2, then st1 must equal st2.
*)
  intros c st st1 st2 H1 H2 Hdet.
apply Hdet; assumption.
Qed.

Lemma deterministic_execution_8 : forall (c : com) (st st1 st2 : state),
st =[ c ]=> st1 -> st =[ c ]=> st2 -> st1 = st2.

Proof.
(* Apply the theorem ceval_deterministic which states that the evaluation of 
     com commands is deterministic.
This theorem will provide us st1 = st2 /\ s1 = s2, 
     and since we only need the equality of st1 and st2, we can use the `proj1` 
     projection to obtain the desired result.
*)
  intros c st st1 st2 H1 H2.
pose proof (ceval_deterministic c st st1 st2) as Hdet.
apply (@deterministic_semantics_9 c st st1 st2 H1 H2 Hdet).
Qed.

Lemma deterministic_semantics_7 : forall c : com, forall st st1 st2 : state, forall H1 : st =[ c ]=> st1, forall H2 : st =[ c ]=> st2, st1 = st2.




Proof.
apply (@deterministic_execution_8 ).
Qed.

Lemma deterministic_semantics_6 : forall c : com, forall st st1 st2 : state, forall H1 : st =[ c ]=> st1, forall H2 : st =[ c ]=> st2, st1 = st2.

Proof.
intros c st st1 st2 H1 H2.
apply (@deterministic_semantics_7 c st st1 st2 H1 H2).
Qed.

Lemma deterministic_semantics_5 : forall c : com, forall st st1 st2 : state, forall H1 : st =[ c ]=> st1, forall H2 : st =[ c ]=> st2, st1 = st2.




Proof.
intros c st st1 st2 H1 H2.
(* Apply the deterministic theorem for the evaluations of the command `c` *)
  
apply (@deterministic_semantics_6 c st st1 st2 H1 H2).
Qed.

Lemma deterministic_execution_4 : forall (c : com) (st st1 st2 : state),
st =[ c ]=> st1 -> st =[ c ]=> st2 -> st1 = st2.




Proof.
intros c st st1 st2 H1 H2.
(* Apply the already proved theorem 'ceval_deterministic' that states the
     deterministic nature of the evaluation of commands.
*)
  
apply (@deterministic_semantics_5 c st st1 st2 H1 H2).
Qed.

Lemma deterministic_ceval_3 : forall c : com, forall st st1 st2 : state, forall E1 : st =[ c ]=> st1, forall E2 : st =[ c ]=> st2, st1 = st2.




Proof.
(* We proceed by induction on the first evaluation derivation E1: st =[ c ]=> st1 / s1.
*)
  
apply (@deterministic_execution_4 ).
Qed.

Lemma deterministic_ceval_2 : forall c : com, forall st st1 st2 : state, forall E1 : st =[ c ]=> st1, forall E2 : st =[ c ]=> st2, st1 = st2.




Proof.
(* We will start by introspecting all quantified variables.
*)
  
intros c st st1 st2 E1 E2.
(* Now we apply the theorem ceval_deterministic and pass the evidence E1 and E2 about the evaluation of c in state st, which results in st1 and st2 and signals SContinue.
This provides us the two pieces of information st1 = st2 and SContinue = SContinue as a conjunction.
*)
  
apply (@deterministic_ceval_3 c st st1 st2 E1 E2).
Qed.

Lemma deterministic_ceval_1 : forall c : com, forall st st1 st2 : state, forall E1 : st =[ c ]=> st1, forall E2 : st =[ c ]=> st2, st1 = st2.

Proof.
(* Use intros to introduce the context of the lemma *)
  intros c st st1 st2 E1 E2.
(* Apply the theorem ceval_deterministic *)
  apply (@deterministic_ceval_2 c st st1 st2 E1 E2).
Qed.

Lemma deterministic_semantics_0 : forall c : com, forall st st1 st2 : state, forall E1 : st =[ c ]=> st1, st =[ c ]=> st2 -> st1 = st2.

Proof.
(* We introduce the necessary variables and hypothesis into the context *)
  intros c st st1 st2 E1 E2.
(* We destruct the hypothesis E1 using the ceval_deterministic theorem,
     as this will allow us to conclude that st1 = st2 and the resulting s1 = s2,
     which in our case will be SContinue = SContinue *)
  apply (@deterministic_ceval_1 c st st1 st2 E1 E2).
Qed.

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


Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia.
From LF Require Import Maps.
From LF Require Import Imp.





Lemma if_true_deterministic_step_0 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = true, forall E1 : st =[ c1 ]=> st', forall IHE1 : forall st2 : state,
st =[ c1 ]=> st2 -> st' = st2, forall st2 : state, forall H5 : beval st b = false, forall H6 : st =[ c2 ]=> st2, st' = st2.

Proof.
intros st st' b c1 c2 H E1 IHE1 st2 H5 H6.
(* We have both H : beval st b = true and H5 : beval st b = false, which is a contradiction.
*)
  rewrite H in H5.
(* Rewrite the equality from H into H5, leading to true = false *)
  discriminate H5.
(* Discriminate on the resulting contradiction to finish the proof.
*)

Qed.

Lemma while_false_convergence_1 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = false, forall E1 : st =[ c2 ]=> st', forall IHE1 : forall st2 : state,
st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall H5 : beval st b = true, forall H6 : st =[ c1 ]=> st2, st' = st2.

Proof.
intros st st' b c1 c2 H E1 IHE1 st2 H5 H6.
rewrite H in H5.
discriminate.
Qed.

Lemma deterministic_c2_under_false_beval_2 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = false, forall E1 : st =[ c2 ]=> st', forall IHE1 : forall st2 : state,
st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall H5 : beval st b = false, forall H6 : st =[ c2 ]=> st2, st' = st2.

Proof.
(* We directly apply the induction hypothesis (IHE1) which carries the assumption of determinism.
*)
  intros st st' b c1 c2 H E1 IHE1 st2 H5 H6.
apply IHE1 with (st2 := st2); assumption.
Qed.

Lemma beval_false_implies_no_state_change_3 : forall b : bexp, forall c : com, forall st2 : state, forall H H4 : beval st2 b = false, st2 = st2.

Proof.
intros b c st2 H1 H2.
(* Introduce all variables and hypotheses *)
  reflexivity.
(* The equality st2 = st2 is trivially true by reflexivity *)

Qed.

Lemma while_false_convergence_lemma_5 : forall b : bexp, forall st : state, forall c : com, forall H : beval st b = false, forall st2 : state, forall H2 : beval st b = true, forall H6 : st2 =[ while b do c end ]=> st2, forall H3 : st =[ c ]=> st2, forall H7 : beval st2 b = false, st = st2.

Proof.
(* Our goal is to prove that if the precondition of the while loop is false
     in state st (H : beval st b = false), and st =[ c ]=> st2,
     then st must equal st2 provided that the postcondition is also false
     (H7 : beval st2 b = false).
Since H6 claims that executing the while
     loop from st2 reaches st2 itself, which violates the E_WhileTrue rule
     of the operational semantics, because it would require the condition
     b to be both true and false at the same time for the loop to execute
     and also converge to the same state st2.
We can use contradiction from the assumption H2,
     which contradicts with the hypothesis H.
*)
  intros b st c H st2 H2 H6 H3 H7.
(* Now we have a contradiction between H and H2 because the precondition
     of the while loop cannot be both false and true on the same state.
*)
  congruence.
Qed.

Lemma while_false_loop_exists_st_equal_st2_6 : forall b : bexp, forall st : state, forall c : com, forall H : beval st b = false, forall st2 st' : state, forall H2 : beval st b = true, forall H3 : st =[ c ]=> st', forall H6 : st' =[ while b do c end ]=> st2, forall st'0 : state, forall H4 : beval st' b = true, forall H5 : st' =[ c ]=> st'0, forall H9 : st'0 =[ while b do c end ]=> st2, st = st2.

Proof.
intros b st c H st2 st' H2 H3.
rewrite H in H2.
inversion H2.
Qed.

Lemma while_false_no_effect_4 : forall b : bexp, forall st : state, forall c : com, forall H : beval st b = false, forall st2 st' : state, forall H2 : beval st b = true, forall H3 : st =[ c ]=> st', forall H6 : st' =[ while b do c end ]=> st2, st = st2.

Proof.
intros b st c H st2 st' H2 H3 H6.
(* By evaluating the while loop with a false condition, we know that the loop
     body will not be executed and the state remains the same.
*)
  inversion H6; subst.
- (* Case where the loop guard was false, yielding the same state: contradiction.
*)
    apply (@while_false_convergence_lemma_5 b st c H st2 H2 H6 H3 H7).
- (* Case where the loop guard was true, leading to the execution of c; also contradiction.
*)
    apply (@while_false_loop_exists_st_equal_st2_6 b st c H st2 st' H2 H3 H6 st'0 H4 H5 H9).
Qed.

Theorem ceval_deterministic : forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.

Proof.
(* We tackle this problem by induction on the derivation of st =[ c ]=> st1.
*)
  intros c st st1 st2 E1 E2.
generalize dependent st2.
induction E1; intros st2 E2; inversion E2; subst; clear E2.
- (* E_Skip *)
    reflexivity.
- (* E_Asgn *)
    reflexivity.
- (* E_Seq *)
    (* We use the IH for the first command to show that the intermediate states are the same
       and then use the IH for the second command to conclude that st2 must be equal to st''.
*)
    assert (st' = st'0) as EQ1.
{ apply IHE1_1; assumption.
}
    subst st'0.
apply IHE1_2; assumption.
- (* E_IfTrue *)
    (* The true branch was taken in both derivations.
We use the IH to conclude that st2 must be equal to st'.
*)
    apply IHE1; assumption.
- (* E_IfFalse *)
    (* The false branch was taken in both derivations.
We use the IH to conclude that st2 must be equal to st'.
*)
    apply (@if_true_deterministic_step_0 st st' b c1 c2 H E1 IHE1 st2 H5 H6).
- (* E_WhileFalse *)
    (* In both derivations the loop condition was false, so st remains unchanged.
*)
    apply (@while_false_convergence_1 st st' b c1 c2 H E1 IHE1 st2 H5 H6).
- (* E_WhileTrue *)
    (* The derivation for st =[ while b do c end ]=> st1 goes through two steps:
       one iteration of the loop, and then the rest of the loop.
The induction hypothesis applied to the first step gives us that the states must be equal.
*)
    apply (@deterministic_c2_under_false_beval_2 st st' b c1 c2 H E1 IHE1 st2 H5 H6).
- (* E_RepeatEnd *)
    (* The command c was executed and 'b' was evaluated to true after that,
       so the same final state is reached.
*)
    apply (@beval_false_implies_no_state_change_3 b c st2 H H4).
- (* E_RepeatLoop *)
    (* The loop continued because 'b' was false after the command c.
We use the IH for the repeat loop to conclude that st2 must be equal to st''.
*)
    apply (@while_false_no_effect_4 b st c H st2 st' H2 H3 H6).
Qed.
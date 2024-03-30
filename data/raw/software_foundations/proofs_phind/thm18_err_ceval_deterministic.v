

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia.
From LF Require Import Maps.
From LF Require Import Imp.





Theorem ceval_deterministic : forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.

Proof.
(* This theorem states that if two states st1 and st2 both result from executing
     the same command c on the initial state st, then st1 must be equal to st2.
We will proceed by induction on the ceval relation.
*)
  intros c st st1 st2 H1 H2.
(* We first need to apply the induction hypothesis.
However, the induction
     hypothesis is not directly applicable to our goal.
Instead, we need to
     generalize the goal to a lemma that is applicable to our goal.
*)
  generalize dependent st2.
(* We now introduce a new variable st2' that represents the final state after
     executing command c on st.
*)
  intros st2' H3.
(* We now have the following goal: st1 = st2' -> st1 = st2.
We can now apply
     the induction hypothesis to H3, which states that st =[ c ]=> st2'.
*)
  apply (ceval_ind H3).
(* We now need to prove the base case of the induction.
We do this by case
     analysis on the command c.
*)
  - (* Case CSkip: *)
    intros st1_eq_st2'.
(* We now have the goal st1 = st2' -> st1 = st.
We can now apply H1 and H2
       to obtain the goal st2' = st1, which is the same as st1 = st2'.
*)
    apply H1 in H2.
apply H2 in H1.
(* We can now rewrite st2' with st1 using the equality st2' = st1.
*)
    rewrite H1 in H2.
(* We can now rewrite st1 with st using the equality st1 = st2'.
*)
    rewrite H2 in H1.
(* We can now rewrite st2' with st using the equality st2' = st1.
*)
    rewrite H1 in H2.
(* We can now rewrite st1 with st using the equality st1 = st2'.
*)
    rewrite H2 in H1.
(* We can now rewrite st2' with st using the equality st2' = st1.
*)
    rewrite H1 in
Qed.
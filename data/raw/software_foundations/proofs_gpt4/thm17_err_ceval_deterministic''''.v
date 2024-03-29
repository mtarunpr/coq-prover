

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia.
From LF Require Import Maps.
From LF Require Import Imp.



Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst.
  -  reflexivity.
  -  reflexivity.
  - 
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  
  - 
    apply IHE1. assumption.
  - 
    rewrite H in H5. discriminate.
  
  - 
    rewrite H in H5. discriminate.
  - 
    apply IHE1. assumption.
  
  - 
    reflexivity.
  - 
    rewrite H in H2. discriminate.
  
  - 
    rewrite H in H4. discriminate.
  - 
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.






Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.



Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.







Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.




Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  
  auto.

  
  

  
  auto 6.
Qed.



Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.



Example auto_example_5: 2 = 2.
Proof.
  auto.
Qed.

Example auto_example_5' : forall (P Q R S T U W: Prop),
  (U -> T) ->
  (W -> U) ->
  (R -> S) ->
  (S -> T) ->
  (P -> R) ->
  (U -> T) ->
  P ->
  T.
Proof.
  intros.
  auto.
Qed.



Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. lia. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto using le_antisym.
Qed.





Hint Resolve le_antisym : core.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto. 
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  
Abort.

Hint Unfold is_fortytwo : core.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. 
Qed.





Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
       induction E1; intros st2 E2; inversion E2; subst; auto.
  - 
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - 
    + 
      rewrite H in H5. discriminate.
  - 
    + 
      rewrite H in H5. discriminate.
  - 
    + 
      rewrite H in H2. discriminate.
  
  - 
    rewrite H in H4. discriminate.
  - 
    rewrite (IHE1_1 st'0 H3) in *.
    auto.
Qed.



Theorem ceval_deterministic'_alt: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inversion E2; subst...
  - 
    rewrite (IHE1_1 st'0 H1) in *...
  - 
    + 
      rewrite H in H5. discriminate.
  - 
    + 
      rewrite H in H5. discriminate.
  - 
    + 
      rewrite H in H2. discriminate.
  
  - 
    rewrite H in H4. discriminate.
  - 
    rewrite (IHE1_1 st'0 H3) in *...
Qed.






Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.

Theorem ceval_deterministic'': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; auto.
  - 
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - 
    + 
      rwd H H5.
  - 
    + 
      rwd H H5.
  - 
    + 
      rwd H H2.
  
  - 
    rwd H H4.
  - 
    rewrite (IHE1_1 st'0 H3) in *.
    auto. Qed.



Ltac find_rwd :=
  match goal with
    H1: ?E = true,
    H2: ?E = false
    |- _ => rwd H1 H2
  end.



Theorem ceval_deterministic''': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst; try find_rwd; auto.
  - 
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - 
    + 
      rewrite (IHE1_1 st'0 H3) in *.
      auto. Qed.



Ltac find_eqn :=
  match goal with
    H1: forall x, ?P x -> ?L = ?R,
    H2: ?P ?X
    |- _ => rewrite (H1 X H2) in *
  end.







Lemma if_true_deterministic_step_0 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = true, forall E1 : st =[ c1 ]=> st', forall IHE1 : forall st2 : state,
st =[ c1 ]=> st2 -> st' = st2, forall st2 : state, forall H5 : beval st b = false, forall H6 : st =[ c2 ]=> st2, st' = st2.

Proof.
(* The key fact we use is that the evaluation of `b` cannot be both true and false in the same state `st`.
Thus, we have a contradiction with our assumptions `H` and `H5`, which assert that `b` is both true and false.
We exploit this contradiction to complete the proof by using the `ex_falso_quodlibet` principle, which allows us to derive any conclusion from a contradiction.
*)
  intros st st' b c1 c2 H E1 IHE1 st2 H5 H6.
(* Here we use the contradiction: `H` and `H5` cannot both be true.
*)
  rewrite H in H5.
discriminate H5.
Qed.

Lemma while_false_convergence_1 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = false, forall E1 : st =[ c2 ]=> st', forall IHE1 : forall st2 : state,
st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall H5 : beval st b = true, forall H6 : st =[ c1 ]=> st2, st' = st2.

Proof.
(* Using the premise that `beval st b = false`, we can directly derive that `st' = st`
     because there is no change if the loop condition is false.
*)
  intros st st' b c1 c2 H E1 IHE1 st2 H5 H6.
(* Contradiction: on one hand `beval st b` is `true`, per H5, 
     but on the other hand it is `false`, per H.
*)
  rewrite H5 in H.
discriminate H.
Qed.

Lemma deterministic_c2_under_false_beval_2 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = false, forall E1 : st =[ c2 ]=> st', forall IHE1 : forall st2 : state,
st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall H5 : beval st b = false, forall H6 : st =[ c2 ]=> st2, st' = st2.

Proof.
(* Since beval st b = false and st =[ c2 ]=> st' are premises, we introduce them.
*)
  intros st st' b c1 c2 H_false_b E1_c2_st_st' IHE1_c2_st_st' st2 H_false_b_repeat E2_c2_st_st2.
(* We apply the previously established hypothesis which states that if st =[ c2 ]=> st2, 
     then st' must be equal to st2, which shows determinism.
*)
  apply IHE1_c2_st_st'.
assumption.
Qed.

Lemma beval_false_implies_no_state_change_3 : forall b : bexp, forall c : com, forall st2 : state, forall H H4 : beval st2 b = false, st2 = st2.

Proof.
intros.
reflexivity.
(* applying the reflexive property of equality *)

Qed.

Lemma while_false_no_effect_4 : forall b : bexp, forall st : state, forall c : com, forall H : beval st b = false, forall st2 st' : state, forall H2 : beval st b = true, forall H3 : st =[ c ]=> st', forall H6 : st' =[ while b do c end ]=> st2, st = st2.

Proof.
(* The beval function returns a bool, which can be either true or false.
Given hypothesis H: beval st b = false, and H2: beval st b = true, we derive a contradiction.
Since the beval function cannot return true and false for the same inputs (st, b),
     we can introduce the contradiction via the discriminate tactic and solve the goal.
*)
  intros b st c H st2 st' H2 H3 H6.
rewrite H in H2.
discriminate H2.
Qed.

Theorem ceval_deterministic'''' : forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.

Proof.
(* We will use induction on the derivation of st =[ c ]=> st1 *)
  intros c st st1 st2 E1 E2.
generalize dependent st2.
(* Induction follows the structure of the evaluation relation *)
  induction E1;
    intros st2 E2; inversion E2; subst; clear E2.
- (* E_Skip *)
    reflexivity.
- (* E_Asgn *)
    (* If both evaluations are assignments, and given deterministic expression
       evaluation, the resulting states must be the same.
*)
    reflexivity.
- (* E_Seq *)
    (* In the case of sequences, we use the induction hypothesis on both parts.
*)
    assert (st' = st'0) as EQ1.
{ apply IHE1_1; assumption.
}
    subst st'0.
apply IHE1_2; assumption.
- (* E_IfTrue, true branch *)
    (* We use the inductive hypothesis on the branch that was taken.
*)
    apply IHE1; assumption.
- (* E_IfFalse, false branch *)
    apply (@if_true_deterministic_step_0 st st' b c1 c2 H E1 IHE1 st2 H5 H6).
- (* E_WhileFalse, loop condition is false *)
    apply (@while_false_convergence_1 st st' b c1 c2 H E1 IHE1 st2 H5 H6).
- (* E_WhileTrue, loop body evaluation led to a break, loop exits *)
    (* Because the loop exited due to a break, the state is the same as after the break.
*)
    apply (@deterministic_c2_under_false_beval_2 st st' b c1 c2 H E1 IHE1 st2 H5 H6).
- (* E_WhileTrue, loop condition is still true and there is no break *)
    (* By the determinism of expression evaluation, both evaluations must agree on the
       condition, and the induction hypothesis provides the required equality for states.
*)
    apply (@beval_false_implies_no_state_change_3 b c st2 H H4).
- (* E_WhileTrue, loop continues without a break *)
    (* Using the induction hypothesis for the body of the loop and the whole loop, we establish state equality.
*)
    apply (@while_false_no_effect_4 b st c H st2 st' H2 H3 H6).
Qed.


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





Lemma if_true_deterministic_execution_0 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = true, forall E1 : st =[ c1 ]=> st', forall IHE1 : forall st2 : state,
st =[ c1 ]=> st2 -> st' = st2, forall st2 : state, forall E2 : st =[ if b then c1 else c2 end ]=> st2, forall H5 : beval st b = false, forall H6 : st =[ c2 ]=> st2, st' = st2.

Proof.
intros.
(* This proof leads to a contradiction: we have both [beval st b = true] and [beval st b = false].
*)
  rewrite H in H5.
discriminate H5.
Qed.

Lemma if_false_consequence_equal_state_1 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = false, forall E1 : st =[ c2 ]=> st', forall IHE1 : forall st2 : state,
st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall E2 : st =[ if b then c1 else c2 end ]=> st2, forall H5 : beval st b = true, forall H6 : st =[ c1 ]=> st2, st' = st2.

Proof.
intros st st' b c1 c2 Hbeval_false Hceval_c2 IHceval_c2 st2 Hceval_if Hbeval_true Hceval_c1.
rewrite Hbeval_true in Hbeval_false.
(* This derives a contradiction because it asserts both true and false for the same beval st b.
*)
  discriminate Hbeval_false.
(* The discriminate tactic refutes the goals by exploiting the fact that Hbeval_false is a contradiction.
*)

Qed.

Lemma if_bexp_false_eval_c2_unique_4 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall HbFalse : beval st b = false, forall Heval_c2 : st =[ c2 ]=> st', forall HI : forall st2 : state, st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall Heval_if : st =[ if b then c1 else c2 end ]=> st2, forall H4 : beval st b = true, forall H5 : st =[ c1 ]=> st2, false = false ->
st =[ c2 ]=> st2 ->
beval st b = true -> st =[ c1 ]=> st2 -> st' = st2.

Proof.
(* We know from HbFalse that beval st b = false, which contradicts H4 which assumes it's true.
Therefore, we can derive the contradiction and solve the goal.
*)
  intros st st' b c1 c2 HbFalse Heval_c2 HI st2 Heval_if H4 H5.
rewrite HbFalse in H4.
discriminate H4.
Qed.

Lemma if_false_eval_c2_unique_state_5 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall HbFalse : beval st b = false, forall Heval_c2 : st =[ c2 ]=> st', forall HI : forall st2 : state, st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall Heval_if : st =[ if b then c1 else c2 end ]=> st2, forall H4 : beval st b = false, forall H5 : st =[ c2 ]=> st2, false = false ->
st =[ c2 ]=> st2 ->
beval st b = true -> st =[ c1 ]=> st2 -> st' = st2.

Proof.
intros st st' b c1 c2 HbFalse Heval_c2 HI st2 Heval_if H4 H5.
intros _.
(* The assumption "false = false" is trivially true, we can dismiss it.
*)
  intro Heval_c2_other.
(* Assume another evaluation of c2 leading to st2 *)
  intro HbTrue.
(* Assume b evaluates to true contradicting our earlier assumption *)
  intro Heval_c1.
(* Assume an evaluation of c1 leading to st2 *)
  rewrite HbFalse in HbTrue.
(* This introduces a contradiction because b cannot be both true and false *)
  discriminate HbTrue.
(* We now have derived a contradiction from assuming both evaluations could coexist *)

Qed.

Lemma if_false_evaluates_else_branch_3 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = false, forall E1 : st =[ c2 ]=> st', forall IHE1 : forall st2 : state,
st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall E2 : st =[ if b then c1 else c2 end ]=> st2, forall H5 : false = false, forall H6 : st =[ c2 ]=> st2, forall H7 : beval st b = true, forall H8 : st =[ c1 ]=> st2, st' = st2.

Proof.
intros st st' b c1 c2 HbFalse Heval_c2 HI st2 Heval_if.
inversion Heval_if; subst.
- (* E_IfTrue: This case results in a contradiction because it assumes that 'b' evaluates to true *)
    apply (@if_bexp_false_eval_c2_unique_4 st st' b c1 c2 HbFalse Heval_c2 HI st2 Heval_if H4 H5).
- (* E_IfFalse: In this case, due to the hypothesis [HI] that
       execution of 'c2' is deterministic, we have that st2 must equal st' *)
    apply (@if_false_eval_c2_unique_state_5 st st' b c1 c2 HbFalse Heval_c2 HI st2 Heval_if H4 H5).
Qed.

Lemma if_false_consequence_equal_state_2 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = false, forall E1 : st =[ c2 ]=> st', forall IHE1 : forall st2 : state,
st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall E2 : st =[ if b then c1 else c2 end ]=> st2, forall H5 : beval st b = false, forall H6 : st =[ c2 ]=> st2, st' = st2.

Proof.
(* We have the hypothesis E2: st =[ if b then c1 else c2 end ]=> st2, which
     means that the execution of the if-then-else construct where the condition
     b is evaluated in the state st leading to st2.
Since the condition is
     false, the else branch should be taken.
*)
  intros.
inversion E2; subst.
- (* The first case is if the condition evaluates to true, which contradicts
       our assumption H: beval st b = false.
So, it suffices to derive a
       contradiction.
*)
    rewrite H in H5.
apply (@if_false_evaluates_else_branch_3 st st' b c1 c2 H E1 IHE1 st2 E2 H5 H6 H7 H8).
- (* The second case is when the condition evaluates to false.
Here, we have
       an execution of c2 leading to st2.
*)
    apply IHE1.
assumption.
Qed.

Lemma while_false_leads_to_no_state_change_3 : forall b : bexp, forall st : state, forall c : com, forall H : beval st b = false, forall st2 : state, forall E2 : st =[ while b do c end ]=> st2, forall st' : state, forall H2 : beval st b = true, forall H3 : st =[ c ]=> st', forall H6 : st' =[ while b do c end ]=> st2, st = st2.

Proof.
(* The proof strategy is to leverage the evaluation rule E_WhileFalse, which states that if the conditional
     bexp b evaluates to false in state st, then the while command results in the same state st without change.
Since the beval st b = false and st =[ while b do c end ]=> st2, it follows directly that st2 must be st
     by E_WhileFalse, which allows us to conclude st = st2.
*)
  intros b st c H st2 E2 st' H2 H3 H6.
inversion E2.
- (* Case where the while loop does not execute because the condition is false *)
    reflexivity.
- (* Case where the while loop would execute does not apply because we are given beval st b = false *)
    rewrite H in H4.
discriminate H4.
Qed.

Theorem ceval_deterministic''' : forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.

Proof.
(* Since evaluation of a command 'c' for a given state 'st' is deterministic, we should be *)
  (* able to prove that two evaluations of the same command in the same state lead to identical results.
*)
  (* Hence, we prove this by induction on the evaluation of the first command.
*)

  intros c st st1 st2 E1 E2.
generalize dependent st2.
(* We perform induction on the evidence 'E1' that [ st =[ c ]=> st1 ].
*)
  induction E1; intros; inversion E2; subst; try reflexivity.
- (* E_Seq : we must show that both parts of the sequence evaluate to the same ending states *)
    assert (st' = st'0) as EQ1.
{ apply IHE1_1; assumption.
}
    subst st'0.
apply IHE1_2; assumption.
- (* E_IfTrue : we must show that the true branch leads to the same state *)
    apply IHE1; assumption.
- (* E_IfFalse : we must show that the false branch leads to the same state *)
    apply (@if_true_deterministic_execution_0 st st' b c1 c2 H E1 IHE1 st2 E2 H5 H6).
- (* E_WhileFalse : the loop does not run, so the state remains as is *)
    apply (@if_false_consequence_equal_state_1 st st' b c1 c2 H E1 IHE1 st2 E2 H5 H6).
- (* E_WhileTrue : both runs take the loop, hence the post-loop states must be the same *)
    apply (@if_false_consequence_equal_state_2 st st' b c1 c2 H E1 IHE1 st2 E2 H5 H6).
- (* E_WhileTrue : both runs take the loop, hence the post-loop states must be the same *)
    apply (@while_false_leads_to_no_state_change_3 b st c H st2 E2 st' H2 H3 H6).
Qed.
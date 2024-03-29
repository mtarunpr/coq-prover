

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



Lemma if_true_deterministic_execution_0 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = true, forall E1 : st =[ c1 ]=> st', forall IHE1 : forall st2 : state,
st =[ c1 ]=> st2 -> st' = st2, forall st2 : state, forall E2 : st =[ if b then c1 else c2 end ]=> st2, forall H5 : beval st b = false, forall H6 : st =[ c2 ]=> st2, st' = st2.

Proof.
(* Given that beval st b = true, we can directly use E_IfTrue to establish the link between st and st' through c1 *)
  intros st st' b c1 c2 H E1 IHE1 st2 E2 H5 H6.
(* Now, we have a contradiction because beval st b cannot be both true and false *)
  rewrite H in H5.
discriminate H5.
Qed.

Lemma if_false_consequence_equal_state_1 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = false, forall E1 : st =[ c2 ]=> st', forall IHE1 : forall st2 : state,
st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall E2 : st =[ if b then c1 else c2 end ]=> st2, forall H5 : beval st b = true, forall H6 : st =[ c1 ]=> st2, st' = st2.

Proof.
intros st st' b c1 c2 Hfalse E2 IH st2 Eif Htrue Ec1.
(* Since `beval st b` cannot be both true and false simultaneously, we have a contradiction.
*)
  rewrite Htrue in Hfalse.
discriminate Hfalse.
Qed.

Lemma execution_if_false_same_end_state_2 : forall st st' : state, forall b : bexp, forall c1 c2 : com, forall H : beval st b = false, forall E1 : st =[ c2 ]=> st', forall IHE1 : forall st2 : state,
st =[ c2 ]=> st2 -> st' = st2, forall st2 : state, forall E2 : st =[ if b then c1 else c2 end ]=> st2, forall H5 : beval st b = beval st b, forall H6 : st =[ c2 ]=> st2, st' = st2.

Proof.
(* Given that the evaluation of b is false (H) and execution of c2 leads to st' (E1),
     we want to prove that the if statement will also lead to st' when the else branch is taken,
     which corresponds to executing c2.
*)
  intros st st' b c1 c2 H E1 IHE1 st2 E2 H5 H6.
(* By using the assumption that the evaluation of b is false (H),
     we can consider the rule for if false in our operational semantics *)
  inversion E2; subst.
- (* If the evaluation of b in the if statement is true (which cannot be due to H), 
       we get a contradiction.
Hence this case is impossible.
*)
    rewrite H in H7.
discriminate.
- (* If the evaluation of b in the if statement is false, (which is as in E1 & H),
       and the else branch leads to st2, then by determinism (represented by IHE1 called with H6),
       we get that st' (from E1) is equal to st2.
*)
    apply IHE1.
assumption.
Qed.

Theorem ceval_deterministic'' : forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.

Proof.
(* We will prove the determinism of "ceval" by induction on the evaluation of command "c" *)
  intros c st st1 st2 E1 E2.
generalize dependent st2.
(* Perform induction on the first evaluation derivation.
*)
  induction E1; intros; inversion E2; subst;
  try reflexivity;
  try (rewrite <- H in H5; inversion H5);
  try (rewrite <- H in H2; inversion H2);
  try (rewrite <- H in H4; inversion H4).
- (* E_Seq, sequential composition *)
    assert (st' = st'0) as EQ1.
{ apply IHE1_1; assumption.
} 
    subst st'0.
apply IHE1_2; assumption.
- (* E_IfTrue *)
    apply IHE1; assumption.
- (* E_IfFalse | b evaluates to false *)
    apply (@if_true_deterministic_execution_0 st st' b c1 c2 H E1 IHE1 st2 E2 H5 H6).
- (* E_WhileFalse | b evaluates to false *)
    apply (@if_false_consequence_equal_state_1 st st' b c1 c2 H E1 IHE1 st2 E2 H5 H6).
- (* E_WhileTrue | b evaluates to true and runs once *)
    apply (@execution_if_false_same_end_state_2 st st' b c1 c2 H E1 IHE1 st2 E2 H5 H6).
- (* E_WhileTrue | b evaluates to true and loops *)
    clear IHE1_2.
apply IHE1_1 in H3.
subst st'0.
apply IHE1_2; assumption.
Qed.
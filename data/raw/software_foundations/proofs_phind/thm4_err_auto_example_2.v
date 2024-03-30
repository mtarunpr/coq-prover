

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

Proof.
(* We will proceed by induction on the constructors of the implications.
*)
  intros P Q R S T U H1 H2 H3 H4 H5 H6 H7.
(* H1 : P -> Q, H2 : P -> R, H3 : T -> R, H4 : S -> T -> U, H5 : (P -> Q) -> (P -> S), H6 : T, H7 : P *)
  (* First, we will use H5 to derive H8 : P -> S *)
  apply H5 in H7.
(* Now, we have H8 : P -> S and H7 : P, so we can derive H9 : S *)
  apply H7 in H8.
(* Now, we will use H4 to derive H10 : T -> U *)
  apply H4 in H9.
(* Now, we have H10 : T -> U and H6 : T, so we can derive H11 : U *)
  apply H6 in H10.
(* Now, we will use H1 and H7 to derive H12 : Q *)
  apply H1 in H7.
(* Now, we will use H2 and H7 to derive H13 : R *)
  apply H2 in H7.
(* Now, we will use H3 and H6 to derive H14 : R *)
  apply H3 in H6.
(* Now, we have H12 : Q, H13 : R, and H14 : R, so we can use the transitivity of implication to derive H15 : Q -> R *)
  apply Imp_trans in H12.
(* Now, we have H15 : Q -> R and H13 : R, so we can derive H16 : Q *)
  apply H15 in H13.
(* Now, we have H16 : Q and H14 : R, so we can use the transitivity of implication to derive H17 : Q -> R *)
  apply Imp_trans in H16.
(* Now, we have H17 : Q -> R and H14 : R, so
Qed.
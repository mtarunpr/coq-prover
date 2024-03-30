

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






Lemma composition_of_functions_0 : forall P Q R S T U : Prop, forall H : P -> Q, forall H0 : Q -> R, forall H1 : R -> S, forall H2 : S -> T, forall H3 : T -> U, forall H4 : P, U.

Proof.
(* The goal is to prove U.
We have the following functions:
     - H : P -> Q
     - H0 : Q -> R
     - H1 : R -> S
     - H2 : S -> T
     - H3 : T -> U
     - H4 : P
     We need to construct a term of type U using these functions.
We can apply H to H4 to get a term of type Q.
Then we can apply H0 to this term to get a term of type R.
We can then apply H1 to this term to get a term of type S.
Finally, we can apply H3 to this term to get a term of type U.
*)
  intros P Q R S T U H H0 H1 H2 H3 H4.
apply H3.
apply H2.
apply H1.
apply H0.
apply H.
apply H4.
Qed.

Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.




Proof.
(*
     We will proceed by induction on the number of implications.
Base case: P -> Q, Q -> R, R -> S, S -> T, T -> U, P -> U.
Inductive step: If we know P -> Q, Q -> R, R -> S, S -> T, T -> U, and P -> U,
     then we can deduce U.
*)
  
intros.
(*
     We will use the following lemma:
     forall P Q R, (P -> Q) -> (P -> R) -> P -> Q,
     which states that if we have a proof of P -> Q and a proof of P -> R, then we can deduce Q.
This lemma is a special case of the transitivity of implication.
*)
  
apply (@composition_of_functions_0 P Q R S T U H H0 H1 H2 H3 H4).
Qed.
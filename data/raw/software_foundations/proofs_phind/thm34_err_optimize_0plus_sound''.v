





Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.









Module AExp.



Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).












Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus  a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult  a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.



Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => (aeval a1) =? (aeval a2)
  | BNeq a1 a2  => negb ((aeval a1) =? (aeval a2))
  | BLe a1 a2   => (aeval a1) <=? (aeval a2)
  | BGt a1 a2   => negb ((aeval a1) <=? (aeval a2))
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.






Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.



Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.



Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  -  reflexivity.
  -  destruct a1 eqn:Ea1.
    +  destruct n eqn:En.
      *   simpl. apply IHa2.
      *  simpl. rewrite IHa2. reflexivity.
    + 
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + 
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + 
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - 
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - 
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.
















Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof.
    try reflexivity. 
Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. 
  apply HP. 
Qed.










Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    
    -  simpl. reflexivity.
    -  simpl. reflexivity.
Qed.



Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  
  destruct n;
  
  simpl;
  
  reflexivity.
Qed.



Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    
  -  reflexivity.
  - 
    destruct a1 eqn:Ea1;
      
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    
    +  destruct n eqn:En;
      simpl; rewrite IHa2; reflexivity.   Qed.







Theorem optimize_0plus_sound'' : forall a,
  aeval (optimize_0plus a) = aeval a.

Proof.
(* We will proceed by induction on the structure of aexp.
*)
  intros a.
induction a as [| a1 a2 | a1 a2 | a1 a2].
(* In each case, we will simplify the goal by applying the induction hypothesis.
*)
  - (* Case ANum *)
    reflexivity.
- (* Case APlus *)
    simpl.
(* We need to show that aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).
*)
    (* By the induction hypothesis, we know that aeval (optimize_0plus a1) = aeval a1 and aeval (optimize_0plus a2) = aeval a2.
*)
    (* Therefore, we have aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus (optimize_0plus a1) (optimize_0plus a2)) by the definition of optimize_0plus.
*)
    (* And we have aeval (APlus a1 a2) = aeval (APlus (optimize_0plus a1) (optimize_0plus a2)) by the definition of aeval.
*)
    (* Therefore, aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).
*)
    reflexivity.
- (* Case AMinus *)
    simpl.
(* We need to show that aeval (optimize_0plus (AMinus a1 a2)) = aeval (AMinus a1 a2).
*)
    (* By the induction hypothesis, we know that aeval (optimize_0plus a1) = aeval a1 and aeval (optimize_0plus a2) = aeval a2.
*)
    (* Therefore, we have aeval (optimize_0plus (AMinus a1 a2)) = aeval (AMinus (optimize_0plus a1) (optimize_0plus a2)) by the definition of optimize_0plus.
*)
    (* And we have aeval (AMinus a1 a2) = aeval (AMinus (optimize_0plus
Qed.
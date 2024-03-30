





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





Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    
    try reflexivity.
  
  - 
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    +  destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.











Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.



Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.



Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.
  
  
Admitted.





Fixpoint optimize_0plus_b (b : bexp) : bexp
  :=
  match b with
  | BTrue       => BTrue
  | BFalse      => BFalse
  | BEq a1 a2   => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BNeq a1 a2  => BNeq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2   => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BGt a1 a2   => BGt (optimize_0plus a1) (optimize_0plus a2)
  | other       => other
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros b.
  destruct b;
  try (simpl; repeat (rewrite optimize_0plus_sound); reflexivity).
Qed.




Fixpoint optimize (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus e1 e2 =>
      match optimize e1 with
      | ANum 0 => optimize e2
      | e1 =>
          match optimize e2 with
          | ANum 0 => e1
          | e2 => APlus e1 e2
          end
      end
  | AMinus e1 e2 =>
      match optimize e1 with
      | ANum 0 => ANum 0
      | e1 =>
          match optimize e2 with
          | ANum 0 => e1
          | e2 => AMinus e1 e2
          end
      end
  | AMult e1 e2 =>
      match optimize e1 with
      | ANum 0 => ANum 0
      | ANum 1 => optimize e2
      | e1 =>
          match optimize e2 with
          | ANum 0 => ANum 0
          | ANum 1 => e1
          | e2 => AMult e1 e2
          end
      end
  end.

Theorem optimize_sound : forall a,
  aeval (optimize a) = aeval a.
Proof.
  intros a.
  induction a.
  - reflexivity.
  - simpl. rewrite <- IHa1. rewrite <- IHa2. destruct (optimize a1);
    try (destruct (optimize a2); [destruct n; [rewrite add_0_r; reflexivity | reflexivity] | reflexivity | reflexivity | reflexivity]).
    + destruct n.
      * reflexivity.
      * destruct (optimize a2).
        ** destruct n0. rewrite add_0_r. reflexivity. reflexivity.
        ** reflexivity.
        ** reflexivity.
        ** reflexivity.
  - simpl. rewrite <- IHa1. rewrite <- IHa2. destruct (optimize a1);
    try (destruct (optimize a2); [destruct n; [rewrite sub_0_r; reflexivity | reflexivity] | reflexivity | reflexivity | reflexivity]).
    + destruct n.
      * reflexivity.
      * destruct (optimize a2).
        ** destruct n0. reflexivity. reflexivity.
        ** reflexivity.
        ** reflexivity.
        ** reflexivity.
  - simpl. rewrite <- IHa1. rewrite <- IHa2. destruct (optimize a1);
    try (destruct (optimize a2); [destruct n; [rewrite mul_0_r; reflexivity | destruct n; [rewrite mul_1_r; reflexivity | reflexivity]] | reflexivity | reflexivity | reflexivity]).
    + destruct n.
      * reflexivity.
      * destruct n.
        ** simpl. rewrite add_0_r. reflexivity.
        ** destruct (optimize a2).
          *** destruct n0. rewrite mul_0_r. reflexivity. destruct n0. rewrite mul_1_r. reflexivity. reflexivity.
          *** reflexivity.
          *** reflexivity.
          *** reflexivity.
Qed.






Ltac invert H := inversion H; subst; clear H.



Lemma invert_example1: forall {a b c: nat}, [a ;b] = [a;c] -> b = c.
  intros.
  invert H.
  reflexivity.
Qed.








Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.

Proof.
intros m n o p H1 H2.
rewrite H2 in H1.
destruct (le_plus_l H1) as [H3 | H4].
- apply H3.
- apply le_plus_r in H4.
apply H4.
Qed.
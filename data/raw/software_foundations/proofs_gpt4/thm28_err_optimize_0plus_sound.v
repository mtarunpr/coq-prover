





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





Lemma optimize_0plus_aexp_addition_preservation_0 : forall n : nat, forall a2 : aexp, forall IHa1 : aeval (optimize_0plus (ANum (S n))) =
aeval (ANum (S n)), forall IHa2 : aeval (optimize_0plus a2) = aeval a2, S (n + aeval (optimize_0plus a2)) = S (n + aeval a2).

Proof.
(* The variables 'n', 'a2', 'IHa1' and 'IHa2' are given.
We introduce them for use in the proof.
*)
  intros n a2 IHa1 IHa2.
(* By assumption 'IHa2', 'aeval (optimize_0plus a2)' is equal to 'aeval a2'.
We can replace 'aeval (optimize_0plus a2)' by 'aeval a2' in the goal.
*)
  rewrite IHa2.
(* What remains to be shown is that S (n + aeval a2) is equal to itself, which is trivial by reflexivity of equality.
*)
  reflexivity.
Qed.

Theorem optimize_0plus_sound : forall a,
  aeval (optimize_0plus a) = aeval a.

Proof.
(* We perform induction on the structure of the arithmetic expression a.
*)
  intros a.
induction a.
- (* Case: a = ANum n; the result is immediate because optimize_0plus has no effect.
*)
    simpl.
reflexivity.
- (* Case: a = APlus a1 a2; we need to consider subcases on a1 being ANum 0 or not.
*)
    simpl.
destruct a1.
+ (* Subcase: a1 is ANum n; consider if n is zero.
*)
      destruct n.
* (* Subcase: n=0; apply the induction hypothesis on a2.
*)
        apply IHa2.
* (* Subcase: n<>0; both sides of the equation are the same after optimization.
*)
        simpl.
apply (@optimize_0plus_aexp_addition_preservation_0 n a2 IHa1 IHa2).
+ (* Subcase: a1 is APlus; apply the induction hypothesis.
*)
      simpl.
rewrite IHa1.
rewrite IHa2.
reflexivity.
+ (* Subcase: a1 is AMinus; apply the induction hypothesis.
*)
      simpl.
rewrite IHa1.
rewrite IHa2.
reflexivity.
+ (* Subcase: a1 is AMult; apply the induction hypothesis.
*)
      simpl.
rewrite IHa1.
rewrite IHa2.
reflexivity.
- (* Case: a = AMinus a1 a2; apply the induction hypothesis on a1 and a2.
*)
    simpl.
rewrite IHa1.
rewrite IHa2.
reflexivity.
- (* Case: a = AMult a1 a2; apply the induction hypothesis on a1 and a2.
*)
    simpl.
rewrite IHa1.
rewrite IHa2.
reflexivity.
Qed.
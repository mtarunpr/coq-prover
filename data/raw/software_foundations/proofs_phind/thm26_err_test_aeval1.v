





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



Example test_aeval1 : aeval (APlus (ANum 2) (ANum 2)) = 4.

Proof.
(* We will use the induction principle for aexp to prove the theorem.
*)
  induction (APlus (ANum 2) (ANum 2)) as [|a1 a2 a1' a2' IH1 IH2].
(* Base case: ANum *)
  - simpl.
reflexivity.
(* Inductive case: APlus *)
  - simpl.
rewrite IH1, IH2.
reflexivity.
(* Inductive case: AMinus *)
  - simpl.
rewrite IH1, IH2.
reflexivity.
(* Inductive case: AMult *)
  - simpl.
rewrite IH1, IH2.
reflexivity.
Qed.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.

Inductive expr : Type :=
  | EVariable : string -> expr
  | EConstant : nat -> expr
  | EPlus : expr -> expr -> expr.

Definition env := string -> nat.

Fixpoint eval (e : expr) (env : env) : nat :=
  match e with
  | EVariable x => env x
  | EConstant n => n
  | EPlus e1 e2 => eval e1 env + eval e2 env
  end.

Fixpoint optimize (e : expr) : expr :=
  match e with
  | EVariable x => EVariable x
  | EConstant n => EConstant n
  | EPlus e1 e2 =>
      match (optimize e1, optimize e2) with
      | (EConstant 0, e2') => e2'
      | (e1', EConstant 0) => e1'
      | (e1', e2') => EPlus e1' e2'
      end
  end.

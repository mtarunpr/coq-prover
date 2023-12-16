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

Lemma eval_optimized_expr_addition_zero_0 : forall env0 : env, forall e1 e2 : expr, forall IHe1 : eval (optimize e1) env0 = eval e1 env0, forall IHe2 : eval (optimize e2) env0 = eval e2 env0, eval
  match optimize e1 with
  | EConstant 0 => optimize e2
  | _ =>
      match optimize e2 with
      | EConstant 0 => optimize e1
      | _ => EPlus (optimize e1) (optimize e2)
      end
  end env0 = eval e1 env0 + eval e2 env0.
 e2)
      end
  end env0 = eval e1 env0 + eval e2 env0.
Proof.
  intros.
  hammer.
Qed.


Theorem optimize_preserves_semantics : forall (env : env) (e : expr),
    eval (optimize e) env = eval e env.


Proof.


  (* We prove this theorem by induction on the expression `e`. *)
  induction e; simpl.

  (* Three cases arise based on the inductive definition of `expr`.
     1. The case when e is a variable:
        - The optimization doesn't change a variable, so the semantics are the same. *)
  - reflexivity.

  (* 2. The case when e is a constant:
       - The optimization doesn't change a constant, so the semantics are the same. *)
  - reflexivity.

  (* 3. The case when e is a sum of two expressions:
       - We need to consider the optimization result on both sub-expressions and apply the inductive hypothesis. *)
  - apply (@eval_optimized_expr_addition_zero_0 env0 e1 e2 IHe1 IHe2).

Qed.
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

Lemma helper_lemma_0 : forall env : Top.env, forall e1 e2 : expr, forall s : string, forall Heqe1_opt : EVariable s = optimize e1, forall IH1 : eval (EVariable s) env = eval e1 env, forall s0 : string, forall Heqe2_opt : EVariable s0 = optimize e2, forall IH2 : eval (EVariable s0) env = eval e2 env, eval (EPlus (EVariable s) (EVariable s0)) env =
eval e1 env + eval e2 env.

Proof.

  intros env e1 e2 s Heqe1_opt IH1 s0 Heqe2_opt IH2.
  (* Rewrite both sides using IH1 and IH2 which equates eval (EVariable _) with eval e1 and eval e2 respectively *)
  rewrite <- IH1.
  rewrite <- IH2.
  (* Now both sides of the equation are the same *)
  reflexivity.

Qed.
Lemma helper_lemma_1 : forall env : Top.env, forall e1 e2 : expr, forall s : string, forall Heqe1_opt : EVariable s = optimize e1, forall IH1 : eval (EVariable s) env = eval e1 env, forall n : nat, forall Heqe2_opt : EConstant n = optimize e2, forall IH2 : eval (EConstant n) env = eval e2 env, eval
  match n with
  | 0 => EVariable s
  | S _ => EPlus (EVariable s) (EConstant n)
  end env = eval e1 env + eval e2 env.

Proof.

  intros env e1 e2 s Heqe1_opt IH1 n Heqe2_opt IH2.
  (* Perform case analysis on n (n is either 0 or not) *)
  destruct n.
  - (* Case for n = 0 *)
    simpl. (* Simplify the match construction *)
    rewrite <- IH1. (* Use IH1 to relate eval (EVariable s) with eval e1 *)
    rewrite <- IH2. (* Use IH2 to relate eval (EConstant 0) with eval e2 *)
    (* eval (EConstant 0) is 0, so we can simplify the sum *)
    rewrite <- plus_n_O.
    reflexivity.
  - (* Case for n = S n' where n' is some natural number *)
    simpl. (* Simplify the match construction *)
    rewrite <- IH1. (* Use IH1 to relate eval (EVariable s) with eval e1 *)
    rewrite <- IH2. (* Use IH2 to relate eval (EConstant (S n)) with eval e2 *)
    reflexivity.

Qed.
Lemma helper_lemma_2 : forall env : Top.env, forall e1 e2 : expr, forall s : string, forall Heqe1_opt : EVariable s = optimize e1, forall IH1 : eval (EVariable s) env = eval e1 env, forall e2_opt1 e2_opt2 : expr, forall Heqe2_opt : EPlus e2_opt1 e2_opt2 = optimize e2, forall IH2 : eval (EPlus e2_opt1 e2_opt2) env = eval e2 env, eval (EPlus (EVariable s) (EPlus e2_opt1 e2_opt2)) env =
eval e1 env + eval e2 env.

Proof.

  intros env e1 e2 s Heqe1_opt IH1 e2_opt1 e2_opt2 Heqe2_opt IH2.
  (* Rewrite the evaluation of e1 followed by rewriting Heqe1_opt to connect it to the optimized expression *)
  rewrite <- IH1.
  (* Rewrite the evaluation of e2 followed by rewriting Heqe2_opt to connect it to the optimized expression *)
  rewrite <- IH2.
  (* No need for associativity rewrite, both sides already match after applying the hypotheses *)
  reflexivity.

Qed.
Lemma helper_lemma_3 : forall env : Top.env, forall e1 e2 : expr, forall n : nat, forall Heqe1_opt : EConstant n = optimize e1, forall IH1 : eval (EConstant n) env = eval e1 env, forall s : string, forall Heqe2_opt : EVariable s = optimize e2, forall IH2 : eval (EVariable s) env = eval e2 env, eval
  match n with
  | 0 => EVariable s
  | S _ => EPlus (EConstant n) (EVariable s)
  end env = eval e1 env + eval e2 env.

Proof.

  intros env e1 e2 n Heqe1_opt IH1 s Heqe2_opt IH2.
  destruct n.
  - simpl.   (* Case for n = 0 *)
    rewrite <- IH2. (* Apply the induction hypothesis for e2 *)
    rewrite <- IH1. (* Apply the induction hypothesis for e1 *)
    rewrite plus_0_l.  (* Simplify 0 + x to x *)
    reflexivity.
  - simpl.   (* Case for n = S _ *)
    rewrite <- IH1.  (* Apply the induction hypothesis for e1 *)
    rewrite <- IH2.  (* Apply the induction hypothesis for e2 *)
    reflexivity.

Qed.
Lemma helper_lemma_4 : forall env : Top.env, forall e1 e2 : expr, forall n : nat, forall Heqe1_opt : EConstant n = optimize e1, forall IH1 : eval (EConstant n) env = eval e1 env, forall n0 : nat, forall Heqe2_opt : EConstant n0 = optimize e2, forall IH2 : eval (EConstant n0) env = eval e2 env, eval
  match n with
  | 0 => EConstant n0
  | S _ =>
      match n0 with
      | 0 => EConstant n
      | S _ => EPlus (EConstant n) (EConstant n0)
      end
  end env = eval e1 env + eval e2 env.

Proof.


  intros env e1 e2 n Heqe1_opt IH1 n0 Heqe2_opt IH2.
  (* Perform case analysis on both n and n0 *)
  destruct n, n0.
  - (* Case for n = 0 and n0 = 0 *)
    simpl. (* Simplify the match construction *)
    rewrite <- IH1. (* Use IH1 to relate eval (EConstant 0) with eval e1 *)
    rewrite <- IH2. (* Use IH2 to relate eval (EConstant 0) with eval e2 *)
    (* Both eval e1 and eval e2 are 0, so 0 + 0 = 0 *)
    reflexivity.
  - (* Case for n = 0 and n0 = S n0' *)
    simpl. (* Simplify the match construction *)
    rewrite <- IH1. (* Use IH1 to relate eval (EConstant 0) with eval e1 *)
    rewrite <- IH2. (* Use IH2 to relate eval (EConstant (S n0')) with eval e2 *)
    (* eval (EConstant 0) is 0, so we can simplify 0 + x to x *)
    rewrite plus_0_l.
    reflexivity.
  - (* Case for n = S n' and n0 = 0 *)
    simpl. (* Simplify the match construction *)
    rewrite <- IH1. (* Use IH1 to relate eval (EConstant (S n')) with eval e1 *)
    rewrite <- IH2. (* Use IH2 to relate eval (EConstant 0) with eval e2 *)
    (* eval (EConstant 0) is 0, so we can simplify x + 0 to x *)
    rewrite plus_0_r.
    reflexivity.
  - (* Case for n = S n' and n0 = S n0' *)
    simpl. (* Simplify the match construction *)
    rewrite <- IH1. (* Use IH1 to relate eval (EConstant (S n')) with eval e1 *)
    rewrite <- IH2. (* Use IH2 to relate eval (EConstant (S n0')) with eval e2 *)
    reflexivity.


Qed.
Lemma helper_lemma_5 : forall env : Top.env, forall e1 e2 : expr, forall n : nat, forall Heqe1_opt : EConstant n = optimize e1, forall IH1 : eval (EConstant n) env = eval e1 env, forall e2_opt1 e2_opt2 : expr, forall Heqe2_opt : EPlus e2_opt1 e2_opt2 = optimize e2, forall IH2 : eval (EPlus e2_opt1 e2_opt2) env = eval e2 env, eval
  match n with
  | 0 => EPlus e2_opt1 e2_opt2
  | S _ => EPlus (EConstant n) (EPlus e2_opt1 e2_opt2)
  end env = eval e1 env + eval e2 env.

Proof.


  intros env e1 e2 n Heqe1_opt IH1 e2_opt1 e2_opt2 Heqe2_opt IH2.
  (* Perform case analysis on n *)
  destruct n.
  - (* Case for n = 0 *)
    simpl. (* Simplify the match construction *)
    rewrite <- IH2. (* Use IH2 to rewrite eval e2 env as eval (EPlus e2_opt1 e2_opt2) env *)
    rewrite <- IH1. (* Use IH1 to rewrite eval e1 env as eval (EConstant 0) env *)
    simpl. (* Simplify eval (EConstant 0) env to 0 *)
    reflexivity. (* The goal follows directly after simplification *)
  - (* Case for n = S _ *)
    simpl. (* Simplify the match construction *)
    rewrite <- IH1. (* Use IH1 to rewrite eval e1 env as eval (EConstant (S n)) env *)
    rewrite <- IH2. (* Use IH2 to rewrite eval e2 env as eval (EPlus e2_opt1 e2_opt2) env *)
    simpl. (* Simplify eval (EConstant (S n)) env to (S n) *)
    reflexivity. (* Direct equality after simplification *)


Qed.
Lemma helper_lemma_6 : forall env : Top.env, forall e1 e2 e1_opt1 e1_opt2 : expr, forall Heqe1_opt : EPlus e1_opt1 e1_opt2 = optimize e1, forall IH1 : eval (EPlus e1_opt1 e1_opt2) env = eval e1 env, forall s : string, forall Heqe2_opt : EVariable s = optimize e2, forall IH2 : eval (EVariable s) env = eval e2 env, eval (EPlus (EPlus e1_opt1 e1_opt2) (EVariable s)) env =
eval e1 env + eval e2 env.

Proof.


  intros env e1 e2 e1_opt1 e1_opt2 Heqe1_opt IH1 s Heqe2_opt IH2.
  (* Rewrite eval e1 using Heqe1_opt and IH1 *)
  rewrite <- IH1.
  (* Do the same for eval e2 using Heqe2_opt and IH2 *)
  rewrite <- IH2.
  (* We now have eval (EPlus e1_opt1 e1_opt2) env + eval (EVariable s) env on both sides, which are obviously equal *)
  reflexivity.


Qed.
Lemma helper_lemma_7 : forall env : Top.env, forall e1 e2 e1_opt1 e1_opt2 : expr, forall Heqe1_opt : EPlus e1_opt1 e1_opt2 = optimize e1, forall IH1 : eval (EPlus e1_opt1 e1_opt2) env = eval e1 env, forall n : nat, forall Heqe2_opt : EConstant n = optimize e2, forall IH2 : eval (EConstant n) env = eval e2 env, eval
  match n with
  | 0 => EPlus e1_opt1 e1_opt2
  | S _ => EPlus (EPlus e1_opt1 e1_opt2) (EConstant n)
  end env = eval e1 env + eval e2 env.

Proof.

  
  intros env e1 e2 e1_opt1 e1_opt2 Heqe1_opt IH1 n Heqe2_opt IH2.
  destruct n.
  - simpl. (* Case for n = 0 *)
    rewrite <- IH1. (* Use IH1 for eval e1 *)
    rewrite <- IH2. (* Use IH2 to simplify eval (EConstant 0) which is 0 *)
    rewrite plus_0_r. (* Simplify right-hand side adding 0 *)
    reflexivity.
  - simpl. (* Case for n = S _ *)
    rewrite <- IH1. (* Use IH1 for eval e1 *)
    rewrite <- IH2. (* Use IH2 for eval e2 *)
    reflexivity. (* Immediate reflexivity after using IH *)


Qed.
Lemma helper_lemma_8 : forall env : Top.env, forall e1 e2 e1_opt1 e1_opt2 : expr, forall Heqe1_opt : EPlus e1_opt1 e1_opt2 = optimize e1, forall IH1 : eval (EPlus e1_opt1 e1_opt2) env = eval e1 env, forall e2_opt1 e2_opt2 : expr, forall Heqe2_opt : EPlus e2_opt1 e2_opt2 = optimize e2, forall IH2 : eval (EPlus e2_opt1 e2_opt2) env = eval e2 env, eval
  (EPlus (EPlus e1_opt1 e1_opt2)
     (EPlus e2_opt1 e2_opt2)) env =
eval e1 env + eval e2 env.

Proof.


  intros env e1 e2 e1_opt1 e1_opt2 Heqe1_opt IH1 e2_opt1 e2_opt2 Heqe2_opt IH2.
  (* Use IH1 to rewrite eval (EPlus e1_opt1 e1_opt2) env as eval e1 env *)
  rewrite <- IH1.
  (* Use IH2 to rewrite eval (EPlus e2_opt1 e2_opt2) env as eval e2 env *)
  rewrite <- IH2.
  (* Now we have eval (EPlus e1_opt1 e1_opt2) env + eval (EPlus e2_opt1 e2_opt2) env
     on both sides, hence they are equal. *)
  reflexivity.

Qed.

Theorem optimize_preserves_semantics : forall (env : env) (e : expr),
    eval (optimize e) env = eval e env.


Proof.










  (* We proceed by induction on the expression e to prove that optimization preserves semantics. *)
  intros env e. induction e as [| n | e1 IH1 e2 IH2].
  
  - (* Case EVariable: optimization does not affect variables, so semantics is preserved. *)
    simpl. reflexivity.
  
  - (* Case EConstant: optimization does not affect constants, so semantics is preserved. *)
    simpl. reflexivity.

  - (* Case EPlus: we have to consider the result of optimizing the subexpressions e1 and e2. *)
    simpl. 
    remember (optimize e1) as e1_opt.
    remember (optimize e2) as e2_opt.
    destruct e1_opt; destruct e2_opt.
    
    + (* Subcase where both optimizations yield EVariable. *)
      apply (@helper_lemma_0 env e1 e2 s Heqe1_opt IH1 s0 Heqe2_opt IH2).
+ (* Subcase where e1_opt is a variable and e2_opt is a constant. *)
      apply (@helper_lemma_1 env e1 e2 s Heqe1_opt IH1 n Heqe2_opt IH2).
+ (* Subcase where e1_opt is a variable and e2_opt is a plus expression. *)
      apply (@helper_lemma_2 env e1 e2 s Heqe1_opt IH1 e2_opt1 e2_opt2 Heqe2_opt IH2).
+ (* Subcase where e1_opt is a constant and e2_opt is a variable. *)
      apply (@helper_lemma_3 env e1 e2 n Heqe1_opt IH1 s Heqe2_opt IH2).
+ (* Subcase where both optimizations yield EConstant. *)
      apply (@helper_lemma_4 env e1 e2 n Heqe1_opt IH1 n0 Heqe2_opt IH2).
+ (* Subcase where e1_opt is a constant and e2_opt is a plus expression. *)
      apply (@helper_lemma_5 env e1 e2 n Heqe1_opt IH1 e2_opt1 e2_opt2 Heqe2_opt IH2).
+ (* Subcase where e1_opt is a plus expression and e2_opt is a variable. *)
      apply (@helper_lemma_6 env e1 e2 e1_opt1 e1_opt2 Heqe1_opt IH1 s Heqe2_opt IH2).
+ (* Subcase where e1_opt is a plus expression and e2_opt is a constant. *)
      apply (@helper_lemma_7 env e1 e2 e1_opt1 e1_opt2 Heqe1_opt IH1 n Heqe2_opt IH2).
+ (* Final subcase where both e1_opt and e2_opt are plus expressions. *)
      apply (@helper_lemma_8 env e1 e2 e1_opt1 e1_opt2 Heqe1_opt IH1 e2_opt1 e2_opt2 Heqe2_opt IH2).

Qed.
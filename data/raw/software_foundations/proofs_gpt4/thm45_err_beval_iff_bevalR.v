





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
  intros. lia.
Qed.

Example add_comm__lia : forall m n,
    m + n = n + m.
Proof.
  intros. lia.
Qed.

Example add_assoc__lia : forall m n p,
    m + (n + p) = m + n + p.
Proof.
  intros. lia.
Qed.













Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module HypothesisNames.



Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).



End HypothesisNames.



Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.

End aevalR_first_try.



Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (APlus e1 e2)  ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) ->
      (e2 ==> n2) ->
      (AMult e1 e2)  ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.
















Definition manual_grade_for_beval_rules : option (nat*string) := None.







Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
 split.
 - 
   intros H.
   induction H; simpl.
   + 
     reflexivity.
   + 
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + 
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + 
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - 
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + 
     apply E_ANum.
   + 
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + 
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + 
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.



Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  
  split.
  - 
    intros H; induction H; subst; reflexivity.
  - 
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.



Reserved Notation "e '==>b' b" (at level 90, left associativity).
Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue : BTrue ==>b true
  | E_BFalse : BFalse ==>b false
  | E_BEq (e1 e2 : aexp) (n1 n2 : nat) (H1 : aevalR e1 n1) (H2 : aevalR e2 n2) : BEq e1 e2 ==>b n1 =? n2
  | E_BNeq (e1 e2 : aexp) (n1 n2 : nat) (H1 : aevalR e1 n1) (H2 : aevalR e2 n2) : BNeq e1 e2 ==>b negb (n1 =? n2)
  | E_BLe (e1 e2 : aexp) (n1 n2 : nat) (H1 : aevalR e1 n1) (H2 : aevalR e2 n2) : BLe e1 e2 ==>b n1 <=? n2
  | E_BGt (e1 e2 : aexp) (n1 n2 : nat) (H1 : aevalR e1 n1) (H2 : aevalR e2 n2) : BGt e1 e2 ==>b negb (n1 <=? n2)
  | E_BNot (e : bexp) (b : bool) (H : bevalR e b) : BNot e ==>b negb b
  | E_BAnd (e1 e2 : bexp) (b1 b2 : bool) (H1 : bevalR e1 b1) (H2 : bevalR e2 b2) : BAnd e1 e2 ==>b andb b1 b2
where "e '==>b' b" := (bevalR e b) : type_scope
.



Lemma aeval_equivalence_implies_nat_equality_2 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, (aeval e1 =? aeval e2) = (n1 =? n2).

Proof.
intros e1 e2 n1 n2 H1 H2.
(* Apply the theorem that connects 'aevalR' predicate with 'aeval' function on both hypotheses *)
  apply aeval_iff_aevalR in H1.
apply aeval_iff_aevalR in H2.
(* Two equalities from hypotheses H1 and H2 are rewritten *)
  rewrite <- H1; rewrite <- H2.
(* The goal is now tautological, since both sides of the equality are the same expression *)
  reflexivity.
Qed.

Lemma aeval_equivalence_implies_nat_equality_1 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, (aeval e1 =? aeval e2) = (n1 =? n2).

Proof.
(* Focus on proving that equivalence in the result of aeval implies equality in naturals *)
  intros e1 e2 n1 n2 H1 H2.
(* Apply the theorem aeval_iff_aevalR' which links aevalR and aeval *)
  apply (@aeval_equivalence_implies_nat_equality_2 e1 e2 n1 n2 H1 H2).
Qed.

Lemma aeval_equivalence_implies_nat_equality_0 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, (aeval e1 =? aeval e2) = (n1 =? n2).




Proof.
intros e1 e2 n1 n2 H1 H2.
(* Apply `aeval_iff_aevalR` lemma to replace `aeval e1` with `n1` and `aeval e2` with `n2` *)
  
apply (@aeval_equivalence_implies_nat_equality_1 e1 e2 n1 n2 H1 H2).
Qed.

Lemma aeval_negb_equality_lemma_2 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, negb (aeval e1 =? aeval e2) = negb (n1 =? n2).

Proof.
(* We introduce the expressions and corresponding natural numbers as well as the hypotheses *)
  intros e1 e2 n1 n2 H1 H2.
(* We use the provided lemma `aeval_equivalence_implies_nat_equality_0` *)
  assert (H_eq: (aeval e1 =? aeval e2) = (n1 =? n2)).
{
    apply aeval_equivalence_implies_nat_equality_0; assumption.
}
  (* Now we rewrite the negation of equality using our assertion `H_eq` *)
  rewrite H_eq.
reflexivity.
Qed.

Lemma aeval_negb_equality_lemma_1 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, negb (aeval e1 =? aeval e2) = negb (n1 =? n2).

Proof.
(* We make use of the lemma we have (aeval_equivalence_implies_nat_equality_0)
     to directly prove this lemma.
We apply this lemma with all the necessary arguments,
     and Coq's computation will finish the proof for us.
*)
  intros e1 e2 n1 n2 H1 H2.
apply (@aeval_negb_equality_lemma_2 e1 e2 n1 n2 H1 H2).
Qed.

Lemma aexp_evaluation_preserves_nat_leb_5 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, ((fix aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => aeval a1 + aeval a2
    | AMinus a1 a2 => aeval a1 - aeval a2
    | AMult a1 a2 => aeval a1 * aeval a2
    end) e1 <=?
 (fix aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => aeval a1 + aeval a2
    | AMinus a1 a2 => aeval a1 - aeval a2
    | AMult a1 a2 => aeval a1 * aeval a2
    end) e2) = (n1 <=? n2).

Proof.
intros e1 e2 n1 n2 H1 H2.
(* We use the equivalence of aeval and aevalR *)
  rewrite (aeval_iff_aevalR e1 n1) in H1.
rewrite (aeval_iff_aevalR e2 n2) in H2.
rewrite <- H1.
rewrite <- H2.
(* Now we can conclude by reflexivity since both sides of the equation are equal *)
  reflexivity.
Qed.

Lemma aeval_comparison_preservation_4 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, (aeval e1 <=? aeval e2) = (n1 <=? n2).

Proof.
(* We start by introducing all variables and hypotheses.
*)
  intros e1 e2 n1 n2 H1 H2.
(* We unfold the definition of aevalR to rewrite both sides of the equation with H1 and H2.
*)
  unfold aeval in *.
(* Use the fact that aevalR and aeval are equivalent to replace aeval with n1 and n2.
*)
  apply (@aexp_evaluation_preserves_nat_leb_5 e1 e2 n1 n2 H1 H2).
Qed.

Lemma aeval_comparison_preservation_3 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, (aeval e1 <=? aeval e2) = (n1 <=? n2).

Proof.
intros e1 e2 n1 n2 H1 H2.
apply (@aeval_comparison_preservation_4 e1 e2 n1 n2 H1 H2).
Qed.

Lemma aeval_comparison_preservation_2 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, (aeval e1 <=? aeval e2) = (n1 <=? n2).




Proof.
intros e1 e2 n1 n2 H1 H2.
(* We apply the theorem 'aeval_iff_aevalR', which states aeval and aevalR are equivalent.
*)
  
apply (@aeval_comparison_preservation_3 e1 e2 n1 n2 H1 H2).
Qed.

Lemma aeval_negb_leq_iff_8 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, negb (negb (aeval e1 <=? aeval e2)) =
negb (negb (n1 <=? n2)).

Proof.
(* We will use negation and comparison preservation lemma for our proof *)
  intros e1 e2 n1 n2 H1 H2.
(* We apply the lemma aeval_comparison_preservation_2 to relate aeval and nat comparison *)
  rewrite <- aeval_comparison_preservation_2 with (e1:=e1) (e2:=e2) (n1:=n1) (n2:=n2).
- (* The goal after simplification remains the same negation over negation, which is idempotent and can be simplified away *)
    reflexivity.
- (* Provide the hypotheses for the aeval_comparison_preservation_2 application *)
    exact H1.
- (* Provide the hypotheses for the aeval_comparison_preservation_2 application *)
    exact H2.
Qed.

Lemma aeval_negb_leq_iff_7 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, negb (negb (aeval e1 <=? aeval e2)) =
negb (negb (n1 <=? n2)).

Proof.
intros e1 e2 n1 n2 H1 H2.
(* Use the lemma 'aeval_comparison_preservation_2' to show the direct equivalence *)
  apply (@aeval_negb_leq_iff_8 e1 e2 n1 n2 H1 H2).
Qed.

Lemma aeval_negb_leq_iff_6 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, negb (negb (aeval e1 <=? aeval e2)) =
negb (negb (n1 <=? n2)).

Proof.
intros e1 e2 n1 n2 H1 H2.
(* Use the lemma that relates the `<=?` operation on `aeval e` and on `n`.
*)
  apply (@aeval_negb_leq_iff_7 e1 e2 n1 n2 H1 H2).
Qed.

Lemma aeval_negb_leq_iff_5 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, negb (negb (aeval e1 <=? aeval e2)) =
negb (negb (n1 <=? n2)).

Proof.
(* We introduce all variables into the context.
*)
  intros e1 e2 n1 n2 H1 H2.
(* We apply the previously proven lemma `aeval_comparison_preservation_2`, which equates the boolean result of comparing the evaluations of two arithmetic expressions with comparing their corresponding evaluation results.
This is justified because e1 evaluates to n1 and e2 to n2.
*)
  apply (@aeval_negb_leq_iff_6 e1 e2 n1 n2 H1 H2).
Qed.

Lemma aeval_compare_negation_lemma_4 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, negb (aeval e1 <=? aeval e2) = negb (n1 <=? n2).




Proof.
(* We introduce all the variables and hypotheses stated in the lemma *)
  
intros e1 e2 n1 n2 H1 H2.
(* We rewrite the goal using the leb_negb_inj lemma, which states that the boolean negation is injective with respect to the "less than or equal" comparison *)
  
rewrite <- negb_involutive with (b := (n1 <=? n2)).
rewrite <- negb_involutive with (b := (aeval e1 <=? aeval e2)).
f_equal.
(* Now, we can use the aeval_iff_aevalR' lemma which provides the bidirectional implication between aevalR and aeval *)
  (* Since we have H1: e1 ==> n1 and H2: e2 ==> n2, we can rewrite the aeval e1 and aeval e2 to be n1 and n2 respectively *)
  
apply (@aeval_negb_leq_iff_5 e1 e2 n1 n2 H1 H2).
Qed.

Lemma aeval_compare_negation_lemma_3 : forall e1 e2 : aexp, forall n1 n2 : nat, forall H1 : e1 ==> n1, forall H2 : e2 ==> n2, negb (aeval e1 <=? aeval e2) = negb (n1 <=? n2).

Proof.
intros e1 e2 n1 n2 H1 H2.
apply (@aeval_compare_negation_lemma_4 e1 e2 n1 n2 H1 H2).
Qed.

Lemma beval_iff_bevalR : forall b bv,
  b ==>b bv <-> beval b = bv.

Proof.
(* We split the proof into two directions: one for the forward implication
     and one for the backward implication, and we prove each separately.
*)
  split.
- (* Forward implication; we assume that b ⇒b bv and show beval b = bv.
*)
    intros H.
induction H.
+ (* Case for true boolean expression *)
      reflexivity.
+ (* Case for false boolean expression *)
      reflexivity.
+ (* Case for equality comparison *)
      simpl.
apply (@aeval_equivalence_implies_nat_equality_0 e1 e2 n1 n2 H1 H2).
+ (* Case for not-equal comparison *)
      simpl.
apply (@aeval_negb_equality_lemma_1 e1 e2 n1 n2 H1 H2).
+ (* Case for less-than-or-equal comparison *)
      simpl.
apply (@aeval_comparison_preservation_2 e1 e2 n1 n2 H1 H2).
+ (* Case for greater-than comparison *)
      simpl.
apply (@aeval_compare_negation_lemma_3 e1 e2 n1 n2 H1 H2).
+ (* Case for not operation *)
      simpl.
rewrite IHbevalR.
reflexivity.
+ (* Case for and operation *)
      simpl.
rewrite IHbevalR1.
rewrite IHbevalR2.
reflexivity.
- (* Backward implication; we assume beval b = bv and show b ⇒b bv.
*)
    generalize dependent bv.
induction b; intros; simpl in H; rewrite -> H; constructor.
+ (* Case for true boolean expression *)
      apply aeval_iff_aevalR.
reflexivity.
+ (* Case for false boolean expression *)
      apply aeval_iff_aevalR.
reflexivity.
+ (* Case for equality comparison *)
      apply aeval_iff_aevalR.
reflexivity.
apply aeval_iff_aevalR.
reflexivity.
+ (* Case for not-equal comparison *)
      apply aeval_iff_aevalR.
reflexivity.
apply aeval_iff_aevalR.
reflexivity.
+ (* Case for less-than-or-equal comparison *)
      apply aeval_iff_aevalR.
reflexivity.
apply aeval_iff_aevalR.
reflexivity.
+ (* Case for greater-than comparison *)
      apply aeval_iff_aevalR.
reflexivity.
apply aeval_iff_aevalR.
reflexivity.
+ (* Case for not operation *)
      apply IHb.
reflexivity.
+ (* Case for and operation *)
      apply IHb1.
reflexivity.
apply IHb2.
reflexivity.
Qed.
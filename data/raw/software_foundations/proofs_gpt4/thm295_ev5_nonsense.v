

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Logic.
From Coq Require Import Lia.











Fixpoint div2 (n : nat) :=
  match n with
    0 => 0
  | 1 => 0
  | S (S n) => S (div2 n)
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.





Fail Fixpoint reaches_1_in (n : nat) :=
  if n =? 1 then 0
  else 1 + reaches_1_in (f n).





Inductive reaches_1 : nat -> Prop :=
  | term_done : reaches_1 1
  | term_more (n : nat) : reaches_1 (f n) -> reaches_1 n.





Conjecture collatz : forall n, reaches_1 n.










Module LePlayground.



Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

End LePlayground.



Inductive clos_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step (x y : X) :
      R x y ->
      clos_trans R x y
  | t_trans (x y z : X) :
      clos_trans R x y ->
      clos_trans R y z ->
      clos_trans R x z.



Inductive clos_refl_trans {X: Type} (R: X->X->Prop) : X->X->Prop :=
  | t_step' (x y : X) :
      R x y ->
      clos_refl_trans R x y
  | t_refl (x : X) :
      clos_refl_trans R x x
  | t_symm (x y : X):
      clos_refl_trans R x y ->
      clos_refl_trans R y x
  | t_trans' (x y z : X) :
      clos_refl_trans R x y ->
      clos_refl_trans R y z ->
      clos_refl_trans R x z.







Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
  | perm3_swap12 (a b c : X) :
      Perm3 [a;b;c] [b;a;c]
  | perm3_swap23 (a b c : X) :
      Perm3 [a;b;c] [a;c;b]
  | perm3_trans (l1 l2 l3 : list X) :
      Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.


















Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).



Fail Inductive wrong_ev (n : nat) : Prop :=
  | wrong_ev_0 : wrong_ev 0
  | wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).








Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.



Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.



Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.  apply ev_SS. apply ev_SS. apply Hn.
Qed.


Theorem ev_double : forall n,
  ev (double n).
Proof.
  induction n.
  - apply ev_0.
  - simpl. apply ev_SS. apply IHn.
Qed.
















Theorem ev_inversion : forall (n : nat),
    ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.  destruct E as [ | n' E'] eqn:EE.
  - 
    left. reflexivity.
  - 
    right. exists n'. split. reflexivity. apply E'.
Qed.





Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H. apply ev_inversion in H.  destruct H as [H0|H1].
  - discriminate.
  - destruct H1 as [n' [Hnm Hev]]. injection Hnm as Heq.
    rewrite Heq. apply Hev.
Qed.



Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.  inversion E as [| n' E' Heq].
  
  apply E'.
Qed.



Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.  destruct H as [ | [m [Hm _]]].
  - discriminate.
  - discriminate.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.



Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H as [| n0 H0 Heq0]. inversion H0 as [| n1 H1 Heq1].
  apply H1.
Qed.






Lemma contradiction_from_false_hypotheses_4 : forall n : nat, forall H : 5 = S (S n), forall H0 : ev n, forall H1 : S (S (S n)) = n, forall H2 : 0 = n, 2 + 2 = 9.

Proof.
intros n H H0 H1 H2.
(* We apply ex_falso_quodlibet because we identify that H2 states 0 = n, which contradicts
     the presence of a successor structure in H, H1.
*)
  exfalso.
(* We rewrite H2 to replace n with 0 throughout the context *)
  rewrite <- H2 in H.
(* Now, we discriminate H, as it presents an inequality: 5 cannot be equal to 2 *)
  discriminate H.
Qed.

Lemma false_equality_from_invalid_assumptions_3 : forall n : nat, forall H : 5 = S (S n), forall H0 : ev n, forall H1 : 3 = n, forall H2 : 0 = n, 2 + 2 = 9.

Proof.
intros n H H0 H1 H2.
rewrite H2 in H1.
(* Using H2 to replace n with 0 in H1, which gives 3 = 0 *)
  apply (@contradiction_from_false_hypotheses_4 n H H0 H1 H2).
Qed.

Lemma false_equality_from_invalid_assumptions_2 : forall n : nat, forall H : 5 = S (S n), forall H0 : ev n, forall H1 : 3 = n, forall H2 : 0 = n, 2 + 2 = 9.

Proof.
intros n H H0 H1 H2.
(* we derive a contradiction by showing 3 = 0 using H1 and H2 *)
  apply (@false_equality_from_invalid_assumptions_3 n H H0 H1 H2).
Qed.

Lemma ev_1_implies_even_1_9 : forall n : nat, forall H : S (S n) = S (S n), forall H0 : ev 3, forall H1 : 3 = n, forall n' : nat, forall H' : ev n', forall H'' : S (S n') = n, forall H2 : 3 = n, forall n0 : nat, forall H4 : ev 1, forall H3 : n0 = 1, ev 1.

Proof.
(* Introduce all the variables and hypotheses into the context *)
  intros n H H0 H1 n' H' H'' H2 n0 H4 H3.
(* Apply one_not_even lemma to get a contradiction *)
  apply one_not_even in H4.
contradiction H4.
Qed.

Lemma ev_SS_injective_ev_1_contradiction_8 : forall n : nat, forall H : S (S n) = S (S n), forall H0 : ev 3, forall H1 : 3 = n, forall n' : nat, forall H' : ev n', forall H'' : S (S n') = n, forall H2 : 3 = n, ev 1.

Proof.
(* Note that the proposition ev 1 is false because ev 0 and ev (S (S n)) for some n are the only constructors for ev, and 1 does not fit either construction.
*)
  intros n H H0 H1 n' H' H'' H2.
(* We use the inversion of H0 which asserts that ev 3 is true, but we know that it is not by the definition of our ev inductive proposition *)
  inversion H0.
apply (@ev_1_implies_even_1_9 n H H0 H1 n' H' H'' H2 n0 H4 H3).
Qed.

Lemma invalid_arithmetic_sum_falsehood_7 : forall n : nat, forall H : S (S n) = S (S n), forall H0 : ev 3, forall H1 : 3 = n, forall n' : nat, forall H' : ev n', forall H'' : S (S n') = n, forall H2 : 3 = n, 2 + 2 = 9.

Proof.
intros n H H0 H1 n' H' H'' H2.
(* We know that if `ev 3` holds, that would contradict the known fact that 3 is odd,
     which is proven by `one_not_even` (or `one_not_even'`).
We can derive the contradiction
     by applying this lemma.
Since `ev 3` implies False, we can prove any statement from it, 
     including `2 + 2 = 9`.
*)
  exfalso.
apply one_not_even.
apply (@ev_SS_injective_ev_1_contradiction_8 n H H0 H1 n' H' H'' H2).
Qed.

Lemma incorrect_sum_from_false_premises_6 : forall n : nat, forall H : S (S n) = S (S n), forall H0 : ev n, forall H1 : 3 = n, forall n' : nat, forall H' : ev n', forall H'' : S (S n') = n, forall H2 : 3 = n, 2 + 2 = 9.

Proof.
intros n H H0 H1 n' H' H'' H2.
(* Use the false premise that 3 = n to derive a contradiction *)
  rewrite <- H1 in H0.
(* Now we have `ev 3` which is a contradiction because we know 1 is not even and `ev_SS` can't be applied to get `ev 1`.
We use `one_not_even` to establish the contradiction.
*)
  apply (@invalid_arithmetic_sum_falsehood_7 n H H0 H1 n' H' H'' H2).
Qed.

Lemma incorrect_sum_from_false_premises_5 : forall n : nat, forall H : S (S n) = S (S n), forall H0 : ev n, forall H1 : 3 = n, forall n' : nat, forall H' : ev n', forall H'' : S (S n') = n, forall H2 : 3 = n, 2 + 2 = 9.

Proof.
intros n H H0 H1 n' H' H'' H2.
(* Use the contradictory hypotheses `H1 : 3 = n` and `H2 : 3 = n` to substitute 3 for n everywhere it appears *)
  apply (@incorrect_sum_from_false_premises_6 n H H0 H1 n' H' H'' H2).
Qed.

Lemma incorrect_sum_from_false_premises_4 : forall n : nat, forall H : S (S n) = S (S n), forall H0 : ev n, forall H1 : 3 = n, forall n' : nat, forall H' : ev n', forall H'' : S (S n') = n, forall H2 : 3 = n, 2 + 2 = 9.

Proof.
intros n H H0 H1 n' H' H'' H2.
(* Introduce all premises *)
  apply (@incorrect_sum_from_false_premises_5 n H H0 H1 n' H' H'' H2).
Qed.

Lemma false_equality_contradiction_3 : forall n : nat, forall H : 5 = S (S n), forall H0 : ev n, forall H1 : 3 = n, forall n' : nat, forall H' : ev n', forall H'' : S (S n') = n, forall H2 : 3 = n, 2 + 2 = 9.

Proof.
intros n H H0 H1 n' H' H'' H2.
rewrite H1 in H.
inversion H.
apply (@incorrect_sum_from_false_premises_4 n H H0 H1 n' H' H'' H2).
Qed.

Lemma false_equality_from_invalid_even_assumption_1 : forall n : nat, forall H : 5 = S (S n), forall H0 : ev n, 2 + 2 = 9.

Proof.
(* We will use proof by contradiction.
Assuming `5 = S (S n)` and `ev n` leads to a contradiction.
*)
  intros n H H0.
(* We use `inversion H` to deduce that `n` is `3`, then we can use `inversion H0` to get `ev 3` which is false as per `one_not_even`.
*)
  inversion H as [H1].
inversion H0 as [| n' H' H''].
- (* In the case `ev 0`, we have a contradiction because `0` is not equal to `3`.
*)
    apply (@false_equality_from_invalid_assumptions_2 n H H0 H1 H2).
- (* In the case `ev (S (S n'))`, we use `H1` in which `n` is `3` and `inversion H'` to deduce `ev 1` which contradicts `one_not_even`.
*)
    inversion H1.
apply (@false_equality_contradiction_3 n H H0 H1 n' H' H'' H2).
Qed.

Lemma false_equality_from_invalid_even_assumption_0 : forall n : nat, forall H : 5 = S (S n), forall H0 : ev n, 2 + 2 = 9.

Proof.
intros n H H0.
(* We derive a contradiction using absurdity from the assumption that 5 = S (S n) *)
  apply (@false_equality_from_invalid_even_assumption_1 n H H0).
Qed.

Theorem ev5_nonsense : ev 5 -> 2 + 2 = 9.

Proof.
(* We invoke proof by contradiction, assuming a premise ev 5 and then proceed to reach a contradiction *)
intros H.
(* Apply inversion on ev to break it down since 5 cannot be 0 or 2 less than an even number as the base cases for ev *)
apply ev_inversion in H.
destruct H as [H0 | H1].
- (* 5 = 0 is absurd, thus a contradiction *)
    discriminate H0.
- (* We have now some n such that 5 = S (S n) for some even number n, which also leads to a contradiction *)
    destruct H1 as [n [H]].
(* Again we reach a contradiction because 5 cannot be represented as S (S n) *)
    apply (@false_equality_from_invalid_even_assumption_0 n H H0).
Qed.
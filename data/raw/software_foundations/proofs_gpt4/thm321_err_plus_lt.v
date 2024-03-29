

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




Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H as [| n0 H0 Heq0].
  inversion H0 as [| n1 H1 Heq1].
  inversion H1.
Qed.




Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.





Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
   unfold Even.



  intros n E. inversion E as [EQ' | n' E' EQ'].
  -  exists 0. reflexivity.
  - 
    assert (H: (exists k', n' = double k')
               -> (exists n0, S (S n') = double n0)).
        { intros [k' EQ'']. exists (S k'). simpl.
          rewrite <- EQ''. reflexivity. }
    apply H.

    

    generalize dependent E'.

    
Abort.










Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - 
    unfold Even. exists 0. reflexivity.
  - 
    unfold Even in IH.
    destruct IH as [k Hk].
    rewrite Hk.
    unfold Even. exists (S k). simpl. reflexivity.
Qed.





Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n. split.
  -  apply ev_Even.
  -  unfold Even. intros [k Hk]. rewrite Hk. apply ev_double.
Qed.






Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em.
  induction En.
  - apply Em.
  - simpl. apply ev_SS. apply IHEn.
Qed.




Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).



Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intros H. induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. apply IHev'1. apply IHev'2.
  - intros H. induction H.
    + apply ev'_0.
    + rewrite <- plus_1_l with (S n). rewrite <- plus_n_Sm. rewrite <- plus_1_l.
      rewrite add_assoc. apply ev'_sum.
      * apply ev'_2.
      * apply IHev.
Qed.



Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
  
Proof.
  intros n m.
  intros E1 E2.
  induction E2.
  - apply E1.
  - simpl in E1. inversion E1 as [| sum E3 H]. apply (IHE2 E3).
Qed.




Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Enm Enp.
  apply ev_ev__ev with (n + n).
  - assert (ev ((n + m) + (n + p))) as H.
      { apply ev_sum. apply Enm. apply Enp. }
    rewrite add_comm with n m in H.
    rewrite <- add_assoc with m n (n + p) in H.
    rewrite add_assoc with n n p in H.
    rewrite add_comm with (n + n) p in H.
    rewrite add_assoc with m p (n + n) in H.
    rewrite add_comm with (m + p) (n + n) in H.
    apply H.
  - rewrite <- double_plus. apply ev_double.
Qed.







Module Playground.



Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "n <= m" := (le n m).







Theorem test_le1 :
  3 <= 3.
Proof.
  
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  
  intros H. inversion H. inversion H2.  Qed.



Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

End Playground.



Inductive total_relation : nat -> nat -> Prop :=
  | total_rel (n m : nat) : total_relation n m
.

Theorem total_relation_is_total : forall n m, total_relation n m.
  Proof.
  intros n m. apply (total_rel n m). Qed.




Inductive empty_relation : nat -> nat -> Prop :=
.

Theorem empty_relation_is_empty : forall n m, ~ empty_relation n m.
  Proof.
  intros n m H.
  inversion H.
Qed.







Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Emn Eno.
  induction Eno as [|o Eno IH].
  - apply Emn.
  - apply (le_S m o IH).
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n.
  induction n.
  - apply le_n.
  - apply (le_S 0 n IHn).
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H as [|m H IH].
  - apply le_n.
  - apply (le_S (S n) (S m) IH).
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  induction m.
  - inversion H as [H0 | zero H1 H2]. apply le_n. inversion H1.
  - inversion H as [H0 | Sm H1 H2]. apply le_n. apply (le_S n m (IHm H1)).
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m.
  destruct m.
  - right. apply O_le_n.
  - induction n.
    + left. apply n_le_m__Sn_le_Sm. apply O_le_n.
    + destruct IHn.
      * destruct H.
        right. apply le_n.
        left. apply n_le_m__Sn_le_Sm. apply H.
      * right. apply le_S. apply H.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction b.
  - rewrite add_0_r. apply le_n.
  - rewrite <- plus_n_Sm. apply (le_S a (a + b) IHb).
Qed.

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H.
  induction H.
  - split.
    + apply le_plus_l.
    + rewrite add_comm. apply le_plus_l.
  - destruct IHle as [H1 H2].
    split.
    + apply (le_S n1 m H1).
    + apply (le_S n2 m H2).
Qed.

Theorem add_le_cases : forall n m p q,
  n + m <= p + q -> n <= p \/ m <= q.
  
Proof.
  induction n.
  - left. apply O_le_n.
  - intros. destruct p.
    + right. apply plus_le in H.
      destruct H as [H1 H2].
      rewrite plus_O_n in H1.
      apply H2.
    + simpl in H.
      rewrite plus_n_Sm with n m in H.
      rewrite plus_n_Sm with p q in H.
      apply IHn in H. destruct H.
      * left. apply n_le_m__Sn_le_Sm. apply H.
      * right. apply Sn_le_Sm__n_le_m. apply H.
Qed.

Theorem plus_le_compat_l : forall n m p,
  n <= m ->
  p + n <= p + m.
Proof.
  intros n m p.
  induction p.
  - intros. rewrite plus_O_n. rewrite plus_O_n. apply H.
  - intros. simpl. apply n_le_m__Sn_le_Sm. apply (IHp H).
Qed.

Theorem plus_le_compat_r : forall n m p,
  n <= m ->
  n + p <= m + p.
Proof.
  intros n m p H.
  rewrite add_comm with n p.
  rewrite add_comm with m p.
  apply plus_le_compat_l.
  apply H.
Qed.

Theorem le_plus_trans : forall n m p,
  n <= m ->
  n <= m + p.
Proof.
  intros n m p.
  generalize dependent n.
  generalize dependent m.
  induction p.
  - intros. rewrite add_comm. rewrite plus_O_n. apply H.
  - intros. destruct H.
    + apply le_plus_l.
    + simpl.
      apply IHp in H.
      apply le_S in H. rewrite plus_n_Sm in H.
      apply (le_S n (m + S p) H).
Qed.

Theorem n_lt_m__n_le_m : forall n m,
  n < m ->
  n <= m.
Proof.
  intros n m H.
  apply le_S in H.
  apply Sn_le_Sm__n_le_m in H.
  apply H.
Qed.



Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.

Proof.
(* We first introduce our variables n1, n2, and m *)
  intros n1 n2 m.
(* Then we unpack the premise that n1 + n2 is less than m *)
  intro H.
(* We must prove a conjunction, so we split the goal into two separate subgoals *)
  split.
- (* First, we'll prove n1 < m *)
    (* Applying our previous lemma: if n1 + n2 <= m, then n1 <= m *)
    assert (H1: n1 <= m).
{
      (* If n1 + n2 is less than m, then naturally, n1 + n2 is also less than or equal to m *)
      apply le_S_n in H.
(* We then apply the plus_le lemma to break down the addition *)
      apply plus_le in H.
(* This gives us two subgoals: n1 <= m and n2 <= m; we're interested in the first one *)
      destruct H as [H1 _].
(* We've obtained n1 <= m *)
      exact H1.
}

    (* Using the fact that n1 + n2 is less than m and n1 <= m, we deduce that n1 < m *)
    apply n_le_m__Sn_le_Sm with (n := n1) (m := n2) in H1.
(* Now, we'll need to show that Sn1 + n2 <= m, to eventually conclude n1 < m *)
    apply le_trans with (n := S n1 + n2) (m := n1 + n2) (o := m).
+ (* Showing S n1 + n2 <= n1 + S n2, by swapping positions using add_comm3_take3 *)
      rewrite add_comm3_take3.
apply le_n.
+ (* n1 + S n2 <= m follows from our assumption *)
      exact H1.
- (* Now we will prove n2 < m *)
    (* Applying our previous lemma: if n1 + n2 <= m, then n2 <= m *)
    assert (H2: n2 <= m).
{
      (* If n1 + n2 is less than m, then naturally, n1 + n2 is also less than or equal to m *)
      apply le_S_n in H.
(* We then apply the plus_le lemma to break down the addition *)
      apply plus_le in H.
(* This gives us two subgoals: n1 <= m and n2 <= m; we're interested in the second one *)
      destruct H as [_ H2].
(* We've obtained n2 <= m *)
      exact H2.
}

    (* Using the fact that n1 + n2 is less than m and n2 <= m, we deduce that n2 < m *)
    apply n_le_m__Sn_le_Sm with (n := n2) (m := n1) in H2.
(* Now, we'll need to show that n2 + Sn1 <= m, to eventually conclude n2 < m *)
    apply le_trans with (n := n2 + S n1) (m := S n1 + n2) (o := m).
+ (* Showing n2 + S n1 <= S n1 + n2 by swapping positions using add_comm3_take3 *)
      rewrite <- add_comm3_take3.
apply le_n.
+ (* S n1 + n2 <= m follows from our assumption *)
      exact H2.
Qed.
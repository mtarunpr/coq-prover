

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
  intros n1 n2 m H.
  inversion H as [H12 | n H12 Hm].
  - split.
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply n_le_m__Sn_le_Sm. rewrite add_comm. apply le_plus_l.
  - rewrite <- Hm in H. apply Sn_le_Sm__n_le_m in H.
    apply plus_le in H. destruct H as [H1 H2].
    split.
    + apply n_le_m__Sn_le_Sm. apply H1.
    + apply n_le_m__Sn_le_Sm. apply H2.
Qed.



Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent m.
  induction n.
  - intros. apply O_le_n.
  - intros. destruct m.
    + discriminate.
    + simpl in H. apply IHn in H. apply n_le_m__Sn_le_Sm. apply H.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
  
Proof.
  intros n m.
  generalize dependent n.
  induction m.
  - intros. inversion H. reflexivity.
  - destruct n.
    + reflexivity.
    + intros. apply Sn_le_Sm__n_le_m in H. apply (IHm n H).
Qed.



Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m.
  split.
  - apply leb_complete.
  - apply leb_correct.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o Hnm Hmo.
  apply leb_complete in Hnm.
  apply leb_complete in Hmo.
  apply leb_correct.
  apply le_trans with m.
  apply Hnm. apply Hmo.
Qed.


Module R.



Inductive R : nat -> nat -> nat -> Prop :=
  | c1                                     : R 0     0     0
  | c2 m n o (H : R m     n     o        ) : R (S m) n     (S o)
  | c3 m n o (H : R m     n     o        ) : R m     (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m     n     o
  | c5 m n o (H : R m     n     o        ) : R n     m     o
.






Definition manual_grade_for_R_provability : option (nat*string) := None.




Definition fR : nat -> nat -> nat
  := plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  split.
  - intros. induction H.
    + reflexivity.
    + simpl. f_equal. apply IHR.
    + rewrite <- plus_n_Sm. f_equal. apply IHR.
    + simpl in IHR.
      apply S_injective in IHR. rewrite <- plus_n_Sm in IHR.
      apply S_injective in IHR.
      apply IHR.
    + rewrite add_comm in IHR. apply IHR.
  - intros.
    rewrite <- H.
    destruct H.
    induction m.
      + induction n. apply c1. apply c3. apply IHn.
      + simpl. apply c2. apply IHm.
Qed.


End R.



Inductive subseq : list nat -> list nat -> Prop :=
  | subseq0 l : subseq [] l
  | subseq1 x l1 l2 (H : subseq l1 l2) : subseq (x :: l1) (x :: l2)
  | subseq2 x l1 l2 (H : subseq l1 l2) : subseq l1 (x :: l2)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  induction l as [| x l IH].
  - apply subseq0.
  - apply (subseq1 x l l IH).
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros.
  induction H as [| x l1 l2 H IH | x l1 l2 H IH].
  - apply subseq0.
  - simpl. apply (subseq1 x l1 (l2 ++ l3) IH).
  - simpl. apply (subseq2 x l1 (l2 ++ l3) IH).
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  
  intros l1 l2 l3 H12 H23.
  generalize dependent l1.
  induction H23 as [| x l2 l3 H23 IH | x l2 l3 H23 IH].
  - intros.
    assert (l1 = []) as Hl1. inversion H12. reflexivity.
    rewrite Hl1. apply subseq0.
  - intros. inversion H12 as [| x' l1' l2' H12' | x' l1' l2' H12'].
    + apply subseq0.
    + apply (subseq1 x l1' l3 (IH l1' H12')).
    + apply (subseq2 x l1 l3 (IH l1 H12')).
  - intros. apply (subseq2 x l1 l3 (IH l1 H12)).
Qed.










Module bin1.
Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
End bin1.




Module bin2.
Inductive bin : Type :=
  | Z : bin
  | B0 (n : bin) : bin
  | B1 (n : bin) : bin.
End bin2.



Module bin3.
Inductive bin : Type :=
  | Z : bin
  | B0 : bin -> bin
  | B1 : bin -> bin.
End bin3.












Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.







Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).



Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1]).
  - apply MChar.
  - apply MChar.
Qed.



Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.



Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.



Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply MStarApp.
  - apply H.
  - apply MStar0.
Qed.





Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  unfold not. intros. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros.
  destruct H.
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.



Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H1.
  induction ss as [| s1 ss IH].
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
    + apply H1. left. reflexivity.
    + apply IH. intros s2 H2. apply H1. right. apply H2.
Qed.






Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.



Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  
  - 
    simpl in Hin. destruct Hin.
  - 
    simpl. simpl in Hin.
    apply Hin.
  - 
    simpl.



    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + 
      left. apply (IH1 Hin).
    + 
      right. apply (IH2 Hin).
  - 
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - 
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - 
    destruct Hin.
  - 
    simpl.



    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + 
      apply (IH1 Hin).
    + 
      apply (IH2 Hin).
Qed.



Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  := match re with
     | EmptySet => false
     | EmptyStr => true
     | Char _ => true
     | App re1 re2 => (re_not_empty re1) && (re_not_empty re2)
     | Union re1 re2 => (re_not_empty re1) || (re_not_empty re2)
     | Star _ => true
     end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros H. destruct H as [s Hmatch].
    induction Hmatch.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHHmatch1. rewrite IHHmatch2. reflexivity.
    + simpl. rewrite IHHmatch. reflexivity.
    + simpl. apply orb_true_iff. right. apply IHHmatch.
    + reflexivity.
    + reflexivity.
  - intros H.
    induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply IHre1 in H1. destruct H1 as [s1 H1].
      apply IHre2 in H2. destruct H2 as [s2 H2].
      exists (s1 ++ s2). apply MApp. apply H1. apply H2.
    + simpl in H. apply orb_true_iff in H. destruct H as [H1 | H2].
      * apply IHre1 in H1. destruct H1 as [s1 H1].
        exists s1. apply MUnionL. apply H1.
      * apply IHre2 in H2. destruct H2 as [s2 H2].
        exists s2. apply MUnionR. apply H2.
    + exists []. apply MStar0.
Qed.







Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.



  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].



  - 
    simpl. intros s2 H. apply H.



  -  intros s2 H. simpl. 
Abort.



Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.


Abort.



Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.



  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].



  -   discriminate.
  -    discriminate.
  -     discriminate.
  -  discriminate.
  -  discriminate.



  - 
    injection Heqre' as Heqre''. intros s H. apply H.

  - 
    injection Heqre' as Heqre''.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite Heqre''. reflexivity.
      * apply H1.
Qed.





Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re Hmatch.
  remember (Star re) as re'.
  induction Hmatch
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. split. reflexivity. intros s' contra. inversion contra.
  - destruct (IH2 Heqre') as [ss' [H1 H2]].
    injection Heqre' as Heqre'. destruct Heqre'.
    exists (s1 :: ss'). split.
    + simpl. rewrite <- H1. reflexivity.
    + intros s' HIn. destruct HIn.
      * rewrite <- H. apply Hmatch1.
      * apply H2 in H. apply H.
Qed.




Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.



Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - 
    apply le_n.
  - 
    apply le_n.
  - 
    apply le_S. apply le_n.
  - 
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - 
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - 
    simpl. apply IHre.
Qed.

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  inversion Hp1 as [Hp1'| p Hp1' Hp1''].
  - rewrite H in Hp1'. discriminate Hp1'.
  - rewrite H in Hp1''. discriminate Hp1''.
Qed.



Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.



Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.



Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.


Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - 
    simpl. intros contra. inversion contra.
  - 
    intros contra. apply Sn_le_Sm__n_le_m in contra. inversion contra.
  - 
    intros H. simpl in H.
    rewrite app_length in H.
    apply add_le_cases in H. destruct H.
    + apply IH1 in H.
      destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
      exists s1'. exists s2'. exists (s3' ++ s2).
      split. rewrite Happ.
      rewrite <- app_assoc with T s1' (s2' ++ s3') s2.
      rewrite <- app_assoc with T s2' s3' s2.
      reflexivity.
      split. apply Hne.
      intros m.
      rewrite app_assoc with T s1' (napp m s2') (s3' ++ s2).
      rewrite app_assoc with T (s1' ++ napp m s2') s3' s2.
      rewrite <- app_assoc with T s1' (napp m s2') s3'.
      apply MApp. apply Hnapp. apply Hmatch2.
    + apply IH2 in H.
      destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
      exists (s1 ++ s1'). exists s2'. exists s3'.
      split. rewrite Happ.
      rewrite <- app_assoc with T s1 s1' (s2' ++ s3').
      reflexivity.
      split. apply Hne.
      intros m.
      rewrite <- app_assoc with T s1 s1' (napp m s2' ++ s3').
      apply MApp. apply Hmatch1. apply Hnapp.
  - 
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H H'].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
    exists s1'. exists s2'. exists s3'.
    split. apply Happ.
    split. apply Hne.
    intros m. apply MUnionL. apply Hnapp.
  - 
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H' H].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
    exists s1'. exists s2'. exists s3'.
    split. apply Happ.
    split. apply Hne.
    intros m. apply MUnionR. apply Hnapp.
  - 
    intros H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    inversion H as [H0|]. rewrite H0 in Hp. inversion Hp.
  - 
    intros H.
    rewrite app_length in H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    assert (Hl: (1 <= length s1 \/ 1 <= length s2)).
    { destruct s1. right. apply le_trans with (pumping_constant re). apply Hp. apply H. left. simpl. apply n_le_m__Sn_le_Sm. apply O_le_n. }
    exists []. exists (s1 ++ s2). exists [].
    split. rewrite app_nil_r. reflexivity.
    split. destruct Hl as [Hl | Hl].
    + destruct s1. inversion Hl. discriminate.
    + destruct s2. inversion Hl. destruct s1. discriminate. discriminate.
    + induction m.
      * apply MStar0.
      * simpl in IHm. simpl. rewrite <- app_assoc.
        apply star_app.
        apply (MStarApp s1 s2 re Hmatch1 Hmatch2).
        apply IHm.
Qed.




Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.


Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - 
    simpl. intros contra. inversion contra.
  - 
    intros contra. apply Sn_le_Sm__n_le_m in contra. inversion contra.
  - 
    intros H.
    assert (le_n_n: forall n : nat, ~ n < n).
    { intros n contra. induction n. inversion contra. apply IHn. apply Sn_le_Sm__n_le_m in contra. apply contra. }
    rewrite app_length in H. simpl in H.
    destruct (lt_ge_cases (length s1) (pumping_constant re1)) as [H1 | H1].
    + destruct (lt_ge_cases (length s2) (pumping_constant re2)) as [H2 | H2].
      * apply add_le_cases in H. destruct H as [H1' | H2'].
        ** assert (contra: pumping_constant re1 < pumping_constant re1).
           {
             apply le_trans with (n := S (length s1)).
             apply n_le_m__Sn_le_Sm. apply H1'. apply H1.
           }
           apply le_n_n in contra. exfalso. apply contra.
        ** assert (contra: pumping_constant re2 < pumping_constant re2).
           {
             apply le_trans with (n := S (length s2)).
             apply n_le_m__Sn_le_Sm. apply H2'. apply H2.
           }
           apply le_n_n in contra. exfalso. apply contra.
      * apply IH2 in H2.
        destruct H2 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists (s1 ++ s1'). exists s2'. exists s3'.
        split. rewrite Happ.
        rewrite <- app_assoc with T s1 s1' (s2' ++ s3').
        reflexivity.
        split. apply Hne.
        split. simpl. rewrite app_length. rewrite <- add_assoc.
        apply le_trans with (n := length s1 + pumping_constant re2).
        apply plus_le_compat_l. apply Hlen.
        apply plus_le_compat_r. apply n_lt_m__n_le_m in H1. apply H1.
        intros m.
        rewrite <- app_assoc with T s1 s1' (napp m s2' ++ s3').
        apply MApp. apply Hmatch1. apply Hnapp.
    + apply IH1 in H1.
      destruct H1 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
      exists s1'. exists s2'. exists (s3' ++ s2).
      split. rewrite Happ.
      rewrite <- app_assoc with T s1' (s2' ++ s3') s2.
      rewrite <- app_assoc with T s2' s3' s2.
      reflexivity.
      split. apply Hne.
      split. simpl.
      apply le_trans with (n := pumping_constant re1).
      apply Hlen. apply le_plus_l.
      intros m.
      rewrite app_assoc with T s1' (napp m s2') (s3' ++ s2).
      rewrite app_assoc with T (s1' ++ napp m s2') s3' s2.
      rewrite <- app_assoc with T s1' (napp m s2') s3'.
      apply MApp. apply Hnapp. apply Hmatch2.
  - 
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H H'].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
    exists s1'. exists s2'. exists s3'.
    split. apply Happ.
    split. apply Hne.
    split. simpl. apply le_trans with (n := pumping_constant re1). apply Hlen. apply le_plus_l.
    intros m. apply MUnionL. apply Hnapp.
  - 
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H' H].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
    exists s1'. exists s2'. exists s3'.
    split. apply Happ.
    split. apply Hne.
    split. simpl. apply le_trans with (n := pumping_constant re2). apply Hlen. rewrite add_comm. apply le_plus_l.
    intros m. apply MUnionR. apply Hnapp.
  - 
    intros H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    inversion H as [H0|]. rewrite H0 in Hp. inversion Hp.
  - 
    intros H.
    rewrite app_length in H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    assert (Hl: (1 <= length s1 \/ 1 <= length s2)).
    { destruct s1. right. apply le_trans with (pumping_constant re). apply Hp. apply H. left. simpl. apply n_le_m__Sn_le_Sm. apply O_le_n. }
    destruct s1 as [| x s11].
    + destruct (lt_ge_cases (length s2) (pumping_constant (Star re))) as [H2 | H2].
      * exists []. exists s2. exists [].
        split. rewrite app_nil_r. reflexivity.
        split. destruct Hl as [Hl | Hl].
        ** inversion Hl.
        ** destruct s2. inversion Hl. discriminate.
        ** split. apply n_lt_m__n_le_m in H2. apply H2.
        induction m. apply MStar0. simpl. rewrite <- app_assoc. apply star_app. apply Hmatch2. apply IHm.
      * apply IH2 in H2.
        destruct H2 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists s1'. exists s2'. exists s3'.
        split. rewrite Happ. reflexivity.
        split. apply Hne.
        split. apply Hlen.
        apply Hnapp.
    + remember (x :: s11) as s1.
      destruct (lt_ge_cases (length s1) (pumping_constant re)) as [H1 | H1].
      * exists []. exists s1. exists s2.
        split. reflexivity.
        split. rewrite Heqs1. discriminate.
        split. apply n_lt_m__n_le_m in H1. apply H1.
        intros m. simpl. apply napp_star. apply Hmatch1. apply Hmatch2.
      * apply IH1 in H1.
        destruct H1 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists s1'. exists s2'. exists (s3' ++ s2).
        split. rewrite Happ. simpl.
        rewrite <- app_assoc with (m := s2' ++ s3').
        rewrite <- app_assoc with (m := s3').
        reflexivity.
        split. apply Hne.
        split. apply Hlen.
        intros m. rewrite app_assoc. rewrite app_assoc. apply MStarApp.
        rewrite <- app_assoc. apply Hnapp. apply Hmatch2.
Qed.

End Pumping.







Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - 
    simpl. intros H. apply H. reflexivity.
  - 
    simpl. destruct (n =? m) eqn:H.
    + 
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + 
      intros H'. right. apply IHl'. apply H'.
Qed.





Inductive reflect (P : Prop) : bool -> Prop :=
  | ReflectT (H :   P) : reflect P true
  | ReflectF (H : ~ P) : reflect P false.





Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  
  intros P b H. destruct b eqn:Eb.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.




Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b r. destruct r as [HP | HnP].
  - split. reflexivity. intros. apply HP.
  - split.
    + intros HP. exfalso. apply (HnP HP).
    + discriminate.
Qed.






Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.





Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - 
    simpl. intros H. apply H. reflexivity.
  - 
    simpl. destruct (eqbP n m) as [H | H].
    + 
      intros _. rewrite H. left. reflexivity.
    + 
      intros H'. right. apply IHl'. apply H'.
Qed.



Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l Hcount. induction l as [| m l' IHl'].
  - intros contra. inversion contra.
  - simpl in Hcount. destruct (eqbP n m).
    + inversion Hcount.
    + intros contra. destruct contra as [Heq | HIn].
      * symmetry in Heq. apply (H Heq).
      * apply (IHl' Hcount HIn).
Qed.









Inductive nostutter {X:Type} : list X -> Prop :=
  | nostutter0 : nostutter []
  | nostutter1 x : nostutter [x]
  | nostutter2 x y l (P: x <> y) (H: nostutter (y :: l)) : nostutter (x :: y :: l)
.


Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  apply nostutter2. discriminate.
  apply nostutter2. discriminate.
  apply nostutter2. discriminate.
  apply nostutter2. discriminate.
  apply nostutter2. discriminate.
  apply nostutter1.
Qed.




Example test_nostutter_2 : nostutter (@nil nat).

Proof.
(* Apply the constructor nostutter.nil, which states that an empty list has no stuttering.
*)
  apply nostutter_nil.
Qed.
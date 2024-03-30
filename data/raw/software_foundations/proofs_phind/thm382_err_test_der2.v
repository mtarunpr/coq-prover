

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


Example test_nostutter_2:  nostutter (@nil nat).
Proof. apply nostutter0. Qed.


Example test_nostutter_3:  nostutter [5].
Proof. apply nostutter1. Qed.


Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof.
  intros contra1.
  inversion contra1 as [| |x1 y1 l1 _ contra2].
  inversion contra2 as [| |x2 y2 l2 contra _].
  apply contra. reflexivity.
Qed.



Definition manual_grade_for_nostutter : option (nat*string) := None.




Inductive merge {X:Type} : list X -> list X -> list X -> Prop :=
  | mergel0 l : merge l [] l
  | merger0 l : merge [] l l
  | mergel1 x l l1 l2 (H: merge l1 l2 l) : merge (x :: l1) l2 (x :: l)
  | merger1 x l l1 l2 (H: merge l1 l2 l) : merge l1 (x :: l2) (x :: l)
.

Theorem merge_filter : forall (X : Set) (test: X->bool) (l l1 l2 : list X),
  merge l1 l2 l ->
  All (fun n => test n = true) l1 ->
  All (fun n => test n = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 H H1 H2.
  induction H as [| |x l l1 l2 _ IHm|x l l1 l2 _ IHm].
  - induction l.
    + reflexivity.
    + destruct H1 as [Htest H1]. simpl. rewrite Htest. rewrite (IHl H1). reflexivity.
  - induction l.
    + reflexivity.
    + destruct H2 as [Htest H2]. simpl. rewrite Htest. apply (IHl H2).
  - destruct H1 as [Htest H1]. simpl. rewrite Htest. rewrite (IHm H1 H2). reflexivity.
  - destruct H2 as [Htest H2]. simpl. rewrite Htest. rewrite (IHm H1 H2). reflexivity.
Qed.





Theorem subs_filter : forall (test: nat->bool) (l1 l2 : list nat),
  subseq l1 l2 ->
  All (fun n => test n = true) l1 ->
  length l1 <= length (filter test l2).
Proof.
  intros test l1 l2 H H1.
  induction H as [| x l1 l2 H IH | x l1 l2 H IH].
  - apply O_le_n.
  - destruct H1 as [Htest H1]. simpl. rewrite Htest. simpl. apply n_le_m__Sn_le_Sm. apply (IH H1).
  - simpl. destruct (test x).
    + simpl. apply le_S. apply (IH H1).
    + apply (IH H1).
Qed.




Inductive pal {X:Type} : list X -> Prop :=
  | pal0 : pal []
  | pal1 x : pal [x]
  | pal2 x l (H: pal l) : pal (x :: l ++ [x])
.

Theorem pal_app_rev : forall (X:Type) (l : list X),
  pal (l ++ (rev l)).
Proof.
  intros X l.
  induction l.
  - apply pal0.
  - simpl. rewrite app_assoc. apply pal2. apply IHl.
Qed.

Theorem pal_rev : forall (X:Type) (l: list X) , pal l -> l = rev l.
Proof.
  intros X l H.
  induction H as [| | x l _ IH].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite <- IH. rewrite <- app_assoc. reflexivity.
Qed.




Theorem palindrome_converse: forall {X: Type} (l: list X),
    l = rev l -> pal l.
Proof.
  intros X.
  assert (rev_length: forall (l: list X), length (rev l) = length l).
  {
    intros l. induction l as [| n l' IHl'].
    - reflexivity.
    - simpl. rewrite -> app_length.
      simpl. rewrite -> IHl'. rewrite add_comm.
      reflexivity.
  }
  assert (lemma: forall (n: nat) (l: list X), length l <= n -> l = rev l -> pal l).
  {
    induction n.
    - intros l Hn _. destruct l. apply pal0. inversion Hn.
    - destruct l.
      + intros _ _. apply pal0.
      + intros Hlen Hrev. destruct (rev l) as [| x' l'] eqn:H'.
        * destruct l. apply pal1. apply f_equal with (f:=rev) in H'. rewrite rev_involutive in H'. discriminate.
        * simpl in Hrev. rewrite H' in Hrev. rewrite Hrev. injection Hrev as H0 H. destruct H0. apply pal2.
          apply f_equal with (f:=rev) in H. rewrite rev_app_distr in H. simpl in H. rewrite H' in H. injection H as H.
          apply f_equal with (f:=length) in H'. simpl in H'.
          simpl in Hlen. apply Sn_le_Sm__n_le_m in Hlen.
          rewrite rev_length in H'.
          assert (Hlen': length l' <= n).
          { apply Sn_le_Sm__n_le_m. rewrite <- H'. apply le_S. apply Hlen. }
          apply (IHn l' Hlen' H).
  }
  intros l.
  apply (lemma (length l) l). apply le_n.
Qed.








Inductive disjoint {X : Type} : list X -> list X -> Prop :=
  | disjoint0 l : disjoint [] l
  | disjoint1 x l1 l2 (P: ~ In x l2) (H: disjoint l1 l2) : disjoint (x :: l1) l2
.



Inductive NoDup {X : Type} : list X -> Prop :=
  | NoDup0 : NoDup []
  | NoDup1 x l (P: ~ In x l) (H: NoDup l) : NoDup (x :: l)
.



Theorem disjoint_NoDup_app : forall (X:Type) (l1:list X) (l2:list X), NoDup l1 -> NoDup l2 -> disjoint l1 l2 -> NoDup (l1 ++ l2).
Proof.
  intros X l1 l2 H1 H2 H.

  induction H as [| x l1 l2 P2 Hd].
  - apply H2.
  - simpl. apply NoDup1.
    + intros contra. apply In_app_iff in contra. destruct contra as [contra | contra].
      * inversion H1 as [| x1 l1' P1]. apply (P1 contra).
      * apply (P2 contra).
    + inversion H1 as [| x1 l1' P1 H1']. apply (IHHd H1' H2).
Qed.

Theorem NoDup_app : forall (X:Type) (l1:list X) (l2:list X), NoDup (l1 ++ l2) -> NoDup l1 /\ NoDup l2.
Proof.
  intros.
  split.
  - induction l1. apply NoDup0. apply NoDup1.
    + intros contra. inversion H. apply P. apply In_app_iff. left. apply contra.
    + inversion H. apply (IHl1 H1).
  - induction l1.
    + apply H.
    + inversion H. apply (IHl1 H1).
Qed.

Theorem NoDup_app_disjoint : forall (X:Type) (l1:list X) (l2:list X), NoDup (l1 ++ l2) -> disjoint l1 l2.
Proof.
  intros X l1 l2 H.
  induction l1.
  - apply disjoint0.
  - apply disjoint1.
    + inversion H. intros contra. apply P. apply In_app_iff. right. apply contra.
    + inversion H. apply (IHl1 H1).
Qed.


Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.






Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros.
  induction l.
  - inversion H.
  - inversion H.
    + exists []. exists l. rewrite H0. reflexivity.
    + apply IHl in H0. destruct H0 as [l1 [l2 H0]].
      exists (x0 :: l1). exists l2. rewrite H0. reflexivity.
Qed.



Inductive repeats {X:Type} : list X -> Prop :=
  | repeats1 x l (P: In x l): repeats (x :: l)
  | repeats2 x l (H: repeats l): repeats (x :: l)
.


Definition manual_grade_for_check_repeats : option (nat*string) := None.


Theorem pigeonhole_principle: excluded_middle ->
  forall (X:Type) (l1  l2:list X),
  (forall x, In x l1 -> In x l2) ->
  length l2 < length l1 ->
  repeats l1.
Proof.
  intros EM X l1. induction l1 as [|x l1' IHl1'].
  - intros. inversion H0.
  - intros. destruct (EM (In x l1')) as [HIn | HnIn].
    + apply repeats1. apply HIn.
    + apply repeats2.
      destruct (in_split X x l2) as [l0 [l2' H3]].
      { apply H. simpl. left. reflexivity. }
      apply IHl1' with (l0 ++ l2').
      * intros. apply In_app_iff. assert (In x0 l2). apply H. right. apply H1.
        rewrite H3 in H2. apply In_app_iff in H2. destruct H2. left. apply H2.
        right. destruct H2. rewrite H2 in HnIn. exfalso. apply HnIn. apply H1. apply H2.
      * apply f_equal with (f:=length) in H3. rewrite app_length in H3. rewrite add_comm in H3. simpl in H3. rewrite app_length. rewrite add_comm. rewrite H3 in H0. simpl in H0. apply Sn_le_Sm__n_le_m in H0. apply H0.
Qed.








Require Import Coq.Strings.Ascii.

Definition string := list ascii.






Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.


Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.


Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.


Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.


Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.


Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.


Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.


Lemma app_exists : forall (s : string) re0 re1,
  s =~ App re0 re1 <->
  exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.


Lemma app_ne : forall (a : ascii) s re0 re1,
  a :: s =~ (App re0 re1) <->
  ([ ] =~ re0 /\ a :: s =~ re1) \/
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H.
    destruct s1.
    + left. split. apply H3. apply H4.
    + right. inversion H1 as [H1']. destruct H1'. exists s1. exists s2. split. reflexivity. split. apply H3. apply H4.
  - intros.
    destruct H as [[H1 H2] | [s1 [s2 [H1 [H2 H3]]]]].
    + assert (silly: a :: s = [] ++ a :: s). reflexivity. rewrite silly. apply MApp. apply H1. apply H2.
    + rewrite H1. assert (silly: a :: s1 ++ s2 = (a :: s1) ++ s2). reflexivity. rewrite silly. apply MApp. apply H2. apply H3.
Qed.



Lemma union_disj : forall (s : string) re0 re1,
  s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.



Lemma star_ne : forall (a : ascii) s re,
  a :: s =~ Star re <->
  exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  split.
  - remember (a :: s) as s'. remember (Star re) as re'.
    intros H. induction H as [| | | | | | s1 s2 re' H1 _ H2 IH].
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + destruct s1.
      * apply (IH Heqs' Heqre').
      * injection Heqre' as Heqre'. destruct Heqre'.
        injection Heqs' as Heqs' Happ. destruct Heqs'.
        exists s1. exists s2.
        split. rewrite Happ. reflexivity.
        split. apply H1. apply H2.
  - intros H. destruct H as [s1 [s2 [H1 [H2 H3]]]].
    rewrite H1.
    assert (silly: a :: s1 ++ s2 = (a :: s1) ++ s2). reflexivity. rewrite silly.
    apply (MStarApp (a :: s1) s2 re H2 H3).
Qed.



Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).


Fixpoint match_eps (re: reg_exp ascii) : bool
  := match re with
     | EmptySet => false
     | EmptyStr => true
     | Char _ => false
     | App re1 re2 => (match_eps re1) && (match_eps re2)
     | Union re1 re2 => (match_eps re1) || (match_eps re2)
     | Star _ => true
  end.



Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  intros re.
  induction re.
  - apply ReflectF. intros contra. inversion contra.
  - apply ReflectT. apply MEmpty.
  - apply ReflectF. intros contra. inversion contra.
  - simpl. inversion IHre1 as [H1 Hb1 | H1 Hb1].
    + inversion IHre2 as [H2 Hb2 | H2 Hb2].
      * apply ReflectT. apply (MApp [] re1 [] re2 H1 H2).
      * apply ReflectF.
        intros contra. inversion contra as [| | s1 re1' s2 re2' H1' H2'| | | |].
        destruct s2. apply (H2 H2'). destruct s1. discriminate. discriminate.
    + apply ReflectF.
      intros contra. inversion contra as [| | s1 re1' s2 re2' H1' H2'| | | |].
      destruct s1. apply (H1 H1'). discriminate.
  - simpl. inversion IHre1 as [H1 Hb1 | H1 HB1].
    + apply ReflectT. apply (MUnionL [] re1 re2 H1).
    + inversion IHre2 as [H2 Hb2 | H2 Hb2].
      * apply ReflectT. apply (MUnionR re1 [] re2 H2).
      * apply ReflectF.
        intros contra. inversion contra as [| | | s1 re1' re2' H1' | re1' s1 re2' H2' | |].
        ** apply (H1 H1').
        ** apply (H2 H2').
  - apply ReflectT. apply MStar0.
Qed.






Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.


Definition derives d := forall a re, is_der re a (d a re).


Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii
  := match re with
     | EmptySet => EmptySet
     | EmptyStr => EmptySet
     | Char x => if eqb x a then EmptyStr else EmptySet
     | App re1 re2 => if match_eps re1 then Union (derive a re2) (App (derive a re1) re2) else App (derive a re1) re2
     | Union re1 re2 => Union (derive a re1) (derive a re2)
     | Star re => App (derive a re) (Star re)
     end.



Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.


Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  reflexivity. Qed.


Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  reflexivity. Qed.




Example test_der2 : match_eps (derive c (Char d)) = false.

Proof.
(* We will prove the example by structural induction on the regular expression re.
*)
  intros re.
(* We will need to use the IHderive lemma, which states that the derive function is correct.
*)
  induction re as [|re1 re2|].
- (* Base case: EmptySet *)
    simpl.
reflexivity.
- (* Base case: EmptyStr *)
    simpl.
reflexivity.
- (* Base case: Char x *)
    simpl.
split.
- intros H.
inversion H.
- intros H.
inversion H.
- (* Base case: App re1 re2 *)
    simpl.
split.
- intros H.
inversion H.
- intros H.
inversion H.
- (* Base case: Union re1 re2 *)
    simpl.
split.
- intros H.
inversion H.
- intros H.
inversion H.
- (* Base case: Star re *)
    simpl.
split.
- intros H.
inversion H.
- intros H.
inversion H.
Qed.
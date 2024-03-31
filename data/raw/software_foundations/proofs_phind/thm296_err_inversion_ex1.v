

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






Lemma list_equality_reflexivity_3 : forall H : [0; 0] = [0; 0], [0] = [0].

Proof.
intros H.
(* We want to prove that [0] = [0].
The context gives us a hypothesis H that [0; 0] = [0; 0].
However, this information is not useful for our goal.
The goal is to prove that [0] = [0],
     which is trivial because both sides are the same list.
*)
  reflexivity.
Qed.

Lemma list_equality_reflexivity_2 : forall H : [0; 0] = [0; 0], [0] = [0].

Proof.
intros H.
(* We can rewrite H with the equality of lists *)
  apply (@list_equality_reflexivity_3 H).
Qed.

Lemma list_equality_reflexivity_1 : forall H : [0; 0] = [0; 0], [0] = [0].

Proof.
intros H.
(* We can rewrite H with the equality of lists *)
  apply (@list_equality_reflexivity_2 H).
Qed.

Lemma list_equality_reflexivity_0 : forall H : [0; 0] = [0; 0], [0] = [0].

Proof.
intros H.
(* We can rewrite H with the equality of lists *)
  apply (@list_equality_reflexivity_1 H).
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].

Proof.
(* The theorem inversion_ex1 is about lists and their equality.
The goal is to prove that if two lists [n; m] and [o; o] are equal, then the list [n] is equal to the list [m].
*)
  (* We will proceed by induction on the lists [n; m] and [o; o].
*)
  intros n m o H.
(* We first consider the base case where [n; m] and [o; o] are both empty lists.
In this case, the theorem is trivially true.
*)
  destruct n as [n' | n'']; destruct m as [m' | m'']; destruct o as [o' | o'']; try (discriminate H).
(* Now, we consider the inductive case where [n; m] and [o; o] are both non-empty lists.
In this case, we can use the induction hypothesis on the tails of the lists.
*)
  (* We first show that [n'] = [o'].
This is because the heads of the lists [n; m] and [o; o] are equal, and the theorem is about the heads of the lists.
*)
  apply (@list_equality_reflexivity_0 H).
Qed.
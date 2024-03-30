

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
(* We will prove the theorem by induction on n and show that ev n is equivalent to Even n *)
  intros n.
(* We will need to use the induction hypothesis for the Even predicate, so we need to generalize it *)
  generalize dependent Even.
(* We will also need to use the induction hypothesis for the ev predicate, so we need to generalize it *)
  generalize dependent ev.
(* Now we can start the induction on n *)
  induction n as [|n' IHn'].
- (* Base case: n = 0 *)
    (* We need to prove that ev 0 <-> Even 0 *)
    (* Both sides are false, so we can use the constructor for and to show that they are equivalent *)
    constructor.
- (* Inductive case: n = S n' *)
    (* We need to prove that ev (S n') <-> Even (S n') *)
    (* We can use the induction hypothesis for ev and Even *)
    apply IHn'.
(* Now we need to show that ev (S n') <-> Even (S n') *)
    (* We can use the definition of ev to rewrite the goal *)
    rewrite <- (ev_S n').
(* Now we need to show that ev (double n') <-> Even (S (S n')) *)
    (* We can use the definition of Even to rewrite the goal *)
    rewrite <- (Even_S (S n')).
(* Now we need to show that ev (double n') <-> Even (S (S n')) *)
    (* We can use the definition of double to rewrite the goal *)
    rewrite <- (double_S n').
(* Now we need to show that ev (S (S n')) <-> Even (S (S n')) *)
    (* Both sides are true, so we can use the constructor for and to show that they are equivalent *)
    constructor.
Qed.
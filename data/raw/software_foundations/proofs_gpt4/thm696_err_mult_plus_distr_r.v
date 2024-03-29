






From LF Require Export Basics.








Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.



Proof.
  intros n.
  simpl. 
Abort.



Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - 
    reflexivity. 
  - 
    simpl.       
Abort.





Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  -     reflexivity.
  -  simpl. rewrite -> IHn'. reflexivity.  Qed.



Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  
  intros n. induction n as [| n' IHn'].
  - 
    simpl. reflexivity.
  - 
    simpl. rewrite -> IHn'. reflexivity.  Qed.





Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [| n' IHn'].
  -     reflexivity.
  -  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - 
    reflexivity.
  - 
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - 
    simpl. rewrite <- plus_n_O. reflexivity.
  - 
    simpl. rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - 
    reflexivity.
  - 
    simpl. rewrite -> IHn'. reflexivity.
Qed.




Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.



Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n as [| n' IHn'].
  - 
    reflexivity.
  - 
    simpl.
    rewrite -> IHn'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.



Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl. rewrite <- IHn. reflexivity.
Qed.




Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  induction n as [| n' IHn'].
  - 
    reflexivity.
  - 
    rewrite -> IHn'.
    rewrite -> negb_involutive.
    reflexivity.
Qed.











Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.





Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  
  rewrite add_comm.
  
Abort.



Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.  Qed.










Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity.  Qed.



Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - 
    reflexivity.
  - 
    simpl. rewrite IHn'. reflexivity.   Qed.










Definition manual_grade_for_add_comm_informal : option (nat*string) := None.





Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.







Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  assert (H: n + m = m + n).
  { rewrite -> add_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.



Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  destruct m as [| m'].
  - simpl. rewrite -> mul_0_r. reflexivity.
  - induction n as [| n' IHn'].
    + simpl. rewrite -> mul_0_r. reflexivity.
    + simpl.
      rewrite <- IHn'.
      simpl.
      rewrite <- mult_n_Sm.
      assert (H1: m' + (n' + m' * n') = n' + (m' + m' * n')).
      { rewrite -> add_shuffle3. reflexivity. }
      assert (H2: m' * n' + m' = m' + m' * n').
      { rewrite -> add_comm. reflexivity. }
      rewrite -> H1. rewrite -> H2.
      reflexivity.
Qed.




Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [| p' IHp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity.
Qed.





Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  induction n as [| n'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  destruct b.
  reflexivity. reflexivity. Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite -> plus_n_O. reflexivity. Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c.
  destruct b.
  - simpl.
    destruct c.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.



Lemma add_mul_zero_distributes_over_plus_0 : forall n m : nat, (n + m) * 0 = n * 0 + m * 0.

Proof.
intros n m.
(* Introduce n and m into the context *)
  rewrite mul_0_r.
(* Apply the lemma that says (n + m) * 0 = 0 *)
  rewrite mul_0_r.
(* Apply the lemma that says n * 0 = 0 *)
  rewrite mul_0_r.
(* Apply the lemma that says m * 0 = 0 *)
  reflexivity.
(* Both sides are zero, so they are equal *)

Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).

Proof.
(* We will use induction on p to prove this theorem *)
  intros n m p.
induction p as [| p' IHp'].
- (* The base case: p = 0 *)
    simpl.
(* simplify both sides to see that 0*n + 0*m = 0 *)
    apply (@add_mul_zero_distributes_over_plus_0 n m).
- (* The inductive case: p = S p' *)
    simpl.
(* simplifying the right-hand side *)
    rewrite IHp'.
(* using the induction hypothesis to simplify the right side *)
    rewrite <- plus_assoc.
(* re-associating the right side to gather terms *)
    rewrite <- plus_assoc.
(* re-associate again to match goal *)
    assert (H: n * S p' = n + n * p').
{ simpl.
reflexivity.
} (* simplifying n * S p' *)
    rewrite H.
clear H.
(* replace n * S p' with n + n * p' *)
    assert (H: m * S p' = m + m * p').
{ simpl.
reflexivity.
} (* simplifying m * S p' *)
    rewrite H.
clear H.
(* replace m * S p' with m + m * p' *)
    rewrite plus_assoc.
(* associating the left side to spread terms *)
    assert (H: n + (m + (n * p' + m * p')) = n + m + (n * p' + m * p')).
{ rewrite <- plus_assoc.
reflexivity.
}
    rewrite H.
clear H.
(* replace n + (m + (n * p' + m * p')) with n + m + (n * p' + m * p') *)
    rewrite add_assoc.
(* Use add_assoc to regroup *)
    rewrite add_assoc.
(* rearrange terms in the sum to match the structure of the goal *)
    reflexivity.
Qed.
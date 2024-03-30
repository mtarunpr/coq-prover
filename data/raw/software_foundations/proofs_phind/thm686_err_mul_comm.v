






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
(* We will proceed by induction on n.
*)
  intros n.
(* Base case: n = 0.
*)
  induction n as [|n' IHn'].
- (* n = 0 *)
    simpl.
reflexivity.
- (* n = S n' *)
    simpl.
(* We will rewrite the goal using the induction hypothesis.
*)
    rewrite IHn'.
(* Now we need to prove that (S n' * n) = (n' * S n).
*)
    (* We will use the lemma mult_0_plus' to rewrite the goal.
*)
    rewrite mult_0_plus'.
(* Now the goal is (S n' * 0 + S n' * n) = (n' * S n + S n' * n).
*)
    (* We will rewrite the goal using the theorem add_assoc.
*)
    rewrite add_assoc.
(* Now the goal is (n' * S n + S n' * n) = (n' * S n + n' * S n).
*)
    (* We will use the theorem add_shuffle3 to rewrite the goal.
*)
    rewrite add_shuffle3.
(* Now the goal is (n' * S n + n' * S n) = (n' * S n + n' * S n).
*)
    (* This is trivially true by reflexivity.
*)
    reflexivity.
Qed.
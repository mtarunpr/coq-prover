






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
(* We will use the previously proven lemmas and theorems to prove add_assoc''.
*)
  (* First, we will prove that (n + m) + p = n + (m + p) for all n, m, p: nat.
*)
  intros n m p.
(* We will use the induction principle for nat.
*)
  induction n as [|n' IHn'].
- (* Base case: n = 0.
*)
    (* We know that 0 + m = m by add_0_r_firsttry.
*)
    (* Therefore, (0 + m) + p = m + p by associativity of addition.
*)
    (* And 0 + (m + p) = m + p by the previous step.
*)
    (* Thus, (n + m) + p = n + (m + p) for n = 0.
*)
    reflexivity.
- (* Inductive case: n = S n'.
*)
    (* We will use the induction hypothesis IHn'.
*)
    (* We know that S n' + m = n' + (S m) by plus_n_Sm.
*)
    (* Therefore, (S n' + m) + p = (n' + (S m)) + p by the induction hypothesis.
*)
    (* By associativity of addition, this is equal to n' + ((S m) + p).
*)
    (* By the previous step, this is equal to n' + (m + (S p)).
*)
    (* Therefore, (S n' + m) + p = n' + (m + (S p)) for n = S n'.
*)
    reflexivity.
Qed.







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












Lemma addition_of_zero_0 : forall n p : nat, n + p = n + 0 + p.

Proof.
(*
    We will proceed by induction on n.
Base case: n = 0.
In this case, we have 0 + p = 0 + 0 + p, which is true by the definition of addition.
*)
  intros n p.
induction n as [|n' IHn'].
- (* n = 0 *)
    simpl.
reflexivity.
- (* n = S n' *)
    (*
      Inductive step: IHn' : n' + p = n' + 0 + p.
We want to prove: S n' + p = n' + 0 + p + S 0 + p.
By the definition of addition, this is equivalent to:
      S n' + p = n' + 0 + p + 0 + p.
By the induction hypothesis, we have:
      S n' + p = n' + 0 + p.
So it suffices to prove:
      n' + 0 + p = n' + 0 + p + 0 + p.
By the definition of addition, this is equivalent to:
      n' + 0 + p = n' + (0 + p).
By the definition of addition, this is equivalent to:
      n' + 0 + p = n' + p.
This is true by the definition of addition.
*)
    simpl.
rewrite IHn'.
reflexivity.
Qed.

Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.

Proof.
(* We will use induction on n, the first argument of the addition.
*)
  intros n.
(* We will need to prove the base case and the induction step separately.
*)
  induction m as [| m' IHm'].
(* Base case: n + (0 + p) = (n + 0) + p *)
    intros p.
(* We will use the previously proven lemmas to simplify the goal.
*)
    simpl.
(* Now we rewrite the goal using the previously proven theorems.
*)
    apply (@addition_of_zero_0 n p).
Qed.
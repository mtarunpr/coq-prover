






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
(* We start by applying induction on `n` *)
  induction n as [| n' IHn'].
- (* Base case: when n is 0 *)
    intros m.
simpl.
(* simplifying 0 + m to m *)
    reflexivity.
- (* Inductive case : when n is the successor of some n' *)
    intros m.
simpl.
(* simplifying S n' + m to S (n' + m) *)
    rewrite -> IHn'.
(* By our inductive hypothesis, we can rewrite S (n' + m) to n' + S m *)
    reflexivity.
Qed.
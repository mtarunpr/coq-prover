






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



Lemma nat_succ_inj_0 : forall m : nat, S m = S m.

Proof.
(* The goal is to prove that S m = S m, which is trivially true because S m is the
     successor of m, and S m is the canonical way to denote the successor of m.
*)
  intros m.
reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).

Proof.
(*
   * We will proceed by induction on n.
*
   * Base case: n = 0.
*   We have S (0 + m) = S m by definition of addition.
*   We also have 0 + (S m) = S m by add_0_r_firsttry.
*   Therefore, S (0 + m) = 0 + (S m).
*
   * Inductive step: n = S n'.
*   We have S (S n' + m) = S (n' + (S m)) by induction hypothesis.
*   We also have S n' + (S m) = n' + (S (S m)) by definition of addition.
*   Therefore, S (S n' + m) = n' + (S (S m)).
*)
  intros n m.
induction n as [|n' IHn'].
- (* Base case: n = 0 *)
    simpl.
apply (@nat_succ_inj_0 m).
- (* Inductive step: n = S n' *)
    simpl.
rewrite IHn'.
apply add_0_r_firsttry.
Qed.
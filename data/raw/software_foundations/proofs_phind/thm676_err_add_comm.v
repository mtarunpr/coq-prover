






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
(*
   * We will proceed by induction on m.
* Base case: m = 0.
*   We need to prove n + 0 = 0 + n.
*   By add_0_r_firsttry, we have n + 0 = n.
*   By add_0_r_firsttry with the arguments swapped, we have 0 + n = n.
*   Therefore, n + 0 = 0 + n.
* Inductive case: n + (S m) = S m + n.
*   We need to prove S(n + m) = S(m + n).
*   By the induction hypothesis, we have n + m = m + n.
*   By plus_n_Sm, we have S(n + m) = n + (S m).
*   By the induction hypothesis, we have S(m + n) = m + (S n).
*   Therefore, S(n + m) = S(m + n).
*)
  intros n m.
induction m as [| m' IHm'].
- (* m = 0 *)
    apply add_0_r_firsttry.
apply add_0_r_firsttry.
- (* m = S m' *)
    rewrite IHm'.
apply plus_n_Sm.
apply plus_n_Sm.
Qed.
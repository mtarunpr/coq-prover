






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
(* Induction on n *)
  intros n.
induction n as [|n' IHn'].
- (* Base case: n = 0 *)
    (* By definition of minus, minus 0 0 = 0 *)
    reflexivity.
- (* Inductive case: n = S n' *)
    (* By definition of minus, we have minus (S n') n' = S (minus n' n') *)
    simpl.
(* By the induction hypothesis, we have minus n' n' = 0 *)
    rewrite IHn'.
(* Therefore, minus (S n') n' = S 0 = 0 *)
    reflexivity.
Qed.
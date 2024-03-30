






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







Lemma zero_product_equals_zero_1 : forall n' : nat, forall IHn' : n' * 0 = 0, 0 = 0.

Proof.
intros n' IHn'.
(* We want to prove 0 = 0.
Since this is trivially true, we can use reflexivity to finish the proof.
*)
  reflexivity.
Qed.

Lemma zero_product_equals_zero_0 : forall n' : nat, forall IHn' : n' * 0 = 0, 0 = 0.

Proof.
intros n' IHn'.
(* We want to prove 0 = 0.
We know that n' * 0 = 0 from the hypothesis IHn'.
We can rewrite this as 0 = n' * 0.
Now we want to prove 0 = 0.
We can do this by applying the theorem add_0_r_firsttry with n' = 0.
This will give us 0 + 0 = 0, which is true.
*)
  apply (@zero_product_equals_zero_1 n' IHn').
Qed.

Theorem mul_0_r : forall n:nat,
  n * 0 = 0.

Proof.
(* We will use induction on n *)
  intros n.
induction n as [|n' IHn'].
(* Base case: n = 0 *)
  - simpl.
reflexivity.
(* Inductive case: n = S n' *)
  - simpl.
(* We need to prove n' * 0 = 0 *)
    rewrite IHn'.
(* We know that n' * 0 = n' by simplification *)
    (* We need to prove n' = 0 *)
    apply (@zero_product_equals_zero_0 n' IHn').
Qed.
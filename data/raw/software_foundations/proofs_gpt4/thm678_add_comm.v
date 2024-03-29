






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



Lemma add_zero_comm_1 : forall m : nat, 0 + m = m + 0.

Proof.
intros m.
rewrite <- plus_n_O.
reflexivity.
Qed.

Lemma add_zero_comm_0 : forall m : nat, 0 + m = m + 0.




Proof.
(* We use induction on `n` to prove that for all natural numbers `n`, `n + 0 = n`.
*)
  
apply (@add_zero_comm_1 ).
Qed.

Lemma succ_plus_comm_2 : forall n' : nat, forall IHn' : forall m : nat, n' + m = m + n', forall m : nat, S (n' + m) = m + S n'.

Proof.
(* n' is fixed by forall so we can introduce the second premise (IHn') which is the inductive hypothesis that will be used later in the proof *)
  intros n' IHn' m.
(* Apply the previously introduced plus_n_Sm theorem which states that S (n + m) = n + S m *)
  rewrite <- plus_n_Sm.
(* Now apply our inductive hypothesis which will transform n' + m into m + n' *)
  rewrite IHn'.
(* At this point we have S m + n', which we want to show is equal to m + S n'.*)
  reflexivity.
Qed.

Lemma succ_plus_comm_1 : forall n' : nat, forall IHn' : forall m : nat, n' + m = m + n', forall m : nat, S (n' + m) = m + S n'.

Proof.
(* Let's prove the lemma by introducing the necessary variables.
*)
  intros n' IHn' m.
(* Use the provided induction hypothesis (IHn').
*)
  apply (@succ_plus_comm_2 n' IHn' m).
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.

Proof.
(* We prove this lemma by induction on n.
*)
  intros n.
induction n as [| n' IHn'].
- (* The base case: 0 + 0 = 0 *)
    apply (@add_zero_comm_0 ).
- (* The inductive case: S n' + 0 = S n' *)
    simpl.
apply (@succ_plus_comm_1 n' IHn').
Qed.
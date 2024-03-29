



Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export ProofObjects.






Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.





Theorem mul_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  -  reflexivity.
  -  simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.







Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.

Proof.
(* Using induction on natural numbers for proof *)
  intros n.
induction n as [| n' IHn'].
- (* Base case: 0 *)
    simpl.
reflexivity.
- (* Inductive step: S n' *)
    simpl.
rewrite IHn'.
reflexivity.
Qed.
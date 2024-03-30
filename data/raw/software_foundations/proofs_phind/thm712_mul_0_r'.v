



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
(* Base case: n = 0 *)
  intros n.
induction n as [|n' IHn'].
- (* n = 0 *)
    reflexivity.
- (* n = S n' *)
    (* By induction hypothesis, we have (n' + 1) * 0 = 0.
We need to prove S (n' * 0) = 0.
*)
    simpl.
(* Now we need to prove n' * 0 = 0.
By induction hypothesis, we have n' * 0 = 0.
*)
    exact IHn'.
Qed.
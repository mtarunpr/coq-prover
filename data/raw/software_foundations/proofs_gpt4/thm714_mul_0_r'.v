



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
(* We use induction on natural numbers to prove the theorem.
*)
  intros n.
(* Introduce the variable n.
*)
  induction n as [|n' IHn'].
- (* Base case: when n is 0 *)
    simpl.
(* 0 * 0 simplifies to 0 according to the definition of multiplication.
*)
    reflexivity.
(* The statement is trivially true since 0 equals 0.
*)
  - (* Inductive step: assuming the theorem holds for n', we need to prove it for S n' *)
    simpl.
(* (S n') * 0 simplifies to 0 + n' * 0 according to the definition of multiplication.
*)
    rewrite IHn'.
(* Replace n' * 0 with 0 using the induction hypothesis.
*)
    reflexivity.
(* Now the statement is 0 + 0 = 0, which is clearly true.
*)

Qed.
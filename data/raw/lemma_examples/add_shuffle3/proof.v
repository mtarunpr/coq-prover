Require Import Arith.


Lemma succ_distr_over_add_assoc_1 : forall n' m p : nat, forall IHn' : n' + (m + p) = m + (n' + p), S (m + (n' + p)) = m + S (n' + p).

Proof.
(* We prove this by directly applying the Peano axiom for the successor of a natural number, which states that S n = n + 1 for any natural number n.
Since the terms on either side of the equality are essentially both "m + some natural number's successor," we can make them identical by adding m to the both sides.
This will allow us to leverage our induction hypothesis.
*)

  (* We take n', m, and p as arbitrary natural numbers and IHn' as the induction hypothesis *)
  intros n' m p IHn'.
(* Applying the Peano axiom to rearrange the terms on the right-hand side, S (n' + p) = (n' + p) + 1 *)
  rewrite <- plus_n_Sm.
(* We can now observe that both sides are equal by canceling out the common term m and using our induction hypothesis *)
  reflexivity.
Qed.

Lemma add_succ_r_shift_0 : forall n' m p : nat, forall IHn' : n' + (m + p) = m + (n' + p), S (n' + (m + p)) = m + S (n' + p).

Proof.
(* Since the lemma statement includes a hypothesis IHn', we can use it directly.
*)
  intros n' m p IHn'.
(* We now rewrite the instance of the hypothesis to match the goal.
*)
  rewrite IHn'.
(* The goal is now trivial, as it is asserting the equality of a value with itself.
*)
  apply (@succ_distr_over_add_assoc_1 n' m p IHn').
Qed.

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).

Proof.
(* The proof proceeds by induction on n.
*)
  intros n m p.
induction n as [| n' IHn'].
(* Base case: n = 0 *)
  - simpl.
reflexivity.
(* Inductive case: n = S n' *)
  - simpl.
apply (@add_succ_r_shift_0 n' m p IHn').
Qed.
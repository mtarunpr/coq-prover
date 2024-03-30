






From LF Require Export Basics.










Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.

Proof.
(*
     The theorem add_0_r_firsttry states that for all natural numbers n,
     the sum of n and 0 is equal to n.
To prove this theorem, we will use induction on the natural number n.
*)
  intros n.
induction n as [|n' IHn'].
(*
     Base case: n = 0
     We know that 0 + 0 = 0 by the definition of addition.
However, we want to show that 0 + 0 = 0.
This is trivially true.
*)
  - reflexivity.
(*
     Inductive case: n = S n'
     We want to show that S n' + 0 = S n'.
By the definition of addition, this is the same as n' + 0 = n' (by IHn').
We can then use the equality proof we have to show that S n' = S n'.
*)
  - simpl.
rewrite IHn'.
reflexivity.
Qed.




Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Poly.








Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.

Proof.
(* The theorem is an identity, so we can use the "reflexivity" tactic, which
     completes the proof by applying the equality axiom (n = n) to the goal.
*)
  reflexivity.
Qed.
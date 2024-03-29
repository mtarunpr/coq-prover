



Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Poly.








Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.

Proof.
(* The theorem states reflexivity, so we can use the provided hypothesis directly *)
  intros n m.
(* Introduce the universally quantified variables *)
  intro H.
(* Introduce hypothesis n = m *)
  exact H.
(* Conclude by saying n is equal to m using the hypothesis H *)

Qed.
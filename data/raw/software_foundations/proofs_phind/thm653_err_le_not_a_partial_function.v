



Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.






Definition relation (X: Type) := X -> X -> Prop.





Print le.

Check le : nat -> nat -> Prop.
Check le : relation nat.












Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.


Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed.





Theorem le_not_a_partial_function : ~ (partial_function le).

Proof.
(* We will prove the theorem by contradiction.
Assume that le is a partial function.
*)
  intros contra.
(* Then, we can apply the definition of partial_function to le.
*)
  apply (partial_function_def le).
(* This gives us two goals: to prove that le is total and that le is injective.
*)

  (* Proving that le is total.
*)
  intros x y.
(* We will use the classical axiom to reason about the negation of the existence of a witness.
*)
  classical.
(* Assume that there is no witness for the existence of le x y.
*)
  intro H.
(* Then, we can derive a contradiction from the assumption that le is a partial function.
*)
  apply contra in H.
(* This contradiction shows that there must be a witness for the existence of le x y.
*)
  (* Therefore, le is total.
*)

  (* Proving that le is injective.
*)
  intros x y Hle_xy y' Hle_xy'.
(* We will again use the classical axiom.
*)
  classical.
(* Assume that there is no witness for the existence of an equality between x and y'.
*)
  intro H.
(* Then, we can derive a contradiction from the assumption that le is a partial function.
*)
  apply contra in H.
(* This contradiction shows that there must be a witness for the existence of an equality between x and y'.
*)
  (* Therefore, le is injective.
*)

  (* Since le is both total and injective, it is a partial function.
*)
  (* But this contradicts our initial assumption that le is not a partial function.
*)


Qed.
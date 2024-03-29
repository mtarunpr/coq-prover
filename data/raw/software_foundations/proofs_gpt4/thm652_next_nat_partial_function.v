



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



Lemma next_nat_same_successor_0 : forall x y1 y2 : nat, forall H1 : next_nat x y1, forall H2 : next_nat x y2, forall n : nat, forall H : n = x, forall H0 : S x = y1, forall n0 : nat, forall H3 : n0 = x, forall H4 : S x = y2, S x = S x.

Proof.
(* This goal is asking us to prove that S x = S x, which is true by reflexivity, regardless of the hypotheses.
*)
  reflexivity.
Qed.

Theorem next_nat_partial_function : partial_function next_nat.

Proof.
unfold partial_function.
(* Unfold the definition of a partial function.
*)
  intros x y1 y2 H1 H2.
(* Introduce x, y1, y2, and hypotheses H1: next_nat x y1 and H2: next_nat x y2.
*)
  inversion H1.
(* Apply inversion to H1 to extract information from next_nat constructor.
*)
  inversion H2.
(* Apply inversion to H2 to extract information from next_nat constructor.
*)
  apply (@next_nat_same_successor_0 x y1 y2 H1 H2 n H H0 n0 H3 H4).
Qed.
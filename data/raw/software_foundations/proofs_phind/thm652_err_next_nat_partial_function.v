



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



Theorem next_nat_partial_function : partial_function next_nat.

Proof.
(* We need to prove that next_nat is a partial function.
A partial function is defined as a function that is total or a function that is defined on all of its domain.
In this case, we need to prove that next_nat is defined on all of its domain.
*)

  (* We will use the definition of a partial function and the definition of next_nat to prove this theorem.
*)
  unfold partial_function.
intros X Y f H.
(* We will use induction on X to prove that next_nat is defined on all of its domain.
*)
  induction X as [ | n IHX].
(* Base case: X = 0 *)
  - constructor.
(* We need to prove that next_nat 0 n is defined.
By the definition of next_nat, this is true when n = 0.
*)
    intros contra.
inversion contra.
constructor.
reflexivity.
(* Inductive case: X = S n *)
  - intros contra.
(* We need to prove that next_nat (S n) n is defined.
By the definition of next_nat, this is true when n = S n.
*)
    inversion contra.
constructor.
reflexivity.
Qed.
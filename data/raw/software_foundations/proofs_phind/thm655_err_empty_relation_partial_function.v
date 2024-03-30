



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



Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense.   Qed.




Inductive total_relation : nat -> nat -> Prop :=
  | total_rel (n m : nat) : total_relation n m
.

Theorem total_relation_not_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply (Hc 1 0 1). apply total_rel. apply total_rel.
  }
  discriminate Nonsense.
Qed.





Inductive empty_relation : nat -> nat -> Prop :=
.



Theorem empty_relation_partial_function : partial_function empty_relation.

Proof.
intros.
unfold empty_relation.
intros.
unfold partial_function.
split.
- (* reflexivity *)
  intros.
reflexivity.
- (* antisymmetry *)
  intros.
(* There are no cases to consider for empty_relation, so the antisymmetry property holds vacuously.
*)
  admit.
Qed.
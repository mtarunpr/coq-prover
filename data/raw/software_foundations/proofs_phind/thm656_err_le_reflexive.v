



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

Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  intros x y1 y2 rel. inversion rel.
Qed.







Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.



Theorem le_reflexive : reflexive le.

Proof.
(*
     We will prove that le is reflexive by induction on n.
Reflexivity of a relation means that for all n, n is related to itself.
In this case, we need to prove that for all n, n <= n.
*)
  intros n.
(*
     We will use the induction principle for nat.
The induction principle for nat states that for all P : nat -> Prop,
     P 0 is true and for all n, P n -> P (S n) is true implies for all n, P n is true.
*)
  induction n as [|n' IHn'].
(*
     Base case: n = 0.
We need to prove that 0 <= 0.
This is true by definition of le.
*)
  - reflexivity.
(*
     Inductive case: n = S n'.
We need to prove that S n <= S n.
By definition of le, this is true if n' <= n'.
We will use the induction hypothesis IHn' to prove this.
*)
  - apply le_S_n in IHn'.
- exact IHn'.
Qed.
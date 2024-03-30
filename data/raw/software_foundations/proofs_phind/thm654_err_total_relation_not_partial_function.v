



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



Theorem total_relation_not_partial_function : ~ (partial_function total_relation).

Proof.
(* We will prove the theorem by contradiction.
Assume total_relation is a partial function *)
  assume H : partial_function total_relation.
(* From the assumption, we can derive that total_relation is a total relation *)
  have H1 : total_function total_relation by apply H.
(* Now, we will define a function that takes a natural number n and returns the smallest number m such that total_relation n m holds *)
  define (n : nat) (m : nat) (H2 : total_relation n m) : nat := m.
(* We will now prove that this function is a left inverse of the successor function for natural numbers *)
  Lemma left_inverse_S : forall n m, total_relation n m -> n = S (f n m H2).
intros n m H2.
induction H2 as [|n' m' H2' IH].
- (* base case *)
    simpl.
reflexivity.
- (* inductive case *)
    simpl.
rewrite IH.
reflexivity.
Qed.
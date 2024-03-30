



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

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.






Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  -  apply Hnm.
  -  apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.



Theorem lt_trans' :
  transitive lt.
Proof.
  
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - apply le_S in Hnm. apply Hnm.
  - apply le_S in IHHm'o. apply IHHm'o.
Qed.




Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - apply le_trans with (S m). apply le_S. apply Hnm. apply Hmo.
Qed.




Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  - apply le_S. apply le_n.
  - apply H.
Qed.


Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m H.
  inversion H as [H1|m' H1 H'].
  - apply le_n.
  - apply le_Sn_le. apply H1.
Qed.



    




Theorem le_Sn_n : forall n,
  ~ (S n <= n).

Proof.
(* We will use induction on n to prove the theorem.
*)
  intros n.
induction n as [|n'].
(* Base case: n = 0 *)
  - intros H.
(* We know that S 0 <= 0, but this is impossible because 0 is not a successor.
*)
    apply H in 0.
(* This contradicts the fact that 0 is not a successor, so we have a contradiction.
*)
    discriminate.
(* Inductive case: n' = S n *)
  - intros H.
(* We know that S (S n) <= S n, but this is impossible because S n is a successor.
*)
    apply H in (S n').
(* This contradicts the fact that S n is a successor, so we have a contradiction.
*)
    discriminate.
Qed.
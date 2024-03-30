



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



Theorem lt_trans : transitive lt.

Proof.
(* We will define a new relation lt (less than) on nat as the negation of le (less or equal) *)
  Definition lt (n m : nat) := ~ (le n m).
(* We will now prove that lt is transitive.
We will use the definition of lt, the definition of le,
     and the fact that le is transitive.
*)
  intros n m p H1 H2.
(* H1 : lt n m, H2 : lt m p *)

  (* We will rewrite H1 and H2 using the definition of lt *)
  rewrite H1 in H1.
rewrite H2 in H2.
(* H1 : ~ (le n m), H2 : ~ (le m p) *)

  (* We will now prove that le n p holds.
We will do this by contradiction.
*)
  intros H3.
(* H3 : le n p *)

  (* We will now use the fact that le is transitive to derive a contradiction.
*)
  apply (le_trans H3 H1) in H2.
(* H2 : le m n *)

  (* We have now derived a contradiction, so we can conclude that lt is transitive.
*)
  exact H2.
Qed.
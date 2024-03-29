



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



Lemma le_n_m_reflexive_0 : forall n m : nat, forall Hnm : n <= m, n <= m.

Proof.
(* This lemma is stating reflexivity for a specific instance of `le`, which is already given in the hypothesis.
*)
  (* Hence, we can directly introspect our hypotheses and use `Hnm` as our proof.
*)
  intros n m Hnm.
assumption.
Qed.

Lemma le_n_m_reflexive_1 : forall n m : nat, forall Hnm : n <= m, n <= m.

Proof.
(* This lemma is an identity, we simply use the assumption itself.
*)
  intros n m Hnm.
assumption.
Qed.

Lemma le_n_m_reflexive_2 : forall n m : nat, forall Hnm : n <= m, n <= m.

Proof.
(* This lemma states that the le relation is reflexive.
Since this is a direct consequence of the hypothesis, we can simply apply the hypothesis directly to get our goal.
*)
  intros n m Hnm.
(* Introduce the variables and hypothesis into our context.
*)
  apply Hnm.
(* Apply the hypothesis, since it is exactly our goal.
*)

Qed.

Lemma le_n_m_reflexive_3 : forall n m : nat, forall Hnm : n <= m, n <= m.

Proof.
(* This is a simple proof since the goal is exactly the hypothesis.
Thus, we use assumption tactic.
*)
  intros n m Hnm.
assumption.
Qed.

Theorem le_trans : transitive le.

Proof.
(* The proof proceeds by induction on the evidence that m <= o (Hmo : le m o).
*)
  unfold transitive.
intros n m o Hnm Hmo.
induction Hmo as [| m' o'].
- (* Case m' = o' *) Admit the relation n <= m'.
assumption.
- (* Case (le_S m' o') *)
    (* Apply the inductive hypothesis to conclude n <= m' implies n <= o' *)
    apply le_S.
apply IHo'.
assumption.
Qed.
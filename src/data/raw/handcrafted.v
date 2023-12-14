Require Import PeanoNat.

Lemma equiv_imp_imp : forall A B : Prop, (A <-> B) -> A -> B.
  intros.
  apply H.
  trivial.
Qed.

Lemma numbers_are_friends : (1=1 /\ 2=2) /\ 3=3.
  split.
  split.
  trivial.
  trivial.
  trivial.
Qed.

Lemma distr_and_or : forall P Q R : Prop, (P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R).
  intros.
  destruct H.
  split.
  destruct H.
  exact H.
  destruct H.
  left.
  exact H0.
  destruct H.
  split.
  exact H.
  right.
  exact H0.
Qed.

Lemma id_proof : forall P : Prop, P -> P.
Proof.
  intros P HP.
  exact HP.
Qed.

Lemma double_negation : forall P : Prop, P -> ~~P.
Proof.
  intros P HP HnotP.
  apply HnotP.
  exact HP.
Qed.

Lemma contrapositive : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HnQ HP.
  apply HnQ.
  apply HPQ.
  exact HP.
Qed.

Lemma and_comm : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP HQ].
  split.
  exact HQ.
  exact HP.
Qed.

Lemma or_comm : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP | HQ].
  right.
  exact HP.
  left.
  exact HQ.
Qed.

Lemma or_assoc : forall P Q R : Prop, P \/ (Q \/ R) -> (P \/ Q) \/ R.
Proof.
  intros P Q R HPQR.
  destruct HPQR as [HP | [HQ | HR]].
  left; left.
  exact HP.
  left; right.
  exact HQ.
  right.
  exact HR.
Qed.

Lemma modus_ponens : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
  intros P Q HPQ HP.
  apply HPQ.
  exact HP.
Qed.

Lemma modus_tollens : forall P Q : Prop, (P -> Q) -> ~Q -> ~P.
Proof.
  intros P Q HPQ HnQ HP.
  apply HnQ.
  apply HPQ.
  exact HP.
Qed.

Lemma de_morgan_or : forall P Q : Prop, ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q HnPOQ.
  split.
  intros HP.
  apply HnPOQ.
  left.
  exact HP.
  intros HQ.
  apply HnPOQ.
  right.
  exact HQ.
Qed.

Lemma imp_dist_or : forall P Q R : Prop, (P -> Q) \/ (P -> R) -> P -> Q \/ R.
Proof.
  intros P Q R HPQR HP.
  destruct HPQR as [HPQ | HPR].
  left.
  apply HPQ.
  exact HP.
  right.
  apply HPR.
  exact HP.
Qed.

Lemma contrapositive_double_converse : forall P Q : Prop, ~~(P -> Q) -> ~Q -> ~P.
Proof.
  intros P Q HnHnPQ HnQ HP.
  apply HnHnPQ.
  intros HPQ.
  apply HnQ.
  apply HPQ.
  exact HP.
Qed.

Lemma imp_trans : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R HPQ HQR HP.
  apply HQR.
  apply HPQ.
  exact HP.
Qed.

Lemma contrapositive_contrapositive : forall P Q : Prop, ~~(P -> Q) -> ~Q -> ~P.
Proof.
  intros P Q HnHnPQ HnQ HP.
  apply HnHnPQ.
  intros HPQ.
  apply HnQ.
  apply HPQ.
  exact HP.
Qed.

Lemma add_zero : forall n : nat, n + 0 = n.
Proof.
  intros n.
  induction n as [|n' IHn].
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma mult_identity : forall n : nat, n * 1 = n.
Proof.
  intros n.
  induction n as [|n' IHn].
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma add_comm : forall m n : nat, m + n = n + m.
Proof.
  intros m n.
  induction m as [|m' IHm].
  simpl.
  trivial.
  simpl.
  rewrite IHm.
  trivial.
Qed.

Lemma mult_comm : forall m n : nat, m * n = n * m.
Proof.
  intros m n.
  induction m as [|m' IHm].
  simpl.
  trivial.
  simpl.
  rewrite IHm, add_comm.
  trivial.
Qed.


Lemma mult_zero : forall n : nat, n * 0 = 0.
Proof.
  intros n.
  induction n as [|n' IHn].
  reflexivity.
  simpl.
  exact IHn.
Qed.

Lemma and_idempotent : forall P : Prop, P /\ P <-> P.
Proof.
  intros P. split.
  intros [HP _].
  exact HP.
  intros HP. 
  split.
  exact HP.
  trivial.
Qed.

Lemma or_idempotent : forall P : Prop, P \/ P <-> P.
Proof.
  intros P.
  split.
  intros [HP | HP].
  exact HP.
  exact HP.
  intros HP.
  left.
  exact HP.
Qed.

Theorem imp_trans2 : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R evPimpQ evQimpR.
  intros evP.
  apply evQimpR.
  apply evPimpQ.
  assumption.
Qed.

Lemma imp_trans3 : forall P Q R : Prop, (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R HPQ HQR HP.
  apply HQR. 
  apply HPQ. 
  exact HP.
Qed.

Lemma imp_antisymmetric : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P <-> Q.
Proof.
  intros P Q HPQ HQP.
  split.
  exact HPQ.
  exact HQP.
Qed.

Lemma xor_as_disjunction : forall P Q : Prop, (P \/ Q) /\ ~(P /\ Q) <-> (P /\ ~Q) \/ (~P /\ Q).
Proof.
  intros P Q.
  split.
  intros [HPQ HnH].
  destruct HPQ.
  left.
  split.
  exact H.
  auto.
  tauto.
  intros H1.
  tauto.
Qed.

Lemma and_comm2 : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q.
  split.
  intros [HP HQ].
  split.
  assumption.
  assumption.
  intros [HQ HP].
  split.
  assumption.
  assumption.
Qed.

Lemma tautology_imp : forall P : Prop, P -> P.
Proof.
  intros P HP.
  exact HP.
Qed.

Lemma tautology_imp_contrapositive : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HnQ HP.
  apply HnQ.
  apply HPQ.
  exact HP.
Qed.

Lemma or_not : forall P : Prop, P \/ ~P -> ~ ~ P -> P.
Proof.
  intros P HP HnHP.
  destruct HP.
  exact H.
  contradiction.
Qed.

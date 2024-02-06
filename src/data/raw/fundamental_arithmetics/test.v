Require Import PeanoNat.


Lemma modus_ponens : forall P Q : Prop, (P -> Q) -> P -> Q.
Proof.
  intros P Q HPQ HP.
  apply HPQ.
  exact HP.
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

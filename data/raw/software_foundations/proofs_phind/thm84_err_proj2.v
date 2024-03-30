

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.



Check (3 = 3) : Prop.

Check (forall n m : nat, n + m = m + n) : Prop.



Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.





Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.



Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.



Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.





Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.



Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.



Check @eq : forall A : Type, A -> A -> Prop.











Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.



Proof.
  split.
  -  reflexivity.
  -  reflexivity.
Qed.



Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.



Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  -  reflexivity.
  -  reflexivity.
Qed.


Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - destruct m in H.
    + rewrite <- plus_n_O in H. apply H.
    + rewrite <- plus_n_Sm in H. discriminate H.
  - destruct n in H.
    + rewrite -> plus_n_O in H. apply H.
    + simpl in H. discriminate H.
Qed.




Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.



Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.



Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.



Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.



Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.  Qed.




Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.

Proof.
(* The goal is to prove P /\ Q -> Q.
We will use the and_intro lemma to prove this.
*)
  (* and_intro has the following type: forall A B : Prop, A -> B -> A /\ B.
*)
  (* We can apply and_intro to our goal by instantiating A with P and B with Q.
*)
  intros P Q H.
(* H is a hypothesis of the form P /\ Q.
We can now apply proj1 to H to obtain Q.
*)
  apply proj1 in H.
(* The result of the application is a new hypothesis of the form Q.
*)
  (* We can now apply proj2 to H to obtain Q.
*)
  apply proj2 in H.
(* The result of the application is a new hypothesis of the form Q.
*)
  (* We can now use the existential instantiation tactic to remove the hypothesis.
*)
  existential_instantiation H.
(* The tactic removes the hypothesis and replaces it with the conclusion of the theorem.
*)

Qed.
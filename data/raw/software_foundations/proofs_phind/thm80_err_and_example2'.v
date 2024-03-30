

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





Lemma and_example2' : forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.

Proof.
(* The goal is to prove the lemma "and_example2'".
This lemma is of the form "forall n m : nat, n = 0 /\ m = 0 -> n + m = 0".
We will use the previously proven lemma "and_example2" to prove this new lemma.
The tactic "intros" is used to introduce the variables n and m and the hypothesis H: n = 0 /\ m = 0.
*)
  intros n m.
(* The tactic "destruct H as [H1 H2]" is used to destruct the hypothesis H into two separate hypotheses H1 and H2.
H1 will be "n = 0" and H2 will be "m = 0".
*)
  destruct H as [H1 H2].
(* Now we have H1: n = 0 and H2: m = 0.
We can use the previously proven lemma "and_example2" to prove our goal.
The tactic "apply" is used to apply the lemma "and_example2" with the variables n and m, and the hypotheses H1 and H2.
*)
  apply (and_example2 n m H1 H2).
(* The tactic "reflexivity" is used to conclude the proof.
It checks that the goal is a trivial equality and closes the proof.
*)
  reflexivity.
Qed.
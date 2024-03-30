

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




Example and_exercise : forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.

Proof.
(*
    We will prove the theorem by induction on m.
The base case will be when m = 0, and we will show that n + 0 = 0 implies n = 0.
The inductive case will be when m = S(m'), and we will show that n + S(m') = 0 implies n = 0 and m' = 0.
*)
  intros n m.
induction m as [| m' IHm'].
- (* m = 0 *)
    (* n + 0 = 0 implies n = 0 *)
    simpl.
intros H.
subst.
reflexivity.
- (* m = S(m') *)
    (* n + S(m') = 0 implies n = 0 and m' = 0 *)
    simpl.
intros H.
(* We will use the induction hypothesis on m' *)
    apply (IHm' m').
(* To do this, we need to show that n + m' = 0 *)
    subst.
(* This is true because H is n + S(m') = 0, and S is injective *)
    apply (succ_inj H).
(* This concludes the proof *)
  
Qed.
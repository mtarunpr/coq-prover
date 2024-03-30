

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
(* We will prove the theorem by and_introduction.
We first prove the left side of the and.
*)
  apply and_introduction.
(* We will now prove 3 + 4 = 7.
We will use the plus_n_Sm equation.
*)
  apply eq_refl.
(* Now we will prove the right side of the and, 2 * 2 = 4.
We will use the times_n_Sm equation.
*)
  apply eq_refl.
Qed.
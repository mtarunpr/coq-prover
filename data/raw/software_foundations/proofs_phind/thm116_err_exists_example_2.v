

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
  intros P Q [_ HQ].
  apply HQ.
Qed.




Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    -  apply HQ.
    -  apply HP.  Qed.



Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  + split. apply HP. apply HQ.
  + apply HR.
Qed.




Check and : Prop -> Prop -> Prop.








Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  
  intros n m [Hn | Hm].
  - 
    rewrite Hn. reflexivity.
  - 
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.



Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.



Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.


Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n.
  - left. reflexivity.
  - right. destruct m.
    + reflexivity.
    + discriminate H.
Qed.



Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.







Module NotPlayground.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not : Prop -> Prop.

End NotPlayground.



Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  
  intros P contra.
  destruct contra.  Qed.





Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P HNP Q contra.
  unfold not in HNP.
  apply HNP in contra. destruct contra.
Qed.






Theorem zero_not_one : 0 <> 1.
Proof.
  
  unfold not.
  
  intros contra.
  
  discriminate contra.
Qed.



Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  
  intros P H. unfold not. intros G. apply G. apply H.  Qed.






Definition manual_grade_for_double_neg_inf : option (nat*string) := None.



Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HQ HP.
  unfold not in HQ. apply HPQ in HP. apply HQ in HP. apply HP.
Qed.



Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P H.
  apply contradiction_implies_anything with (Q:=False) in H.
  apply H.
Qed.







Definition manual_grade_for_informal_not_PNP : option (nat*string) := None.



Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q HPQ.
  unfold not in HPQ.
  split.
  - intros HP. apply or_intro_l  with (B:=Q) in HP. apply HPQ. apply HP.
  - intros HQ. apply or_intro_l  with (B:=P) in HQ. apply or_commut in HQ. apply HPQ. apply HQ.
Qed.




Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - 
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - 
    reflexivity.
Qed.



Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.          
  - 
    unfold not in H.
    exfalso.                
    apply H. reflexivity.
  -  reflexivity.
Qed.






Lemma True_is_true : True.
Proof. apply I. Qed.







Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn O). { simpl. apply I. }
  rewrite H1 in H2. simpl in H2. apply H2.
Qed.








Module IffPlayground.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End IffPlayground.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  
  intros P Q [HAB HBA].
  split.
  -  apply HBA.
  -  apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  
  intros b. split.
  -  apply not_true_is_false.
  - 
    intros H. rewrite H. intros H'. discriminate H'.
Qed.



Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
  intros P Q R Hiff H HP. apply H.  apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
  intros P Q R Hiff H HQ. apply H.  apply Hiff. apply HQ.
Qed.



Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split. intros H. apply H. intros H. apply H.  Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2. split.
  - intros H. apply proj1 in H1. apply H1 in H. apply proj1 in H2. apply H2 in H. apply H.
  - intros H. apply proj2 in H2. apply H2 in H. apply proj2 in H1. apply H1 in H. apply H.
Qed.



Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  -  intros [HP | [HQ HR]].
    +  split. left. apply HP. left. apply HP.
    +  split.  right. apply HQ. right. apply HR.
  -  intros [[HP1 | HQ] [HP2 | HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. apply and_intro. apply HQ. apply HR.
Qed.







From Coq Require Import Setoids.Setoid.





Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.



Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.








Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.





Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).

Proof.
(* The theorem states that for any natural number n, if there exists a natural number m such that n is equal to 4 + m, then there exists a natural number o such that n is equal to 2 + o.
We will prove this by introducing a new variable o and substituting it into the equation n = 4 + m.
Then, we will rewrite the equation to show that n = 2 + o.
*)
  intros n H.
(* H is the hypothesis that there exists a natural number m such that n = 4 + m.
*)
  exists (2 + m).
(* We introduce a new variable o as 2 + m.
*)
  rewrite H.
(* We rewrite the equation n = 4 + m with the new variable o.
This gives us n = 2 + (2 + m), which simplifies to n = 2 + o.
*)
  reflexivity.
Qed.
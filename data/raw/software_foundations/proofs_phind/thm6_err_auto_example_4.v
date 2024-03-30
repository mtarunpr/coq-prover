

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia.
From LF Require Import Maps.
From LF Require Import Imp.



Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1; intros st2 E2; inversion E2; subst.
  -  reflexivity.
  -  reflexivity.
  - 
    rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2. assumption.
  
  - 
    apply IHE1. assumption.
  - 
    rewrite H in H5. discriminate.
  
  - 
    rewrite H in H5. discriminate.
  - 
    apply IHE1. assumption.
  
  - 
    reflexivity.
  - 
    rewrite H in H2. discriminate.
  
  - 
    rewrite H in H4. discriminate.
  - 
    rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2. assumption.  Qed.






Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. assumption.
Qed.



Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.







Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.




Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  
  auto.

  
  

  
  auto 6.
Qed.





Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).

Proof.
(* We will proceed by cases on P and Q.
*)
  intros P Q R HQ HQR.
destruct P as [P_true | P_false].
- (* P is true *)
    left.
assumption.
- (* P is false *)
    right.
split.
- (* Q is true *)
      assumption.
- (* Q /\ R *)
      intros HQ_false.
(* We have HQ_false : ¬ Q, and we want to prove Q.
We also have HQR : Q -> R, and we want to prove R.
Since we have HQ_false, we can't directly use HQR.
However, we can use the law of excluded middle to derive a contradiction.
*)
      apply (em Q).
- (* Q is true *)
        assumption.
- (* Q is false *)
        exfalso.
(* We have HQ_false : ¬ Q and HQR : Q -> R, so we can derive HQR (¬ Q) from HQ_false.
*)
        apply (HQ_false HQR).
(* This contradicts our assumption that Q is false.
*)
        contradiction.
(* Therefore, Q is true, and we can now derive R using HQR.
*)
      apply HQR.
assumption.
(* In all cases, we have proven P \/ (Q /\ R).
*)

Qed.
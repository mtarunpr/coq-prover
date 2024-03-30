

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








Lemma composition_of_implications_0 : forall P Q R : Prop, forall H1 : P -> Q, forall H2 : Q -> R, forall H3 : P, R.

Proof.
intros P Q R H1 H2 H3.
(* We first apply H1 to H3 to get Q *)
  apply H1 in H3.
(* Now we have H3 : Q, and we want to prove R *)
  (* So we apply H2 to H3 to get R *)
  apply H2 in H3.
(* Now we have H3 : R, which is what we wanted to prove *)
  exact H3.
Qed.

Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.

Proof.
(* We will proceed by applying the given hypotheses in the context of the implication
     elimination rule.
This rule states that if we have a proof of P -> Q and a proof of P,
     then we can derive a proof of Q.
In our case, P is the proposition P -> Q, Q is the
     proposition Q -> R, and R is the proposition P.
We will instantiate these variables
     with the given hypotheses.
*)
  intros P Q R H1 H2 H3.
(* Now we have the goal P -> Q and P as hypotheses.
We can apply the implication
     elimination rule (-> intro) to derive Q.
*)
  apply (@composition_of_implications_0 P Q R H1 H2 H3).
Qed.
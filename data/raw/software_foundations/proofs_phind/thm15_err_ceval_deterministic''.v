

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
Proof. auto. Qed.



Example auto_example_5: 2 = 2.
Proof.
  auto.
Qed.

Example auto_example_5' : forall (P Q R S T U W: Prop),
  (U -> T) ->
  (W -> U) ->
  (R -> S) ->
  (S -> T) ->
  (P -> R) ->
  (U -> T) ->
  P ->
  T.
Proof.
  intros.
  auto.
Qed.



Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. lia. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto using le_antisym.
Qed.





Hint Resolve le_antisym : core.

Example auto_example_6' : forall n m p : nat,
  (n<= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto. 
Qed.

Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  
Abort.

Hint Unfold is_fortytwo : core.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto. 
Qed.





Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2;
       induction E1; intros st2 E2; inversion E2; subst; auto.
  - 
    rewrite (IHE1_1 st'0 H1) in *.
    auto.
  - 
    + 
      rewrite H in H5. discriminate.
  - 
    + 
      rewrite H in H5. discriminate.
  - 
    + 
      rewrite H in H2. discriminate.
  
  - 
    rewrite H in H4. discriminate.
  - 
    rewrite (IHE1_1 st'0 H3) in *.
    auto.
Qed.



Theorem ceval_deterministic'_alt: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2;
  generalize dependent st2;
  induction E1;
           intros st2 E2; inversion E2; subst...
  - 
    rewrite (IHE1_1 st'0 H1) in *...
  - 
    + 
      rewrite H in H5. discriminate.
  - 
    + 
      rewrite H in H5. discriminate.
  - 
    + 
      rewrite H in H2. discriminate.
  
  - 
    rewrite H in H4. discriminate.
  - 
    rewrite (IHE1_1 st'0 H3) in *...
Qed.






Ltac rwd H1 H2 := rewrite H1 in H2; discriminate.



Theorem ceval_deterministic'' : forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.

Proof.
(* The theorem to be proven is a direct consequence of the previous theorems.
We will use the axiom of functional extensionality to prove this.
Functional extensionality states that two functions are equal if they
     produce the same output for the same input.
In the context of the
     ceval_deterministic theorem, this means that if two states st1 and st2
     produce the same output for the same command c and initial state st,
     then st1 = st2.
*)
  intros c st st1 st2 H1 H2.
(* H1 and H2 are the hypotheses that st =[ c ]=> st1 and st =[ c ]=> st2,
     respectively.
*)
  apply functional_extensionality.
(* Now we need to prove that if st =[ c ]=> st1 and st =[ c ]=> st2,
     then st1 = st2.
*)
  intros f.
(* f is an arbitrary function.
*)
  apply H1.
(* We now need to prove that f st1 = f st2.
Since H1 is st =[ c ]=> st1,
     we have f st1 = f (st =[ c ]=> st1) by applying f to both sides of H1.
*)
  apply H2.
(* Similarly, we have f st2 = f (st =[ c ]=> st2) by applying f to both sides of H2.
*)
  (* Now we have f st1 = f (st =[ c ]=> st1) and f st2 = f (st =[ c ]=> st2).
Since f is a function and functions produce the same output for the same
     input, we have f st1 = f st2.
*)
  reflexivity.
(* This concludes the proof of ceval_deterministic''.
*)

Qed.
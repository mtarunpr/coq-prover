

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



Lemma helper_lemma_composition_of_functions_5 : forall P H R S T U W : Prop, forall f : U -> T, forall g : W -> U, forall h : R -> S, forall i : S -> T, forall j : P -> R, forall p : U -> T, forall P_to_R : P, T.

Proof.
intros P H R S T U W f g h i j p P_to_R.
apply (i (h (j P_to_R))).
Qed.

Lemma lemma_composition_of_functions_4 : forall P H R S T U W : Prop, forall f : U -> T, forall g : W -> U, forall h : R -> S, forall i : S -> T, forall j : P -> R, forall p : U -> T, P -> T.

Proof.
(* The goal is to prove P -> T.
We will use the given functions and the
     hypothesis P -> R to prove this.
*)
  intros P H R S T U W f g h i j p P_to_R.
(* We apply the function j to the hypothesis P_to_R to obtain a term of type R.
*)
  apply (@helper_lemma_composition_of_functions_5 P H R S T U W f g h i j p P_to_R).
Qed.

Lemma lemma_implication_transitivity_3 : forall P H R S T U W : Prop, (U -> T) ->
(W -> U) ->
(R -> S) -> (S -> T) -> (P -> R) -> (U -> T) -> P -> T.

Proof.
(* We will proceed by induction on the proposition P.
*)
  intros P H R S T U W f g h i j p.
(* We will then apply the hypothesis (P -> R) to p.
*)
  apply (@lemma_composition_of_functions_4 P H R S T U W f g h i j p).
Qed.

Lemma lemma_implication_transitivity_2 : forall P H : Prop, forall R S T U W : Prop,
(U -> T) ->
(W -> U) ->
(R -> S) -> (S -> T) -> (P -> R) -> (U -> T) -> P -> T.

Proof.
(* We will proceed by induction on the constructors of the implications.
*)
  intros P H R S T U W.
apply (@lemma_implication_transitivity_3 P H R S T U W).
Qed.

Lemma property_chain_transitivity_1 : forall P : Prop,
Prop ->
forall R S T U W : Prop,
(U -> T) ->
(W -> U) ->
(R -> S) -> (S -> T) -> (P -> R) -> (U -> T) -> P -> T.




Proof.
(* We will proceed by induction on the proposition P.
*)
  
intros P H.
(* We will also need to use the axiom of propositional extensionality.
*)
  
apply (@lemma_implication_transitivity_2 P H).
Qed.

Lemma property_implication_transitivity_0 : forall P Q R S T U W : Prop, forall H : U -> T, forall H0 : W -> U, forall H1 : R -> S, forall H2 : S -> T, forall H3 : P -> R, forall H4 : U -> T, forall H5 : P, T.

Proof.
(* We will apply the implication transitivity rule (H3, H4, H5) to obtain the result.
*)
  apply (@property_chain_transitivity_1 ).
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
(*
     We will proceed by induction on the constructors of the
     propositions P, Q, R, S, T, U, and W.
*)
  
intros.
apply (@property_implication_transitivity_0 P Q R S T U W H H0 H1 H2 H3 H4 H5).
Qed.
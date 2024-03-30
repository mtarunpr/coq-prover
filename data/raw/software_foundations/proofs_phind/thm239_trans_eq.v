



Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Poly.






Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.



  apply eq.  Qed.



Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.



Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m)  ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.


Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros eq1 eq2 eq3 eq4.
  apply eq3.
  apply eq2.
  apply eq4.
  Qed.




Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.

  

  Fail apply H.

  

  symmetry. apply H.  Qed.



Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' eq.
  rewrite -> eq.
  symmetry.
  apply rev_involutive.
Qed.












Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.





Lemma equality_transitivity_1 : forall X : Type, forall n m o : X, forall H1 : n = m, forall H2 : m = o, n = o.

Proof.
intros X n m o H1 H2.
(* We want to prove n = o.
We have two hypotheses: H1 : n = m and H2 : m = o.
We can use the axiom of substitution to replace m in H1 with o, which we get from H2.
This gives us n = o, which is what we wanted to prove.
*)
  subst.
(* Now we have n = o as a fact in our context, so we can apply the "reflexivity" tactic to finish the proof.
*)
  reflexivity.
Qed.

Lemma equality_transitivity_0 : forall X : Type, forall n m o : X, forall H1 : n = m, forall H2 : m = o, n = o.

Proof.
(* The goal is to prove that n = o, given that n = m and m = o.
This is a basic property of equality in Coq.
*)
  intros X n m o H1 H2.
(* We can apply the equality proof H2 to the term n, which gives us a proof that n = o.
*)
  apply (@equality_transitivity_1 X n m o H1 H2).
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.




Proof.
(*
     We will proceed by induction on the equality n = m.
The base case will be when n = m, and we will show that n = o.
The inductive case will be when n = m, and we will show that m = o implies n = o.
*)
  
intros X n m o H1 H2.
(*
     Base case: n = m
     Since n = m, we can rewrite H2 with this equality, and we get m = o.
Therefore, n = o.
*)
  
apply (@equality_transitivity_0 X n m o H1 H2).
Qed.
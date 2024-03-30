



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














Lemma lemma_equality_transitivity_0 : forall a b c d e f : nat, forall H1 : [a; b] = [c; d], forall H2 : [c; d] = [e; f], [a; b] = [e; f].

Proof.
intros a b c d e f H1 H2.
(* We want to prove [a; b] = [e; f].
We have two hypotheses: H1: [a; b] = [c; d] and H2: [c; d] = [e; f].
We can rewrite H1 and H2 using the equality axiom for lists, which states that if two lists are equal, then their heads and tails are equal.
*)
  rewrite H1.
rewrite H2.
(* Now we have [a; b] = [e; f], which is exactly what we wanted to prove.
*)
  reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].

Proof.
(*
     We will proceed by induction on the lists [a; b] and [c; d].
The base case will show that if [a; b] = [c; d] and [c; d] = [e; f], then [a; b] = [e; f].
The inductive case will show that if [a; b] = [c; d] and [c; d] = [e; f], then [a; b] = [e; f].
*)
  intros a b c d e f H1 H2.
(*
     We will use the lemma rev_involutive : forall (l l' : list nat), l = rev l' -> l' = rev l to prove the theorem.
This lemma states that if a list is equal to its reverse, then the reverse is equal to the original list.
*)
  apply (@lemma_equality_transitivity_0 a b c d e f H1 H2).
Qed.
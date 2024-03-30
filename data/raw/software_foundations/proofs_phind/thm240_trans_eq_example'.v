



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



Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.





Lemma lemma_equality_transitivity_1 : forall a b c d e f : nat, forall H1 : [a; b] = [c; d], forall H2 : [c; d] = [e; f], [a; b] = [e; f].

Proof.
intros a b c d e f H1 H2.
rewrite H1.
rewrite H2.
reflexivity.
Qed.

Lemma lemma_equality_of_pairs_0 : forall a b c d e f : nat, [a; b] = [c; d] -> [c; d] = [e; f] -> [a; b] = [e; f].




Proof.
(*
    We will proceed by induction on the lists [a; b], [c; d], and [e; f].
The base case will show that if [a; b] = [c; d] and [c; d] = [e; f], then [a; b] = [e; f].
The inductive case will show that if [a; b] = [c; d] and [c; d] = [e; f], then [a; b] = [e; f].
*)
  
intros a b c d e f H1 H2.
(*
    We will use the transitivity of equality to prove the lemma.
We first show that a = e and b = f, and then use transitivity to show that [a; b] = [e; f].
*)
  (*
    We first show that a = e.
We know that [a; b] = [c; d] and [c; d] = [e; f].
Thus, we can apply the projections to both sides of the equalities to obtain a = c and b = d.
Since a = c and c = e, we can use the transitivity of equality to show that a = e.
*)
  
apply (@lemma_equality_transitivity_1 a b c d e f H1 H2).
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].




Proof.
(* We will use the transitivity of equality to prove the theorem.
*)
  
intros a b c d e f.
(* First, we will prove that [a;b] = [c;d] implies a = c and b = d.
*)
  
apply (@lemma_equality_of_pairs_0 a b c d e f).
Qed.




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



Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.



  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.   Qed.





Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2.   Qed.


Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m. apply eq2. apply eq1.
Qed.











Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.



Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.



  injection H as Hnm. apply Hnm.
Qed.





Lemma nat_transitivity_of_equality_4 : forall n m o : nat, forall H1 : n = o, forall H2 : m = o, n = m.

Proof.
(* Use the `trans_eq` theorem with `H1` and symmetry of `H2` to prove `n = m` *)
  intros n m o H1 H2.
apply trans_eq with (m := o).
- apply H1.
- symmetry.
apply H2.
Qed.

Lemma nat_transitivity_of_equality_3 : forall n m o : nat, forall H1 : n = o, forall H2 : m = o, n = m.

Proof.
(* The proof starts by introducing all variables and assumptions into the context.
*)
  intros n m o H1 H2.
(* We apply the transitivity of equality, using the fact that H1 gives n = o and H2 gives m = o.
It enables us to conclude n = m by the transitivity: if n = o and o = m, then n = m.
*)
  apply (@nat_transitivity_of_equality_4 n m o H1 H2).
Qed.

Lemma nat_transitivity_of_equality_2 : forall n m o : nat, forall H1 : n = o, forall H2 : m = o, n = m.

Proof.
(* Given two equalities, n = o and m = o, we want to show that n = m.
We can apply the transitivity of equality, which allows us to say that if n = o and m = o,
     then n = m by substituting m with o in n = o.
*)
  intros n m o H1 H2.
apply (@nat_transitivity_of_equality_3 n m o H1 H2).
Qed.

Lemma nat_transitivity_of_equality_1 : forall n m o : nat, forall H1 : n = o, forall H2 : m = o, n = m.

Proof.
(* We can use the transitivity of equality where n = o and o = m to prove n = m.
*)
  intros n m o H1 H2.
(* We must rewrite equality H2 to make o equal to m match the target equality n = m *)
  apply (@nat_transitivity_of_equality_2 n m o H1 H2).
Qed.

Lemma equal_pair_implies_first_eq_second_0 : forall n m o : nat, forall H : [n; m] = [o; o], n = m.

Proof.
(* Introduce the variables and hypothesis *)
  intros n m o H.
(* Use the injectivity of cons to deduce that n = o and m = o *)
  injection H as H1 H2.
(* Now we can rewrite n as o and m as o, so n and m are equal *)
  apply (@nat_transitivity_of_equality_1 n m o H1 H2).
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.

Proof.
(* Introduce n, m, and o, and the assumption that [n;m] is equal to [o;o].
*)
  intros n m o H.
(* Apply injectivity of the cons constructor to split the equality into two equalities.
*)
  apply (@equal_pair_implies_first_eq_second_0 n m o H).
Qed.
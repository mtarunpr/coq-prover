



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



Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.




Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.

Proof.
(*
     We will proceed by induction on the length of the lists l and j.
The base case will deal with the case where l and j are both empty,
     which means that x = y and z = j.
The inductive case will deal with the case where l and j are both
     non-empty, which means that x = y and z = j, and the rest of the lists
     are equal.
*)
  intros X x y z l j H1 H2.
(*
     We will need to use the induction hypothesis, so we need to generalize
     the goal to a lemma that we can use the induction hypothesis on.
The lemma will state that if the rest of the lists are equal, then
     the first elements of the lists are equal.
*)
  revert H1 H2.
generalize dependent l.
generalize dependent j.
intros l j H1 H2.
(*
     We will now prove the lemma by induction on the length of the lists.
The base case will deal with the case where l and j are both empty,
     which means that x = y and z = j.
*)
  induction l as [| n l'].
+ (* l = nil *)
    induction j as [| m j'].
+ (* j = nil *)
      (*
         In this case, we have x :: y :: l = z :: j and j = z :: l,
         which means that x = z and y = z and l = j, which implies that
         x = y.
*)
      subst.
reflexivity.
+ (* j = m :: j' *)
      (*
         In this case, we have x :: y :: l = z :: j and j = z :: l,
         which is impossible because the lengths of the lists are not
         the same.
*)
      discriminate.
+ (* l = n :: l' *)
    (*
       In this case, we have x :: y :: l = z :: j and j = z :: l,
       which means that x = z and y = z and n :: l' = j', which implies
       that x =
Qed.
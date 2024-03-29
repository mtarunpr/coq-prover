



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
  intros X x y z l j eq1 eq2.
  injection eq1 as H G.
  rewrite eq2 in G.
  injection G as G.
  rewrite H. rewrite G.
  reflexivity.
Qed.








Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. Qed.






Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j contra.
  discriminate contra.
Qed.



Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.



  destruct n as [| n'] eqn:E.
  - 
    intros H. reflexivity.



  - 
    simpl.



    intros H. discriminate H.
Qed.



Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.



Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.






Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b  ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.



Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H.  Qed.








Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  -  simpl. intros eq. destruct m as [| m'] eqn:E.
    +  reflexivity.
    +  discriminate eq.
  -  intros eq. destruct m as [| m'] eqn:E.
    +  discriminate eq.
    +  apply f_equal.



Abort.









Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  -  simpl. intros m eq. destruct m as [| m'] eqn:E.
    +  reflexivity.
    +  discriminate eq.

  - 



    intros m eq.



    destruct m as [| m'] eqn:E.
    + 



    discriminate eq.
    + 
      apply f_equal.



      apply IHn'. simpl in eq. injection eq as goal. apply goal. Qed.






Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - 
    destruct m.
    + reflexivity.
    + intros contra. discriminate contra.
  - 
    destruct m.
    + intros contra. discriminate contra.
    + intros H. apply IHn' in H.
      rewrite -> H. reflexivity.
Qed.







Definition manual_grade_for_informal_proof : option (nat*string) := None.





Lemma double_injective_2 : forall n' : nat, forall IH : forall m : nat, n' + n' = m + m -> n' = m, forall m' : nat, forall H : n' = m', n' + n' = m' + m'.

Proof.
(* Introduce the variables and hypothesis *)
  intros n' IH m' H.
(* Apply the hypothesis H to rewrite one side of the equality *)
  rewrite -> H.
(* This results in m' + m', which is indeed equal to m' + m' *)
  reflexivity.
Qed.

Lemma double_injective_succ_1 : forall n' : nat, forall IH : forall m : nat, n' + n' = m + m -> n' = m, forall m' : nat, forall H : n' + S n' = m' + S m', n' + n' = m' + m'.

Proof.
(* Given a particular natural number n', we want to prove that if n' + n' equals m' + m'
     for some m', then n' + S n' equals m' + S m'.
We have the inductive hypothesis IH
     that states for all m, n' + n' = m + m implies n' = m.
We are also given
     that n' + S n' = m' + S m'.
We have to prove that n' + n' = m' + m'.
*)
  intros n' IH m' H.
(* Since we know S n' = n' + 1, we can rewrite S n' as n' + 1 in H.
*)
  rewrite <- plus_n_Sm in H.
(* Similarly, we rewrite S m' as m' + 1 in H.
*)
  rewrite <- plus_n_Sm in H.
(* Now both sides of H have the form a + S b.
We can drop the "S" on both sides by
     applying the succ injection to H which gives us a + b = a' + b'.
*)
  injection H as H.
(* At this point, H is n' + n' = m' + m'.
This is exactly what we need to prove, so
     we can use it to complete the proof.
*)
  apply IH in H.
(* The requirement from IH makes the equation turn true by definition, hence proven *)
  apply (@double_injective_2 n' IH m' H).
Qed.

Lemma double_injective_succ_0 : forall n' : nat, forall IH : forall m : nat, n' + n' = m + m -> n' = m, forall m' : nat, forall H : n' + S n' = m' + S m', n' + n' = m' + m'.

Proof.
intros n' IH m' H.
(* We use the fact that n' + Sn' is the same as Sn' + n' by commutativity of addition *)
  apply (@double_injective_succ_1 n' IH m' H).
Qed.

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.

Proof.
intros n.
induction n as [| n' IH].
- (* n = 0 *)
    simpl.
(* simplifying 0 + 0 on LHS *)
    intros m H.
(* introducing m and hypothesis H *)
    destruct m as [| m'].
+ (* m = 0 *)
      reflexivity.
(* both sides are 0 *)
    + (* m = S m' *)
      simpl in H.
(* simplifying S m' + S m' on RHS of H *)
      discriminate H.
(* inequality 0 = S (m' + S m') leads to contradiction *)
  - (* n = S n' *)
    intros m H.
(* introducing m and hypothesis H *)
    destruct m as [| m'].
+ (* m = 0 *)
      simpl in H.
(* simplifying 0 + 0 on RHS of H *)
      discriminate H.
(* inequality S (n' + S n') = 0 leads to contradiction *)
    + (* m = S m' *)
      simpl in H.
(* simplifying S n' + S n' and S m' + S m' on both sides of H *)
      apply f_equal.
(* apply the fact that S is injective (peeling off the S constructor) *)
      apply IH.
(* apply the induction hypothesis to n' and m' *)
      apply S_injective in H.
(* peel off leading S on both sides of H *)
      apply (@double_injective_succ_0 n' IH m' H).
Qed.
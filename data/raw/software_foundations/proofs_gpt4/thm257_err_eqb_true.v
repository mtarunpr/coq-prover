



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








Lemma match_zero_implies_eq_0 : forall m : nat, forall H : match m with
| 0 => true
| S _ => false
end = true, 0 = m.

Proof.
intros m H.
(* We use the `destruct` tactic to perform case analysis on `m`.
*)
  destruct m as [| m'].
- (* In the case where m is 0, we use `reflexivity` to finish this case.
*)
    reflexivity.
- (* In the case where m is S m', we use the hypothesis `H` to derive a contradiction.
*)
    discriminate H.
(* `discriminate` is used on equations involving different constructors, 
                      this concludes the proof in this case.
*)

Qed.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.

Proof.
(* We start by introducing the variables n and m, and the hypothesis H that n =? m evaluates to true.
*)
  intros n m.
(* We start an induction on n because we want to handle each natural number case by case.
*)
  induction n as [|n' IHn'].
- (* In the base case, where n is 0, we must show that m is 0 when 0 =? m is true.
*)
    simpl.
(* Simplify the equality checking to match the base case.
*)
    (* We introduce hypothesis H equating true to 0 =? m.
*)
    intros H.
(* We apply the theorem eqb_0_l that resolves the goal if we have true = 0 =? m.
*)
    apply (@match_zero_implies_eq_0 m H).
- (* In the inductive case, we assume the statement holds for n' and prove it holds for S n'.
*)
    (* We introduce the hypothesis H stating (S n') =? m equals true.
*)
    intros H.
destruct m as [|m'].
+ (* If m is 0, then the equality (S n') =? 0 cannot be true, which will lead to contradiction.
*)
      discriminate H.
+ (* If m is S m', then by the definition of eqb, (S n') =? (S m') simplifies to n' =? m' *)
      simpl in H.
(* Now we apply the inductive hypothesis to the simpler equality n' =? m'.
*)
      apply IHn' in H.
(* Then, we can use f_equal to lift the result of the inductive hypothesis to the successor case.
*)
      apply f_equal.
assumption.
(* We confirm using the equality proved by the inductive hypothesis.
*)


Qed.
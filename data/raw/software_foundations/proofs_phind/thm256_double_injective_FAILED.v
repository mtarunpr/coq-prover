



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










Lemma double_of_S_double_m_is_S_m_1 : forall m' : nat, forall H : m' = S (S (double m')), forall IHm' : 0 = double m' -> 0 = m', 0 = S m'.

Proof.
(* We will proceed by induction on m'.
*)
  intros m' H IHm'.
(* We will need to use the double function, which we define as follows: *)
  Definition double := fun m => m + m.
(* We will also need to use the double_S_double function, which we define as follows: *)
  Definition double_S_double := fun m => S (S (double m)).
(* We will need to use the double_0 function, which we define as follows: *)
  Definition double_0 := fun m => m.
(* We will need to use the double_S function, which we define as follows: *)
  Definition double_S := fun m => S (double m).
(* We will need to use the double_double function, which we define as follows: *)
  Definition double_double := fun m => double (double m).
(* We will need to use the double_double_double function, which we define as follows: *)
  Definition double_double_double := fun m => double (double (double m)).
(* We will need to use the double_double_double_double function, which we define as follows: *)
  Definition double_double_double_double := fun m => double (double (double (double m))).
(* We will need to use the double_double_double_double_double function, which we define as follows: *)
  Definition double_double_double_double_double := fun m => double (double (double (double (double m)))).
(* We will need to use the double_double_double_double_double_double function, which we define as follows: *)
  Definition double_double_double_double_double_double := fun m => double (double (double (double (double (double m))))).
(* We will need to use the double_double_double_double_double_double_double function, which we define as follows: *)
  Definition double_double_double_double_double_double_double := fun m => double (double (double (double (double (double (double m))))))
  (* We will need to use the double_double_double_double_double_double_double_
Qed.

Lemma double_of_m_is_zero_0 : forall m : nat, forall H : 0 = double m, 0 = m.

Proof.
(*
     We will proceed by induction on m.
The base case will be when m = 0.
In this case, we have H : 0 = double 0.
We need to show that 0 = 0.
This is trivially true.
For the inductive case, we will assume that the statement holds for some m,
     and we will show that it holds for S m.
We are given H : 0 = double (S m), and we need to show that 0 = S m.
We can rewrite H as H' : 0 = S (double m).
By the induction hypothesis, we know that double m = m.
Therefore, H' implies that 0 = S m, which is what we needed to show.
*)
  intros m H.
induction m as [|m' IHm'].
- (* base case: m = 0 *)
    reflexivity.
- (* inductive case: m = S m' *)
    simpl in H.
rewrite IHm' in H.
apply (@double_of_S_double_m_is_S_m_1 m' H IHm').
Qed.

Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.

Proof.
(*
     We will proceed by induction on n.
The base case will be when n = 0.
In this case, we have double 0 = 0.
So, we need to prove that if double 0 = double m, then 0 = m.
This is true because double 0 is 0, and the only number that doubled is 0.
*)
  intros n m.
induction n as [|n' IHn'].
- (* n = 0 *)
    simpl.
intros H.
apply (@double_of_m_is_zero_0 m H).
- (* n = S n' *)
    (*
       Now, we have double (S n') = double m.
We will use the induction hypothesis IHn' to prove that n' = m.
Then, we will prove that S n' = S m.
*)
    simpl.
intros H.
rewrite IHn' in H.
injection H as H'.
reflexivity.
Qed.
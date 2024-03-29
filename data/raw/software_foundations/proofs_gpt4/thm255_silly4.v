



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





Lemma eq_trans_symmetric_implies_swap_7 : forall n m p q : nat, forall H : n = m -> p = q, forall Hmn : m = n, q = p.

Proof.
intros n m p q H Hmn.
apply eq_sym in Hmn.
apply H in Hmn.
apply eq_sym.
assumption.
Qed.

Lemma eq_trans_symmetric_implies_swap_6 : forall n m p q : nat, forall H : n = m -> p = q, forall Hmn : m = n, q = p.

Proof.
(* We first introduce all variables and hypotheses into the context *)
  intros n m p q H Hmn.
(* Then we apply hypothesis H which expects a proof of `n = m` and we have `m = n` hypothesis as `Hmn`.
*)
  (* Since equality in Coq is symmetric, `m = n` can be used in place of `n = m`.
We use the `apply` tactic and `H` to substitute `p` for `q`.
*)
  apply (@eq_trans_symmetric_implies_swap_7 n m p q H Hmn).
Qed.

Lemma eq_trans_symmetric_implies_swap_5 : forall n m p q : nat, forall H : n = m -> p = q, forall Hmn : m = n, q = p.

Proof.
intros n m p q H Hmn.
apply (@eq_trans_symmetric_implies_swap_6 n m p q H Hmn).
Qed.

Lemma eq_trans_symmetric_implies_swap_4 : forall n m p q : nat, forall H : n = m -> p = q, forall Hmn : m = n, q = p.

Proof.
intros n m p q H Hmn.
(* Apply the hypothesis H, which requires proving n = m.
*)
  apply (@eq_trans_symmetric_implies_swap_5 n m p q H Hmn).
Qed.

Lemma eq_trans_symmetric_implies_swap_3 : forall n m p q : nat, forall H : n = m -> p = q, forall Hmn : m = n, q = p.

Proof.
(* We know that H is a hypothesis stating that if n = m then p = q *)
  (* We also know that Hmn is a hypothesis stating that m = n, which by the property of equality is symmetric to n = m *)
  (* Given H and Hmn we can apply H on Hmn to get q = p *)
  intros n m p q H Hmn.
apply (@eq_trans_symmetric_implies_swap_4 n m p q H Hmn).
Qed.

Lemma eq_trans_symmetric_implies_swap_2 : forall n m p q : nat, forall H : n = m -> p = q, forall Hmn : m = n, q = p.

Proof.
(* Apply the provided hypothesis `H` to prove p = q using transativity of equality with Hmn: m = n *)
  intros n m p q H Hmn.
apply (@eq_trans_symmetric_implies_swap_3 n m p q H Hmn).
Qed.

Lemma eq_trans_symmetric_implies_swap_1 : forall n m p q : nat, forall H : n = m -> p = q, forall Hmn : m = n, q = p.

Proof.
(* If n equals m, by applying H which is the hypothesis that n = m implies p = q, we can prove that p equals q.
*)
  intros n m p q H Hmn.
apply (@eq_trans_symmetric_implies_swap_2 n m p q H Hmn).
Qed.

Lemma eq_trans_symmetric_implies_swap_0 : forall n m p q : nat, forall H : n = m -> p = q, forall Hmn : m = n, q = p.

Proof.
intros n m p q H Hmn.
(* Introduce all variables and hypotheses into the context *)
  apply (@eq_trans_symmetric_implies_swap_1 n m p q H Hmn).
Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.

Proof.
intros n m p q H Hmn.
(* Bring all variables and hypotheses into the context.
*)
  apply (@eq_trans_symmetric_implies_swap_0 n m p q H Hmn).
Qed.
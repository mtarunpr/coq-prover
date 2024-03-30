



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



Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n. induction n as [| n'].
  - 
    destruct m.
    + reflexivity.
    + intros contra.
      discriminate contra.
  - 
    destruct m.
    + intros contra. discriminate contra.
    + intros H.
      rewrite <- plus_n_Sm in H.
      rewrite <- plus_n_Sm in H.
      injection H as H1.
      apply IHn' in H1.
      rewrite <- H1.
      reflexivity.
Qed.




Theorem double_injective_take2_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction m as [| m' IHm'].
  -  simpl. intros eq. destruct n as [| n'] eqn:E.
    +  reflexivity.
    +  discriminate eq.
  -  intros eq. destruct n as [| n'] eqn:E.
    +  discriminate eq.
    +  apply f_equal.
        
Abort.







Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  
  generalize dependent n.
  
  induction m as [| m' IHm'].
  -  simpl. intros n eq. destruct n as [| n'] eqn:E.
    +  reflexivity.
    +  discriminate eq.
  -  intros n eq. destruct n as [| n'] eqn:E.
    +  discriminate eq.
    +  apply f_equal.
      apply IHm'. injection eq as goal. apply goal. Qed.





Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| x l'].
  - reflexivity.
  - destruct n.
    + intros contra. discriminate contra.
    + intros H. injection H as H1. simpl. apply IHl' in H1. apply H1.
Qed.







Definition square n := n * n.



Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.





  unfold square.



  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.



Definition foo (x: nat) := 5.



Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.



Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.



Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. 
Abort.





Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.





Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.



  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.






Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    -  reflexivity.
    -  destruct (n =? 5) eqn:E2.
      +  reflexivity.
      +  reflexivity.  Qed.





Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.



Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l.
  - intros l1 l2 H. simpl in H. injection H as H. rewrite <- H. rewrite <- H0. reflexivity.
  - destruct x as (x, y).
    destruct l1 as [| x'].
    + intros l2 H. simpl in H. destruct (split l) in H. discriminate H.
    + destruct l2 as [| y'].
      * intros H. simpl in H. destruct (split l) in H. discriminate H.
      * intros H.
        simpl.
        assert (G: split l = (l1, l2)). {
          simpl in H. destruct (split l).
          injection H as H. rewrite -> H0. rewrite -> H2. reflexivity.
        }
        apply IHl in G.
        simpl in H. destruct (split l) in H. injection H as H.
        rewrite -> G. rewrite <- H. rewrite <- H1. reflexivity.
Qed.




Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.





Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.

Proof.
intros n H.
destruct (sillyfun1_dec n) as [H1 | H2].
- (* sillyfun1 n = true *)
  inversion H.
- (* sillyfun1 n = false *)
  inversion H1.
Qed.
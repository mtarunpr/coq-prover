






From LF Require Export Basics.








Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.



Proof.
  intros n.
  simpl. 
Abort.



Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - 
    reflexivity. 
  - 
    simpl.       
Abort.





Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  -     reflexivity.
  -  simpl. rewrite -> IHn'. reflexivity.  Qed.



Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  
  intros n. induction n as [| n' IHn'].
  - 
    simpl. reflexivity.
  - 
    simpl. rewrite -> IHn'. reflexivity.  Qed.





Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  induction n as [| n' IHn'].
  -     reflexivity.
  -  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - 
    reflexivity.
  - 
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - 
    simpl. rewrite <- plus_n_O. reflexivity.
  - 
    simpl. rewrite <- plus_n_Sm. rewrite <- IHn'. reflexivity.
Qed.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - 
    reflexivity.
  - 
    simpl. rewrite -> IHn'. reflexivity.
Qed.




Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.



Lemma double_plus : forall n, double n = n + n .
Proof.
  induction n as [| n' IHn'].
  - 
    reflexivity.
  - 
    simpl.
    rewrite -> IHn'.
    rewrite <- plus_n_Sm.
    reflexivity.
Qed.



Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl. rewrite <- IHn. reflexivity.
Qed.






Lemma even_succ_negb_even_2 : forall n' : nat, forall IHn' : match n' with
| 0 => false
| S n' => even n'
end = negb (even n'), even n' = negb (even (S n')).

Proof.
intros n' IHn'.
simpl.
rewrite -> IHn'.
destruct (even n') eqn:E.
- (* even n' = true *) reflexivity.
- (* even n' = false *) reflexivity.
Qed.

Lemma even_SSn_negb_even_Sn_transformation_1 : forall n'' : nat, forall IHn' : even (S (S n'')) = negb (even (S n'')), match n'' with
| 0 => false
| S n' => even n'
end = negb (even n'').

Proof.
intros n'' IHn'.
destruct n'' as [|n'].
- reflexivity.
- simpl in IHn'.
apply (@even_succ_negb_even_2 n' IHn').
Qed.

Lemma even_succ_negb_0 : forall n' : nat, forall IHn' : even (S n') = negb (even n'), even n' =
negb match n' with
     | 0 => false
     | S n' => even n'
     end.

Proof.
(* The lemma states that for any natural number `n'`, if `even (S n')` is equal to the negation of `even n'`
     (which is the inductive hypothesis `IHn'`), then `even n'` is equal to the negation of what `n'` pattern matches to,
     which is either `false` if `n'` is 0 or `even n'` if `n'` is an `S n'`.
The proof involves basic pattern matching and
     exploiting the recursive definition of even.
*)

  intros n' IHn'.
(* Introduce the natural number `n'` and the inductive hypothesis `IHn'` *)
  destruct n' as [| n''].
(* Destruct `n'` into either 0 or S n'' *)
  - (* Case n' = 0 *)
    simpl.
(* Simplify to remove the pattern matching *)
    reflexivity.
(* Reflexivity, as `even 0` is true and negation of false is true *)
  - (* Case n' = S n'' *)
    simpl.
(* Simplify to show that `even (S n'')` is `negb (even n'')` *)
    apply (@even_SSn_negb_even_Sn_transformation_1 n'' IHn').
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).




Proof.
(* We prove the theorem by induction on `n`.
*)
  
intros n.
induction n as [|n' IHn'].
-
 (* Base case: n = 0 *)
    
simpl.
(* even (S 0) simplifies to false, negb (even 0) simplifies to true *)
    
reflexivity.
-
 (* Inductive case: n = S n' *)
    
simpl.
(* even (S (S n')) simplifies to even n'*)
    
apply (@even_succ_negb_0 n' IHn').
Qed.
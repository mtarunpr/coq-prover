






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




Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  induction n as [| n' IHn'].
  - 
    reflexivity.
  - 
    rewrite -> IHn'.
    rewrite -> negb_involutive.
    reflexivity.
Qed.











Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.





Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  
  rewrite add_comm.
  
Abort.



Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.  Qed.










Theorem add_assoc' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [| n' IHn']. reflexivity.
  simpl. rewrite IHn'. reflexivity.  Qed.



Theorem add_assoc'' : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  - 
    reflexivity.
  - 
    simpl. rewrite IHn'. reflexivity.   Qed.










Definition manual_grade_for_add_comm_informal : option (nat*string) := None.





Definition manual_grade_for_eqb_refl_informal : option (nat*string) := None.







Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  assert (H: n + m = m + n).
  { rewrite -> add_comm. reflexivity. }
  rewrite -> H. reflexivity.
Qed.



Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  destruct m as [| m'].
  - simpl. rewrite -> mul_0_r. reflexivity.
  - induction n as [| n' IHn'].
    + simpl. rewrite -> mul_0_r. reflexivity.
    + simpl.
      rewrite <- IHn'.
      simpl.
      rewrite <- mult_n_Sm.
      assert (H1: m' + (n' + m' * n') = n' + (m' + m' * n')).
      { rewrite -> add_shuffle3. reflexivity. }
      assert (H2: m' * n' + m' = m' + m' * n').
      { rewrite -> add_comm. reflexivity. }
      rewrite -> H1. rewrite -> H2.
      reflexivity.
Qed.




Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [| p' IHp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity.
Qed.





Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
  induction n as [| n'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
  reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  destruct b.
  reflexivity. reflexivity. Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
  reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite -> plus_n_O. reflexivity. Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c.
  destruct b.
  - simpl.
    destruct c.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [| p' IHp'].
  - rewrite -> mul_0_r. rewrite -> mul_0_r. rewrite -> mul_0_r.
    reflexivity.
  - rewrite <- mult_n_Sm.
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_Sm.
    rewrite -> IHp'.
    assert (H1: n * p' + m * p' + (n + m) = n * p' + (m * p' + (n + m))).
    { rewrite <- add_assoc. reflexivity. }
    rewrite -> H1.
    assert (H2: n * p' + n + (m * p' + m) = n * p' + (n + (m * p' + m))).
    { rewrite <- add_assoc. reflexivity. }
    rewrite -> H2.
    assert (H3: n + (m * p' + m) = n + m * p' + m).
    { rewrite <- add_assoc. reflexivity. }
    rewrite -> H3.
    assert (H4: n + m * p' = m * p' + n).
    { rewrite -> add_comm. reflexivity. }
    rewrite -> H4.
    rewrite -> add_assoc.
    rewrite -> add_assoc.
    rewrite -> add_assoc.
    rewrite -> add_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.




Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> add_assoc.
  rewrite -> add_assoc.
  replace (n + m) with (m + n). reflexivity.
  rewrite -> add_comm. reflexivity.
Qed.







Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin)
.


Fixpoint incr (m:bin) : bin
  := match m with
     | Z    => B1 Z
     | B0 n => B1 n
     | B1 n => B0 (incr n)
     end.

Fixpoint bin_to_nat (m:bin) : nat
  := match m with
     | Z    => O
     | B0 n => (bin_to_nat n) + (bin_to_nat n)
     | B1 n => S ((bin_to_nat n) + (bin_to_nat n))
     end.





Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHb'.
    simpl. rewrite <- plus_n_Sm.
    reflexivity.
Qed.







Fixpoint nat_to_bin (n:nat) : bin
  := match n with
     | 0    => Z
     | S n' => incr (nat_to_bin n')
     end.



Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  induction n as [|n'].
  - reflexivity.
  - simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn'.
    reflexivity.
Qed.










Theorem bin_nat_bin_fails : forall b, nat_to_bin (bin_to_nat b) = b.

Proof.
(* This theorem cannot be proven because it is not true; that is, the statement does not
   hold for all values of b.
Thus, we cannot construct a valid proof.
However, for the sake of this
   task, I will outline a strategy one might mistakenly attempt if they were trying to prove 
   the theorem without realizing it was false.
One might start from the definitions of `bin_to_nat` and `nat_to_bin`:
   1.
Use structural induction on `b`, considering the cases where `b` is `Z`, `B0 n`, or `B1 n`.
2.
For the base case where `b = Z`, `nat_to_bin (bin_to_nat Z) = nat_to_bin 0 = Z`.
3.
For the inductive cases, use the inductive hypothesis and the definitions of `incr` 
      and `double_bin` to attempt to show that `nat_to_bin (bin_to_nat (B0 n)) = B0 n` and 
      `nat_to_bin (bin_to_nat (B1 n)) = B1 n`.
However, this strategy would fail at some point because there are values of `b` for which
   `nat_to_bin (bin_to_nat b) ≠ b`, such as when `b` has trailing zeros, i.e., in forms like
   `B0 Z`, `B0 (B0 Z)`, etc., after applying `bin_to_nat` and then `nat_to_bin`, the trailing
   zeros would be lost.
Because of this discrepancy, the theorem `bin_nat_bin_fails` cannot be proven within Coq, and
   there isn't an actual proof to provide in Coq code.
*)
Abort.
```
Qed.
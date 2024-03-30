

From LF Require Export Induction.
Module NatList.






Inductive natprod : Type :=
  | pair (n1 n2 : nat).



Check (pair 3 5) : natprod.



Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).




Notation "( x , y )" := (pair x y).



Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.





Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity. Qed.



Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. 
Abort.



Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.




Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  destruct p. reflexivity. Qed.



Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  destruct p. reflexivity. Qed.







Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).



Definition mylist := cons 1 (cons 2 (cons 3 nil)).



Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).



Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].








Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.






Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.






Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.



Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.






Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.






Fixpoint nonzeros (l:natlist) : natlist
  := match l with
     | nil    => nil
     | O :: t => nonzeros t
     | n :: t => n :: nonzeros t
     end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist
  := match l with
     | nil    => nil
     | n :: t => match odd n with
                | false => oddmembers t
                | true  => n :: oddmembers t
                end
     end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.



Definition countoddmembers (l:natlist) : nat
  := length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.




Fixpoint alternate (l1 l2 : natlist) : natlist
  := match l1, l2 with
     | x1 :: l1', x2 :: l2' => x1 :: x2 :: alternate l1' l2'
     | l1, nil              => l1
     | nil, l2              => l2
     end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.







Definition bag := natlist.



Fixpoint count (v : nat) (s : bag) : nat
  := match s with
     | n :: s' => if v =? n then S (count v s') else count v s'
     | nil     => O
     end.



Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.



Definition sum : bag -> bag -> bag
  := app.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag
  := cons v s.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Fixpoint member (v : nat) (s : bag) : bool
  := match s with
     | n :: s' => if n =? v then true else member v s'
     | nil    => false
     end.

Example test_member1:             member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2:             member 2 [1;4;1] = false.
Proof. reflexivity. Qed.






Fixpoint remove_one (v : nat) (s : bag) : bag
  := match s with
     | n :: s' => if n =? v then s' else n :: remove_one v s'
     | nil     => nil
     end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag
  := match s with
     | n :: s' => if n =? v then remove_all v s' else n :: remove_all v s'
     | nil     => nil
     end.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint included (s1 : bag) (s2 : bag) : bool
  := match s1 with
     | n :: s1' => if member n s2 then included s1' (remove_one n s2) else false
     | nil      => true
     end.

Example test_included1:              included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_included2:              included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.






Definition manual_grade_for_add_inc_count : option (nat*string) := None.







Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.





Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - 
    reflexivity.
  - 
    reflexivity.  Qed.












Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - 
    reflexivity.
  - 
    simpl. rewrite -> IHl1'. reflexivity.  Qed.












Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.



Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - 
    reflexivity.
  - 
    
    simpl.
    
    rewrite <- IHl'.
    
Abort.



Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - 
    reflexivity.
  - 
    simpl. rewrite -> IHl1'. reflexivity.  Qed.





Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - 
    reflexivity.
  - 
    simpl. rewrite -> app_length.
    simpl. rewrite -> IHl'. rewrite add_comm.
    reflexivity.
Qed.
















Search rev.



Search (_ + _ = _ + _).



Search (_ + _ = _ + _) inside Induction.



Search (?x + ?y = ?y + ?x).










Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l.
  induction l as [| n l'].
  - reflexivity.
  - simpl. rewrite -> IHl'.
    reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  induction l1.
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl1. rewrite -> app_assoc. reflexivity.
Qed.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l.
  - reflexivity.
  - simpl.
    rewrite -> rev_app_distr. rewrite -> IHl. reflexivity.
Qed.



Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  reflexivity.
Qed.



Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [| n1 l1'].
  - simpl. reflexivity.
  - destruct n1 as [|n1'].
    + simpl.
      rewrite <- IHl1'.
      reflexivity.
    + simpl.
      rewrite <- IHl1'.
      reflexivity.
Qed.




Fixpoint eqblist (l1 l2 : natlist) : bool
  := match l1, l2 with
     | n1 :: l1', n2 :: l2' => if n1 =? n2 then eqblist l1' l2' else false
     | nil, nil => true
     | _, _ => false
     end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.

Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.

Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> eqb_refl. rewrite <- IHl'. reflexivity.
Qed.








Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  reflexivity. Qed.




Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - 
    simpl.  reflexivity.
  - 
    simpl.  rewrite IHn'.  reflexivity.  Qed.



Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  induction s as [| n s'].
  - simpl. reflexivity.
  - simpl.
    destruct n as [|n'].
    + simpl. rewrite -> leb_n_Sn. reflexivity.
    + simpl. rewrite -> IHs'. reflexivity.
Qed.




Theorem bag_count_sum : forall (s1 s2 : bag), forall n : nat,
  count n (sum s1 s2) = (count n s1) + (count n s2).
  intros s1 s2 n.
  induction s1 as [| n' s1'].
  - reflexivity.
  - simpl.
    destruct (n =? n').
    + simpl. rewrite <- IHs1'. reflexivity.
    + rewrite <- IHs1'. reflexivity.
Qed.






Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f I n1 n2 H.
  rewrite -> I.
  rewrite <- H.
  rewrite <- I.
  reflexivity.
Qed.





Theorem rev_injective : forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2. intros H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.







Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42
  | a :: l' => match n with
               | 0 => a
               | S n' => nth_bad l' n'
               end
  end.



Inductive natoption : Type :=
  | Some (n : nat)
  | None.



Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n with
               | O => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.





Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.



Definition hd_error (l : natlist) : natoption
  := match l with
     | nil    => None
     | h :: _ => Some h
     end.



Lemma empty_hd_error_3 : hd_error [ ] = None.

Proof.
(* The lemma empty_hd_error_3 is to be proven by rewriting the definition of hd_error
     for the empty list.
*)
  unfold hd_error.
reflexivity.
Qed.

Lemma empty_hd_error_2 : hd_error [ ] = None.




Proof.
(* The lemma empty_hd_error_2 is to be proven.
We will use the definition of hd_error to prove this.
*)
  
intros.
(* We will pattern match on the input list.
*)
  
apply (@empty_hd_error_3 ).
Qed.

Lemma empty_hd_error_1 : hd_error [ ] = None.

Proof.
(* The lemma empty_hd_error_1 is to be proven by rewriting the definition of hd_error
     with the empty list.
*)
  apply (@empty_hd_error_2 ).
Qed.

Lemma empty_hd_error_0 : hd_error [ ] = None.

Proof.
(* The lemma empty_hd_error_0 is to be proven by rewriting the definition of hd_error
     with the empty list.
*)
  intros.
apply (@empty_hd_error_1 ).
Qed.

Example test_hd_error1 : hd_error [] = None.




Proof.
(* We will prove the theorem by structural induction on the input list.
*)
  
apply (@empty_hd_error_0 ).
Qed.
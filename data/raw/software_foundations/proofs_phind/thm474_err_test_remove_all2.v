

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


Example test_remove_all2 : count 5 (remove_all 5 [2;1;4;1]) = 0.

Proof.
(* We will prove the theorem by induction on the input list.
*)
  intros l.
(* We will need to use the IHremove_all, which states that removing all occurrences of an element from a list removes one occurrence at a time.
*)
  (* We will also need to use the IHcount, which states that the count of an element in a list is the sum of the count of that element in the tail of the list and a boolean value indicating whether the head of the list is equal to the element.
*)
  (* The base case is when the list is empty.
In this case, the count of the element in the list is 0.
*)
  induction l as [| n l' IHl'].
- (* l = nil *)
    reflexivity.
- (* l = n :: l' *)
    (* We will consider two cases: when n is equal to the element v and when n is not equal to the element v.
*)
    destruct (n =? v) as [n_eq_v | n_neq_v].
- (* n = v *)
      (* In this case, we remove one occurrence of the element v from the tail of the list l'.
*)
      rewrite IHl'.
(* We then add one to the count of the element v in the tail of the list l'.
*)
      rewrite (Nat.add_comm 1 _).
reflexivity.
- (* n <> v *)
      (* In this case, we remove all occurrences of the element v from the tail of the list l'.
*)
      rewrite IHl'.
(* We then add the count of the element v in the tail of the list l'.
*)
      reflexivity.
Qed.
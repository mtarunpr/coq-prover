

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


Lemma append_empty_list_4 : [1; 2; 3] ++ [ ] = [1; 2; 3].

Proof.
(* We will use the definition of the append operation for lists.
*)
  unfold append.
(* We will also use the definition of the length function.
*)
  unfold length.
(* We will perform induction on the length of the first list.
*)
  induction (length mylist).
- (* For the base case, we have an empty list.
*)
    (* We know that the append of an empty list with another list is the other list.
*)
    reflexivity.
- (* For the inductive case, we have a list of the form h :: t.
*)
    (* We know that the append of a list of this form with another list is the list h :: (append t l).
*)
    (* By the induction hypothesis, we know that (append t l) = t.
*)
    (* Therefore, the append of the entire list is h :: t, which is the original list.
*)
    reflexivity.
Qed.

Lemma append_empty_list_3 : [1; 2; 3] ++ [ ] = [1; 2; 3].




Proof.
(* We will use the definition of the append operation for lists.
*)
  
unfold append.
(* We will also use the definition of the empty list.
*)
  
apply (@append_empty_list_4 ).
Qed.

Lemma append_empty_list_2 : [1; 2; 3] ++ [ ] = [1; 2; 3].

Proof.
(* We will use the definition of the append operation for lists.
*)
  unfold append.
(* We will also use the definition of the empty list.
*)
  apply (@append_empty_list_3 ).
Qed.

Lemma append_empty_list_1 : [1; 2; 3] ++ [ ] = [1; 2; 3].

Proof.
(* We will use the definition of the append operation for lists.
*)
  unfold append.
(* We will also use the definition of the empty list.
*)
  apply (@append_empty_list_2 ).
Qed.

Lemma append_empty_list_0 : [1; 2; 3] ++ [ ] = [1; 2; 3].

Proof.
(* We will use the definition of the append operation for lists.
*)
  unfold append.
(* We will also use the definition of the cons operator.
*)
  apply (@append_empty_list_1 ).
Qed.

Example test_app3 : [1;2;3] ++ nil = [1;2;3].




Proof.
(* We will proceed by induction on the first list.
*)
  
apply (@append_empty_list_0 ).
Qed.
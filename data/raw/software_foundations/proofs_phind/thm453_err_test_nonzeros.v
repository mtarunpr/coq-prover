

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



Example test_nonzeros : nonzeros [0;1;0;2;3;0;0] = [1;2;3].

Proof.
(* We will proceed by induction on the input list.
*)
  intros l.
(* We will need to define the induction hypothesis.
*)
  induction l as [| n l' IHl'].
(* For the base case, we need to show that nonzeros of an empty list is an empty list.
*)
  - (* The base case is trivial since the definition of nonzeros on nil is nil.
*)
    reflexivity.
(* For the inductive case, we need to show that nonzeros of a non-empty list is either the nonzeros of the tail or the head followed by the nonzeros of the tail.
*)
  - (* We will first consider the case where the head of the list is zero.
*)
    destruct n as [n'].
+ (* In this case, we know that nonzeros of the tail is IHl'.
*)
      (* We also know that nonzeros of the list is nonzeros of the tail.
*)
      (* Therefore, we can rewrite nonzeros of the list as IHl'.
*)
      rewrite IHl'.
(* Since n' is zero, we know that the head of the list is zero.
*)
      (* Therefore, nonzeros of the list is nonzeros of the tail, which is IHl'.
*)
      reflexivity.
(* We will now consider the case where the head of the list is not zero.
*)
    + (* In this case, we know that nonzeros of the tail is IHl'.
*)
      (* We also know that nonzeros of the list is the head followed by nonzeros of the tail.
*)
      (* Therefore, we can rewrite nonzeros of the list as the head followed by IHl'.
*)
      rewrite <- IHl'.
(* Since n' is not zero, we know that the head of the list is not zero.
*)
      (* Therefore, nonzeros of the list is the head followed by nonzeros of the tail, which is the head followed by IHl'.
*)
      reflexivity.
Qed.
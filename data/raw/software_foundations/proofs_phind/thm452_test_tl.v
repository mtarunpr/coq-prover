

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


Lemma helper_lemma_appending_last_elements_1 : forall n n' : nat, forall l' : natlist, forall IHl : tl [1; 2; 3] = [2; 3], [2; 3] = [2; 3].

Proof.
(* We are proving a lemma about appending the last elements of two lists.
The lemma states that if we have a list [1; 2; 3] and another list l',
     and we know that the tail of [1; 2; 3] is [2; 3], then [2; 3] is equal to [2; 3].
This is a trivially true statement because the statement is just restating the
     given premise.
*)
  intros n n' l' IHl.
reflexivity.
Qed.

Lemma helper_lemma_appending_singleton_0 : forall n : nat, forall l : natlist, forall IHl : tl [1; 2; 3] = [2; 3], [2; 3] = [2; 3].

Proof.
(* We will proceed by induction on the list l.
*)
  intros n l IHl.
(* We will need to prove the base case when l is nil and the inductive case when l is cons.
*)
  destruct l as [| n' l'].
(* Base case: l is nil.
*)
  - simpl.
reflexivity.
(* Inductive case: l is cons.
*)
  - simpl.
apply (@helper_lemma_appending_last_elements_1 n n' l' IHl).
Qed.

Example test_tl : tl [1;2;3] = [2;3].

Proof.
(* We will proceed by induction on the list.
*)
  induction mylist as [| n l IHl]; intros.
(* Base case: when the list is [1;2;3], we have *)
  (* tl [1;2;3] = [2;3] by definition of tl.
*)
  - reflexivity.
(* Inductive case: when the list is of the form n :: l, we have *)
  (* tl (n :: l) = tl l by definition of tl.
We will now use the induction hypothesis IHl.
*)
  - simpl.
apply (@helper_lemma_appending_singleton_0 n l IHl).
Qed.
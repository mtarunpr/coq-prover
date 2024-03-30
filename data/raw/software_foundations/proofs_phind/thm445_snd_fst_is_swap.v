

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






Lemma lemma_swap_pair_inverse_2 : forall p : natprod, (snd p, fst p) = swap_pair p.

Proof.
intros p.
unfold swap_pair.
unfold fst, snd.
destruct p as [n m].
simpl.
reflexivity.
Qed.

Lemma lemma_swap_pair_inverse_1 : forall p : natprod, (snd p, fst p) = swap_pair p.




Proof.
(* The lemma states that for any pair p, the pair of the second and first
     elements of p is equal to the result of swapping p.
We will proceed by
     induction on p.
*)
  
intros p.
(* We first need to rewrite p in terms of the constructors of the
     inductive type natprod.
*)
  
apply (@lemma_swap_pair_inverse_2 p).
Qed.

Lemma lemma_swap_pair_inverse_0 : forall p : natprod, (snd p, fst p) = swap_pair p.

Proof.
(* We will proceed by induction on p.
*)
  intros p.
(* We will then destruct p into its components.
*)
  apply (@lemma_swap_pair_inverse_1 p).
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.




Proof.
(*
    We will proceed by induction on p.
The base case will be when p is (pair n m).
In this case, we will show that (m, n) = swap_pair (pair n m).
The inductive case will be when p is (pair n m) for some n, m.
In this case, we will show that (snd p, fst p) = swap_pair p.
*)
  
intros p.
apply (@lemma_swap_pair_inverse_0 p).
Qed.
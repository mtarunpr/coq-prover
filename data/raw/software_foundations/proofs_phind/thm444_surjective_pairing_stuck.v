

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





Lemma nat_equality_reflexive_1 : forall n m : nat, (n, m) = (n, m).

Proof.
(* The goal is to prove that (n, m) = (n, m).
This is a trivial statement because
     the left-hand side and the right-hand side are the same term.
*)
  intros n m.
reflexivity.
Qed.

Lemma lemma_nat_pair_equality_0 : forall n m : nat, (n, m) = (fst (n, m), snd (n, m)).

Proof.
intros n m.
unfold fst, snd.
unfold fst', snd'.
unfold swap_pair.
apply (@nat_equality_reflexive_1 n m).
Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).

Proof.
intros p.
(* We will use the definition of the pair type and the fst and snd functions to rewrite p in a way that allows us to apply the surjective_pairing' theorem.
*)
  destruct p as [n m].
(* Now we have n and m, we can rewrite p using the fst' and snd' functions.
*)
  apply (@lemma_nat_pair_equality_0 n m).
Qed.
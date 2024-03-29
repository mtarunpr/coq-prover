

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
(* The theorem states that the pair (n,m) is equal to the result of reconstructing
     a pair from its constituent parts using `fst` and `snd`.
This follows directly from the definitions of `fst` and `snd`, which return the
     first and second elements of the pair, respectively.
Using the definition of
     pairing, the pair (n,m) is the same as the pair (fst (n,m), snd (n,m)).
We can prove this by reflexivity as the equality is evident from the definitions.
*)
  intros n m.
(* We introduce n and m to allow specific reasoning about them.
*)
  simpl.
(* Simplify the expressions to make the equality obvious if possible.
*)
  reflexivity.
(* Apply reflexivity of equality, which should complete the proof.
*)

Qed.
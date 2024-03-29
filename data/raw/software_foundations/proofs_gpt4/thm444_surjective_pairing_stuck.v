

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
(* We'll prove this by destructing `p` due to its inductive nature as a pair *)
  intros p.
destruct p as [n m].
(* Now that we've broken `p` into its components `(n, m)`, 
     we can directly check that `fst (n, m)` and `snd (n, m)` are `n` and `m` respectively *)
  simpl.
(* Now we can conclude that `(n, m)` is indeed equal to `(n, m)` *)
  reflexivity.
Qed.
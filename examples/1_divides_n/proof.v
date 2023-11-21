Require Import Arith.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Wf_nat.
 
Inductive divides : nat -> nat -> Prop :=
    dividesDef : forall a b q : nat, b = q * a -> divides a b.

Lemma helper_lemma_0 : forall n : nat, n = n * 1.

Proof.


  (* We use the fact that n * 1 = n for all natural numbers n. 
     This is a property of multiplication by 1, and in Coq it's automatically solved by the `ring` tactic. *)
  intro n.
  ring.


Qed.

Lemma SO_divides_all : forall n : nat, divides 1 n.


Proof.


  (* To show that 1 divides any natural number n, we use the constructor dividesDef. *)
  intros n.
  (* We instantiate the "divides" predicate with 1, n, and n itself, since n = n * 1 is always true. *)
  apply (dividesDef 1 n n).
  (* We now prove that n = n * 1, which is a direct application of the arithmetic identity. *)
  (* We can use simpl to prove it or use ring simplification to handle the arithmetic expression. *)
  simpl. apply (@helper_lemma_0 n).

Qed.
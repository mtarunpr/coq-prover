Require Import Arith.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Wf_nat.
 
Inductive divides : nat -> nat -> Prop :=
    dividesDef : forall a b q : nat, b = q * a -> divides a b.



Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Lia.
From LF Require Import Maps.
From LF Require Import Imp.





Theorem ceval_deterministic : forall c st st1 st2,
  st =[ c ]=> st1  ->
  st =[ c ]=> st2 ->
  st1 = st2.

Proof.
(*
     We will proceed by induction on the evaluation relation.
The base case will deal with the "skip" instruction.
The inductive case will deal with the "assign" and "seq" instructions.
*)
  intros c st st1 st2 H1 H2.
generalize dependent st2.
induction H1 as [ | st' c' H1' IH].
- (* skip case *)
    intros st2 H2.
specialize (H2 st').
inversion H2.
- (* assign case *)
    intros st2 H2.
specialize (H2 st').
specialize (IH st' H1' H2).
rewrite IH.
reflexivity.
- (* seq case *)
    intros st2 H2.
specialize (H2 st').
specialize (IH st' H1' H2).
rewrite IH.
reflexivity.
Qed.


Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.



Check (3 = 3) : Prop.

Check (forall n m : nat, n + m = m + n) : Prop.



Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.





Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.



Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.



Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.





Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.



Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.



Lemma one_equals_one_implies_zero_equals_zero_1 : forall H : 1 = 1, 0 = 0.

Proof.
(* The goal is to prove 0 = 0.
Since this is a trivially true statement, we can use the axiom of reflexivity to prove it.
*)
  reflexivity.
Qed.

Lemma nat_successor_injective_0 : forall n1 : nat, S n1 = 1 -> n1 = 0.

Proof.
(*
    We will prove the lemma by induction on n1.
The base case will be when n1 = 0.
The inductive case will be when n1 = S n2 for some n2.
*)
  intros n1 H.
induction n1 as [| n2 IHn2].
(*
    Base case: n1 = 0
    We know that S 0 = 1, so H is 1 = 0, which is false.
Therefore, we can't have n1 = 0.
*)
  - apply (@one_equals_one_implies_zero_equals_zero_1 H).
- discriminate H.
Qed.

Lemma succ_inj : injective S.

Proof.
(* We will prove that the successor function is injective by proving that
     if S n1 = S n2, then n1 = n2.
*)
  intros n1 n2.
(* We will use the induction principle for the natural numbers.
*)
  induction n2 as [|n2' IHn2'].
- (* Base case: n2 = 0.
*)
    (* We know that S n1 = S 0.
*)
    (* Since n1 = 0, S n1 = S 0.
*)
    (* Therefore, n1 = 0.
*)
    apply (@nat_successor_injective_0 n1).
- (* Inductive case: n2 = S n2'.
*)
    (* We know that S n1 = S (S n2').
*)
    (* By the induction hypothesis, we have IHn2' : S n1 = S n2' -> n1 = n2'.
*)
    (* We want to prove that n1 = S n2'.
*)
    (* We have S n1 = S (S n2').
*)
    (* By the injectivity of S, we have n1 = S n2'.
*)
    apply IHn2' in H.
(* Now we have S n1 = S n2' by the injectivity of S.
*)
    (* Therefore, n1 = S n2'.
*)
    reflexivity.
Qed.
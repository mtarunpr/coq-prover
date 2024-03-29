



Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.






Definition relation (X: Type) := X -> X -> Prop.





Print le.

Check le : nat -> nat -> Prop.
Check le : relation nat.












Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.


Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Check next_nat : relation nat.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1. inversion H2.
  reflexivity.  Qed.





Lemma impossible_zero_equals_one_from_uniquely_bounded_nats_1 : (forall x y1 y2 : nat, x <= y1 -> x <= y2 -> y1 = y2) ->
0 = 1.

Proof.
intros H_unique.
(* We use the unique property on 0, 0 and 1 to imply that 0 = 1.
*)
  assert (H_zero_one: 0 = 1).
{
    apply H_unique with (x := 0) (y1 := 0) (y2 := 1).
- apply le_n.
(* This proves that 0 <= 0 *)
    - apply le_S.
apply le_n.
(* This proves that 0 <= 1 *)
  }

  (* At this point, H_zero_one constitutes a contradiction, as it states that 0 = 1.
We essentially use the contradiction to derive the proof.
*)
  exact H_zero_one.
Qed.

Lemma contradicting_zero_one_equality_0 : forall H : forall x y1 y2 : nat,
x <= y1 -> x <= y2 -> y1 = y2, 0 = 1.




Proof.
apply (@impossible_zero_equals_one_from_uniquely_bounded_nats_1 ).
Qed.

Lemma contradicting_zero_one_equality_1 : forall H : forall x y1 y2 : nat,
x <= y1 -> x <= y2 -> y1 = y2, 0 = 1.

Proof.
(* Introduce the hypothesis H *)
  intro H.
(* Use the hypothesis H with x := 0, y1 := 0, and y2 := 1, and apply O_le_n to prove 0 <= 0 and 0 <= 1 *)
  specialize (H 0 0 1).
apply H.
- apply le_n.
- apply O_le_n.
Qed.

Lemma contradicting_zero_one_equality_2 : forall H : forall x y1 y2 : nat,
x <= y1 -> x <= y2 -> y1 = y2, 0 = 1.

Proof.
(* We will prove this by contradiction by applying the hypothesis H to
     specific values of x, y1, and y2, where y1 and y2 have distinct values
     that are both bounds for x.
This will lead us to a contradiction since
     we will deduce that two distinct numbers are equal.
*)

  (* We introduce the hypothesis H to our context *)
  intros H.
(* We will use 0 as the value for x, 0 for y1, and 1 for y2.
According to H,
     if 0 <= 0 and 0 <= 1, then 0 = 1, which is a contradiction.
*)
  assert (zero_le_zero : 0 <= 0) by constructor.
(* 0 is less than or equal to itself *)
  assert (zero_le_one : 0 <= 1).
(* 0 is less than or equal to 1 *)
  {
    constructor.
(* Use the definition of <= *)
    constructor.
(* 0 <= S 0 *)
  }
  specialize (H 0 0 1 zero_le_zero zero_le_one).
(* Our goal 0 = 1 follows directly from the specialized hypothesis H.
*)
  exact H.
Qed.

Theorem le_not_a_partial_function : ~ (partial_function le).

Proof.
unfold partial_function.
(* Unfold the definition to work with it *)
  intro H.
(* Assume H is our hypothesis that le is a partial_function *)
  assert (Heq : 0 = 1).
(* Assert that 0 equals to 1 for deriving a contradiction *)
  {
    apply H with (x := 0);   (* Apply our hypothesis to the specific case where x is 0 *)
      apply le_n             (* It is true that 0 <= 0 *)
    | apply le_S, le_n.
(* It is also true that 0 <= 1 *)
  }
  discriminate Heq.
(* 0 = 1 leads to contradiction since they are distinct naturals *)




Qed.





Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Lists.











Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).





Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).



Check list : Type -> Type.



Check (nil nat) : list nat.



Check (cons nat 3 (nil nat)) : list nat.



Check nil : forall X : Type, list X.



Check cons : forall X : Type, X -> list X -> list X.





Check (cons nat 2 (cons nat 1 (nil nat)))
      : list nat.



Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.



Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.





Example test_repeat2 : repeat bool false 1 = cons bool false (nil bool).

Proof.
(*
    We will proceed by induction on the count argument of the repeat function.
The base case will be when count is 0, and the inductive case will be when
    count is the successor of some other natural number.
*)
  intros.
induction count as [|n count_ih].
- (* Base case: count = 0 *)
    (* Since count is 0, repeat returns the empty list for any type and element.
*)
    reflexivity.
- (* Inductive case: count = S n *)
    (* In this case, repeat returns a list with one element, followed by the result
       of calling repeat with the same element and the predecessor of count.
*)
    simpl.
(* We now need to prove that cons X x (repeat X x count') = cons X x (cons X x (repeat X x n)).
To do this, we'll use the induction hypothesis count_ih, which states that
       repeat X x n = cons X x (repeat X x n).
We'll rewrite this to cons X x (cons X x (repeat X x n')),
       where n' is the predecessor of n.
Then, we'll use this to rewrite the left-hand side of our goal.
*)
    rewrite (IHcount_ih count_ih).
(* Now our goal is cons X x (cons X x (repeat X x n)) = cons X x (cons X x (cons X x (repeat X x n'))).
This is true by definition of cons and repeat.
*)
    reflexivity.
Qed.
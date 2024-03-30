




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





Example test_repeat1 : repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).

Proof.
(* We will proceed by induction on the count argument of the repeat function.
*)
  induction 2 as [|n' IHn'].
- (* Base case: count = 0 *)
    (* We need to prove that repeat nat 4 0 = nil nat *)
    reflexivity.
- (* Inductive case: count = S n' *)
    (* We need to prove that repeat nat 4 (S n') = cons nat 4 (repeat nat 4 n') *)
    (* By the IHn', we know that repeat nat 4 n' = cons nat 4 (repeat nat 4 n').
Now we just need to prove that *)
    (* cons nat 4 (repeat nat 4 n') = cons nat 4 (cons nat 4 (repeat nat 4 n')).
This is true by definition of cons.
*)
    reflexivity.
Qed.
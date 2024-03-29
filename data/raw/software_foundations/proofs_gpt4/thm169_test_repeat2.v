




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
(* Apply the definition of 'repeat' with count = 1.
This unfolds the definition once, resulting in 'cons bool false (repeat bool false 0)'.
*)
  simpl.
(* Now apply the definition of 'repeat' with count = 0.
This unfolds it again to 'cons bool false (nil bool)'.
*)
  reflexivity.
Qed.
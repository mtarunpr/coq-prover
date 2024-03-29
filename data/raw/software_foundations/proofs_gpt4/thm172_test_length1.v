




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



Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.



Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).


Eval compute in d mumble (b a 5).
Eval compute in d bool (b a 5).
Eval compute in e bool true.
Eval compute in e mumble (b c 0).
End MumbleGrumble.







Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.



Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.








Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.



Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).



Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).






Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.



Definition list123'' := cons 1 (cons 2 (cons 3 nil)).



Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.



Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').





Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.



Example test_length1 : length (cons 1 (cons 2 (cons 3 nil))) = 3.

Proof.
(* The length of a list constructed by cons-ing three elements to nil is 3 because: *)
  (* 1.
cons adds one element to the head of the list, so (cons 3 nil) has length 1 *)
  (* 2.
(cons 2 (cons 3 nil)) adds another element, making the list have length 2 *)
  (* 3.
(cons 1 (cons 2 (cons 3 nil))) adds one more element, resulting in length 3 *)
  simpl.
(* Applying the definition of length simplifies the expression directly to 3 *)
  reflexivity.
(* The simplified expression equals the expected result *)

Qed.
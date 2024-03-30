





















Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.



Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.





Compute (next_weekday friday).


Compute (next_weekday (next_weekday saturday)).






Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.



Proof. simpl. reflexivity.  Qed.









From Coq Require Export String.






Inductive bool : Type :=
  | true
  | false.



Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.





Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb2:  (orb false false) = false.
Proof. simpl. reflexivity.  Qed.
Example test_orb3:  (orb false true)  = true.
Proof. simpl. reflexivity.  Qed.
Example test_orb4:  (orb true  true)  = true.
Proof. simpl. reflexivity.  Qed.



Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:  false || false || true = true.
Proof. simpl. reflexivity. Qed.





Definition negb' (b:bool) : bool :=
  if b then false
  else true.

Definition andb' (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1:bool) (b2:bool) : bool :=
  if b1 then true
  else b2.





Definition nandb (b1:bool) (b2:bool) : bool
  := negb (b1 && b2).

Example test_nandb1:               (nandb true false) = true.
Proof. reflexivity.  Qed.


Example test_nandb2 : (nandb false false) = true.

Proof.
(* We will prove test_nandb2 by applying the definition of nandb and simplifying the resulting expression.
*)
  unfold nandb.
(* The goal is now: (negb (andb false false)) = true *)
  simpl.
(* The goal is now: negb false = true *)
  unfold negb.
(* The goal is now: if false then false else true = true *)
  simpl.
(* The goal is now: true = true *)
  reflexivity.
Qed.
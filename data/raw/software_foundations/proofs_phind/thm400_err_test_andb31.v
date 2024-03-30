





















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
Example test_nandb2:               (nandb false false) = true.
Proof. reflexivity.  Qed.
Example test_nandb3:               (nandb false true) = true.
Proof. reflexivity.  Qed.
Example test_nandb4:               (nandb true true) = false.
Proof. reflexivity.  Qed.




Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool
  := b1 && (b2 && b3).



Example test_andb31 : (andb3 true true true) = true.

Proof.
(* We will prove the theorem by structural induction on the first boolean value (b1).
*)
  intros b1 b2 b3 Hb1 Hb2 Hb3.
(* We will need to use the definition of andb3.
*)
  simpl.
(* We will now consider the two possible cases for b1: true and false.
*)
  destruct b1 as [Hb1_true | Hb1_false].
(* Case 1: b1 is true.
*)
  - (* In this case, andb3 b1 (b2 && b3) is true because b1 is true.
*)
    simpl in Hb1_true.
(* We now need to prove b2 && b3.
*)
    destruct b2 as [Hb2_true | Hb2_false].
- (* Case 1.1: b2 is true.
*)
      simpl in Hb2_true.
(* We now need to prove b3.
*)
      destruct b3 as [Hb3_true | Hb3_false].
- (* Case 1.1.1: b3 is true.
*)
        simpl in Hb3_true.
(* The result is true because true && true && true is true.
*)
        reflexivity.
- (* Case 1.1.2: b3 is false.
*)
        simpl in Hb3_false.
(* The result is false because true && true && false is false.
*)
        reflexivity.
- (* Case 1.2: b2 is false.
*)
      simpl in Hb2_false.
(* The result is false because true && false && b3 is false.
*)
      reflexivity.
(* Case 2: b1 is false.
*)
  - (* In this case, andb3 b1 (b2 && b3) is false because b1 is false.
*)
    simpl in Hb1_false.
(* The result is false because false && b2 && b3 is false.
*)
    reflexivity.
Qed.
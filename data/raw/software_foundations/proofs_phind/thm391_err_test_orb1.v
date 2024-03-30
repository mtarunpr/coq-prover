





















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







Example test_orb1 : (orb true  false) = true.

Proof.
(*
    We will prove the theorem by structural induction on the first argument of orb.
The base case will be when the first argument is true, and the inductive case will be when the first argument is false.
*)
  intros.
(*
    Base case: orb true b2 = true.
Since the first argument is true, the result is true regardless of the value of b2.
*)
  reflexivity.
(*
    Inductive case: orb false b2 = orb b2 true.
We will prove this by applying the definition of orb to the inductive hypothesis.
*)
  intros.
(*
    We now have b2 as the first argument and true as the second argument.
By the definition of orb, the result is b2.
*)
  reflexivity.
Qed.
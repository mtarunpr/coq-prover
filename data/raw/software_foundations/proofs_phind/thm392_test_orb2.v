





















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


Lemma orb_false_false_2 : orb false false = false.

Proof.
(* We will perform a case analysis on the first argument of orb.
*)
  intros.
(* When the first argument is false, we need to prove that orb false false = false.
*)
  simpl.
(* This is trivial because the definition of orb states that when the first argument is false,
     the result is the second argument.
In this case, the second argument is also false.
*)
  reflexivity.
Qed.

Lemma orb_false_false_1 : orb false false = false.

Proof.
(* We will perform a case analysis on the first argument of orb.
*)
  intros.
(* When the first argument is false, we can destruct it to get the result of the second argument.
*)
  apply (@orb_false_false_2 ).
Qed.

Lemma orb_false_false_0 : orb false false = false.

Proof.
(* We will perform a case analysis on the first argument of orb.
*)
  intros.
(* When the first argument is false, we can destruct it to get the result of the second argument.
*)
  apply (@orb_false_false_1 ).
Qed.

Example test_orb2 : (orb false false) = false.




Proof.
(* We will use induction on the first argument of orb.
*)
  
apply (@orb_false_false_0 ).
Qed.
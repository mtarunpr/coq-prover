





















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


Lemma orb_true_true_0 : orb true true = true.

Proof.
(* Base case: We want to prove that (orb true true) = true.
We can do this by pattern matching on the definition of (orb true true).
*)
  simpl.
reflexivity.
Qed.

Example test_orb4 : (orb true  true)  = true.




Proof.
(* We will use induction on the first boolean value of the orb function *)
  
apply (@orb_true_true_0 ).
Qed.
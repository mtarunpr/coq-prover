





















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


Lemma bool_symmetry_2 : orb false true = true.

Proof.
(* We will use the definition of orb to prove this lemma.
We need to show that
     orb false true is equal to true.
We can do this by pattern matching on the
     definition of orb.
*)
  unfold orb.
(* Now we have the definition of orb with b1 = false and b2 = true.
Since b1 is
     false, the match construct will return the second case, which is true.
*)
  reflexivity.
Qed.

Lemma bool_symmetry_1 : orb false true = true.




Proof.
(* We will use the definition of orb to prove this lemma.
We will pattern match on the first argument of orb.
*)
  
intros.
apply (@bool_symmetry_2 ).
Qed.

Lemma bool_symmetry_0 : orb false true = true.




Proof.
(* We will use the definition of orb to prove this lemma.
We will pattern match on the first argument of orb.
*)
  
intros.
apply (@bool_symmetry_1 ).
Qed.

Example test_orb3 : (orb false true)  = true.




Proof.
(* We will prove test_orb3 by structural induction on the first argument of orb.
*)
  
intros.
(* Case analysis on the first argument of orb.
*)
  
apply (@bool_symmetry_0 ).
Qed.
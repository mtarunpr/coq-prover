





















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








Example test_next_weekday : (next_weekday (next_weekday saturday)) = tuesday.

Proof.
(* Both applications of next_weekday are reduced by computation.
*)
  simpl.
(* After simplification, the goal is to show that tuesday = tuesday, which is true by reflexivity.
*)
  reflexivity.
Qed.
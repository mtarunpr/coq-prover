





















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








Lemma next_weekday_of_saturday_is_tuesday_0 : next_weekday (next_weekday saturday) = tuesday.

Proof.
(*
    To prove this lemma, we will use the definition of next_weekday and pattern matching.
We want to show that next_weekday (next_weekday saturday) is equal to tuesday.
We know that next_weekday saturday is equal to monday (from the definition of next_weekday).
So, we want to show that next_weekday monday is equal to tuesday.
This is true according to the definition of next_weekday.
*)
  apply (eq_refl (next_weekday (next_weekday saturday))).
Qed.

Example test_next_weekday : (next_weekday (next_weekday saturday)) = tuesday.

Proof.
(* We will use pattern matching to destruct the input of the function next_weekday.
*)
  apply (@next_weekday_of_saturday_is_tuesday_0 ).
Qed.
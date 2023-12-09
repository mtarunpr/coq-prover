Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint sum_natural_numbers (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => n + sum_natural_numbers n'
  end.

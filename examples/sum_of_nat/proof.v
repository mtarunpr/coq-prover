Require Import Coq.Lists.List.
Import ListNotations.

Fixpoint sum_natural_numbers (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => n + sum_natural_numbers n'
  end.

Lemma sum_natural_numbers_succ :
  forall n'_0 : forall n' : nat, forall IH : 2 * sum_natural_numbers n' = n' * (n' + 1), S
  (n' + sum_natural_numbers n' +
   S (n' + sum_natural_numbers n' + 0)) =
S (n' + 1 + n' * S (n' + 1)).

Proof.

(* First, we introspect the hypotheses and the variable *)
intros n'.
(* Now we've got `n' : nat` and a hypothesis `IHn' : 2 * sum_natural_numbers n' = n' * (n' + 1)` to work with.
   We begin by simplifying the expressions in the goal using basic arithmetic simplifications and the induction hypothesis. *)
simpl.
(* We need the associativity and commutativity of addition, and the induction hypothesis `IHn'`. *)
rewrite <- IHn'.
(* We can simplify our goal by observing that the left-hand side of the equality can be rewritten to match the right-hand side *)
rewrite <- plus_n_Sm.
(* To match the form on the right, we rewrite the goal further *)
rewrite plus_Sn_m.
(* We apply the distributive property of multiplication over addition *)
rewrite <- mult_plus_distr_l.
(* Now we have a goal that can be solved by straightforward reflexivity *)
reflexivity.

Qed.

Theorem sum_of_natural_numbers : forall n : nat,
  2 * (sum_natural_numbers n) = n * (n + 1).


Proof.


  (* We will prove the theorem by induction on n *)
  induction n as [| n' IH].
  - (* Base case: n = 0 *)
    simpl. reflexivity.
  - (* Inductive step: Assume the hypothesis holds for n', prove for S n' *)
    simpl.
    apply (@sum_natural_numbers_succ n' IH).

Qed.
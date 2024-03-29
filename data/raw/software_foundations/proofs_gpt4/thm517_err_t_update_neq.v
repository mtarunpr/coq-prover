








From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Datatypes.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.





Locate "+".



Print Init.Nat.add.










Check String.eqb_refl :
  forall x : string, (x =? x)%string = true.


Check String.eqb_eq :
  forall n m : string, (n =? m)%string = true <-> n = m.
Check String.eqb_neq :
  forall n m : string, (n =? m)%string = false <-> n <> m.
Check String.eqb_spec :
  forall x y : string, reflect (x = y) (String.eqb x y).








Definition total_map (A : Type) := string -> A.





Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).



Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.





Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.




Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).


Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).



Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).



Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.









Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
  (_ !-> v) x = v.
Proof.
  reflexivity. Qed.




Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite eqb_refl. reflexivity.
Qed.






Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.

Proof.
(* To prove this theorem, we'll use the fact that if x1 and x2 are different,
     then updating the map at x1 should not affect the value at x2.
*)
  intros A m x1 x2 v Hneq.
(* We will perform case analysis on whether x2 equals x1 or not.
*)
  unfold t_update.
(* The function (t_update _ _ _) is defined by a conditional expression,
     so we can reason about what happens when the condition (beq_string x1 x2)
     is true or false.
*)
  destruct (beq_string x1 x2) eqn:Heq.
- (* If beq_string x1 x2 evaluates to true, we have a contradiction because
       we assumed that x1 and x2 are different.
We use the false case of the
       equality to derive a contradiction.
*)
    apply beq_string_true_iff in Heq.
contradiction.
- (* If beq_string x1 x2 evaluates to false, this case aligns with our assumption
       that x1 and x2 are different.
Therefore, the result of the update function
       will yield m x2, as the condition for changing the value to v will not be met.
*)
    reflexivity.
Qed.









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






Lemma update_same_key_returns_value_2 : forall A : Type, forall m : total_map A, forall x : string, forall v : A, (if (x =? x)%string then v else m x) = v.

Proof.
intros A m x v.
(* Using the fact that string equality is reflexive.
*)
  rewrite String.eqb_refl.
reflexivity.
Qed.

Lemma update_same_key_returns_value_1 : forall A : Type, forall m : total_map A, forall x : string, forall v : A, (if (x =? x)%string then v else m x) = v.

Proof.
intros A m x v.
apply (@update_same_key_returns_value_2 A m x v).
Qed.

Lemma update_same_key_returns_value_0 : forall A : Type, forall m : total_map A, forall x : string, forall v : A, (if (x =? x)%string then v else m x) = v.

Proof.
(* The proof proceeds by introspection and simplification, because
     we have an if-statement that checks the equality of a string with itself.
*)
  intros A m x v.
(* We simplify the equality comparison of the same strings.
*)
  simpl.
(* Since x =? x will always return true, the if-statement simplifies
     to the first branch which is just 'v', which concludes the proof.
*)
  apply (@update_same_key_returns_value_1 A m x v).
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.

Proof.
(* Using the definition of t_update, we want to prove that updating a map at key `x` with value `v`
     will yield the value `v` when we lookup `x` in the updated map.
*)

  (* Introduce the variables into the context *)
  intros A m x v.
(* Unfold the definition of t_update to proceed with case analysis on string equality *)
  unfold t_update.
(* Observe that when the key is equal to `x`, the if condition evaluates to true,
     and we should return the value `v` we just put in our total_map *)
  apply (@update_same_key_returns_value_0 A m x v).
Qed.









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
(* The lemma states that for any type A, any string x, and any value v of type A,
     if we have a total mapping that maps every string to v, then the result of applying
     this mapping to any string x must be v.
*)

  (* This proof is straightforward since the definition of (_ !-> v) is a function that takes any string
     and returns v.
Therefore, applying this function to any string x will yield v.
*)

  intros A x v.
unfold t_update.
unfold t_empty.
reflexivity.
Qed.









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
(*
    We will proceed by induction on m, the total_map.
The base case will be when m is empty, and the inductive case
    will be when m is a non-empty map.
*)
  intros A m x v.
induction m as [|x' v' m' IH].
(*
    Base case: m is empty.
In this case, we know that (_ !-> v) x = v, by the t_apply_empty lemma.
*)
  - simpl.
apply t_apply_empty.
(*
      Inductive case: m is a non-empty map.
We will split into two cases: when x = x' and when x ≠ x'.
*)
  - destruct (x = x') eqn:E.
(*
      Case 1: x = x'.
In this case, we know that (x' !-> v' ; m') x = v', by the IH.
Since x = x', we can substitute x' with x in this equation to get
      (x !-> v' ; m') x = v'.
*)
    + subst x'.
rewrite IH.
reflexivity.
(*
      Case 2: x ≠ x'.
In this case, we know that (x' !-> v' ; m') x = m' x, by the IH.
Since x ≠ x', we can't have (x' !-> v' ; m') x = v, so we have a contradiction.
*)
    + assert (x' !-> v' ; m') x = m' x by reflexivity.
assert (x' !-> v' ; m') x = v by contradiction.
rewrite H in H0.
rewrite H0 in H.
clear H0.
subst x'.
rewrite H.
reflexivity.
Qed.
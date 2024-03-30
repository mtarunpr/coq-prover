








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
  intros A m x1 x2 v H.
  unfold t_update. destruct (eqb_spec x1 x2). exfalso. apply H. apply e. reflexivity.
Qed.




Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  apply functional_extensionality. intros x'.
  unfold t_update.
  destruct (eqb_spec x x') as [_ | _]. reflexivity. reflexivity.
Qed.





Theorem t_update_same : forall (A : Type) (m : total_map A) x,
  (x !-> m x ; m) = m.

Proof.
(* We will proceed by induction on m.
*)
  intros A m x.
induction m as [|x' v' m' IHm'].
(* Base case: m is empty.
*)
  - simpl.
reflexivity.
(* Inductive case: m is an update.
*)
  - simpl.
(* We need to show that (x' !-> v' ; x !-> m' x ; m') x = m' x.
*)
    (* Case 1: x = x', in which case the result is trivial.
*)
    - intros.
reflexivity.
(* Case 2: x <> x', in which case we can use the induction hypothesis.
*)
    - intros.
(* We need to show that (x' !-> v' ; x !-> m' x ; m') x = m' x.
*)
      (* By the definition of the update function, this is the same as showing that *)
      (* (x' !-> v' ; m') x = m' x.
*)
      (* By the induction hypothesis, this follows.
*)
      rewrite IHm'.
reflexivity.
Qed.
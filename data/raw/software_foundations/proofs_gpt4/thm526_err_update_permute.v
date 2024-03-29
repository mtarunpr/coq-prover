








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
  intros A m x.
  apply functional_extensionality.
  intros x'.
  unfold t_update.
  destruct (eqb_spec x x') as [H | _]. rewrite H. reflexivity. reflexivity.
Qed.




Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m)
  =
  (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 H.
  apply functional_extensionality.
  intros x'.
  unfold t_update.
  destruct (eqb_spec x1 x') as [H1 | H1].
  - destruct (eqb_spec x2 x') as [H2 | _].
    + exfalso. apply H. rewrite H1. rewrite H2. reflexivity.
    + reflexivity.
  - destruct (eqb_spec x2 x') as [H2 | H2].
    + reflexivity.
    + reflexivity.
Qed.







Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).


Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).


Notation "x '|->' v" := (update empty x v)
  (at level 100).

Definition examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).



Lemma apply_empty : forall (A : Type) (x : string),
  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
  x2 <> x1 ->
  (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
  m x = Some v ->
  (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.



Lemma unique_key_implies_equal_values_2 : forall A : Type, forall m : partial_map A, forall x1 x2 : string, forall v1 v2 : A, forall x : string, forall Hneq : x <> x1, forall e : x1 = x, forall e0 : x2 = x, x = x1.

Proof.
(* Direct proof using the given equality `e : x1 = x`.
*)
  intros A m x1 x2 v1 v2 x Hneq e e0.
rewrite <- e.
reflexivity.
Qed.

Lemma swap_disjoint_keys_in_partial_map_1 : forall A : Type, forall m : partial_map A, forall x1 x2 : string, forall v1 v2 : A, forall Hneq : x2 <> x1, forall x : string, forall e : x1 = x, forall e0 : x2 = x, (x1 |-> v1; x2 |-> v2; m) x =
(x2 |-> v2; x1 |-> v1; m) x.

Proof.
intros A m x1 x2 v1 v2 Hneq x e e0.
rewrite e.
rewrite e0 in Hneq.
contradiction Hneq.
apply (@unique_key_implies_equal_values_2 A m x1 x2 v1 v2 x Hneq e e0).
Qed.

Lemma swap_disjoint_keys_in_partial_map_0 : forall A : Type, forall m : partial_map A, forall x1 x2 : string, forall v1 v2 : A, forall Hneq : x2 <> x1, forall x : string, forall e : x1 = x, forall e0 : x2 = x, (x1 |-> v1; x2 |-> v2; m) x =
(x2 |-> v2; x1 |-> v1; m) x.

Proof.
intros A m x1 x2 v1 v2 Hneq x e e0.
apply (@swap_disjoint_keys_in_partial_map_1 A m x1 x2 v1 v2 Hneq x e e0).
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
  x2 <> x1 ->
  (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).

Proof.
(* To prove the permutation property for two updates, we show that
     the result of applying either update order to any string is equivalent *)
  intros A m x1 x2 v1 v2 Hneq.
(* It is enough to use functional extensionality by showing that
     for all strings x, both sides of equation have the same value *)
  apply functional_extensionality.
intros x.
(* We perform case analysis on whether x is equal to x1 or x2 *)
  unfold t_update.
destruct (string_dec x1 x); destruct (string_dec x2 x).
- (* case: x1 = x and x2 = x *)
    apply (@swap_disjoint_keys_in_partial_map_0 A m x1 x2 v1 v2 Hneq x e e0).
- (* case: x1 = x and x2 <> x *)
    reflexivity.
- (* case: x1 <> x and x2 = x *)
    reflexivity.
- (* case: x1 <> x and x2 <> x *)
    reflexivity.
Qed.
From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Import Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Set Default Goal Selector "!".


Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _ !-> false
  ).

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

Definition includedin {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.
Lemma extend_partial_map_includedin_same_key_0 : forall A : Type, forall m m' : partial_map A, forall x : string, forall vx : A, forall Hinc : includedin m m', forall x' : string, forall v' : A, forall Heq : (x =? x')%string = true, (x |-> vx; m) x' = Some v' ->
(x |-> vx; m') x' = Some v'.

Proof.

  (* Introduce the hypotheses and the goal we are trying to prove *)
  intros A m m' x vx Hinc x' v' Heq Hmapx_x'.

  (* Unfold the definitions of update and t_update in the hypothesis Hmapx_x' *)
  unfold update, t_update in Hmapx_x'.
  
  (* Since (x =? x')%string = true, we rewrite the equality check in Hmapx_x' *)
  rewrite Heq in Hmapx_x'.

  (* Now we have (if true then Some vx else _) = Some v' in Hmapx_x', which simplifies *)
  simpl in Hmapx_x'.

  (* Given that Some vx = Some v' we now know that vx = v' *)
  assert (Hvx: vx = v').
  { injection Hmapx_x'. intros. assumption. }

  (* Then we rewrite the current goal with this assertion *)
  rewrite <- Hvx.

  (* Now we need to show that '(x |-> vx; m') x = Some vx' *)
  unfold update, t_update.

  (* Once again, we perform the equality check for strings, which should be true *)
  rewrite Heq.

  (* The goal follows by reflexivity *)
  reflexivity.

Qed.
Lemma extend_partial_map_with_different_key_1 : forall A : Type, forall m m' : partial_map A, forall x : string, forall vx : A, forall Hinc : includedin m m', forall x' : string, forall v' : A, forall Heq : (x =? x')%string = false, (x |-> vx; m) x' = Some v' ->
(x |-> vx; m') x' = Some v'.

Proof.

  (* Introduce the hypotheses and the goal we are trying to prove *)
  intros A m m' x vx Hinc x' v' Heq Hmapx_x'.

  (* Unfold the definitions of update and t_update in the hypothesis Hmapx_x' *)
  unfold update, t_update in Hmapx_x'.

  (* Since (x =? x')%string = false, we rewrite the equality check in Hmapx_x' *)
  rewrite Heq in Hmapx_x'.

  (* No simplification occurs due to the false condition, leaving the else branch (m x') = Some v' *)
  (* Now we need to show that '(x |-> vx; m') x' = Some v' *)
  unfold update, t_update.

  (* Again, we perform the equality check for x and x', which should be false *)
  rewrite Heq.

  (* Since Heq states that x and x' are different, we proceed with the goal using the else branch, which depends on m' *)
  (* We apply the includedin hypothesis Hinc to show that m x' = Some v' implies m' x' = Some v' *)
  apply Hinc in Hmapx_x'.

  (* The result follows directly from the hypothesis *)
  assumption.

Qed.

Theorem includedin_update : forall (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').


Proof.



  (* We will prove that if m is included in m', then updating both m and m'
     with the same key and value will maintain this inclusion relationship. *)

  (* Introduce the necessary variables and hypothesis about m being included in m' *)
  intros A m m' x vx Hinc.

  (* Now we need to unfold the definition of includedin for the updated maps *)
  unfold includedin.

  (* Introduce the necessary variables for our universally quantified goal *)
  intros x' v'.

  (* We will case analyze on whether the key x' is the same as the key x we used to update the maps *)
  destruct (String.eqb x x') eqn:Heq.

  - (* If x' is equal to x, the updated entries for both maps should be some v' *)
    simpl. apply (@extend_partial_map_includedin_same_key_0 A m m' x vx Hinc x' v' Heq).
- (* If x' is not equal to x, we can make use of the inclusion hypothesis. *)
    simpl. apply (@extend_partial_map_with_different_key_1 A m m' x vx Hinc x' v' Heq).

Qed.
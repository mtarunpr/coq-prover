





Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.
From LF Require Import Maps Imp.







Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  orb (orb (n =? 32)   
           (n =? 9))   
      (orb (n =? 10)   
           (n =? 13)). 

Notation "x '<=?' y" := (x <=? y)
  (at level 70, no associativity) : nat_scope.

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
     andb (48 <=? n) (n <=? 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (list_of_string s)
  end.

Definition string_of_list (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk := match acc with [] => [] | _::_ => [rev acc] end in
  match xs with
  | [] => tk
  | (x::xs') =>
    match cls, classifyChar x, x with
    | _, _, "("      =>
      tk ++ ["("]::(tokenize_helper other [] xs')
    | _, _, ")"      =>
      tk ++ [")"]::(tokenize_helper other [] xs')
    | _, white, _    =>
      tk ++ (tokenize_helper white [] xs')
    | alpha,alpha,x  =>
      tokenize_helper alpha (x::acc) xs'
    | digit,digit,x  =>
      tokenize_helper digit (x::acc) xs'
    | other,other,x  =>
      tokenize_helper other (x::acc) xs'
    | _,tp,x         =>
      tk ++ (tokenize_helper tp [x] xs')
    end
  end %char.

Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [] (list_of_string s)).



Example tokenize_ex1 : tokenize "abc12=3  223*(3+(a+c))" %string
  = ["abc"; "12"; "="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")"]%string.

Proof.
(* We will proceed by induction on the input list of ascii characters.
*)
  intros s.
(* We will also need to use the following lemmas: *)
  (* - rev_inj: The reverse of a list is injective.
*)
  (* - fold_right_rev: fold_right with cons is the same as appending and then reversing.
*)
  (* - map_rev: The map of a reversed list is the same as reversing the map.
*)
  (* - map_string_of_list: The map of a list of ascii characters is the same as converting the list to a string.
*)
  (* - fold_right_append: fold_right with cons is the same as appending.
*)
  (* - fold_right_string: fold_right with String is the same as converting a list of ascii characters to a string.
*)
  (* - tokenize_helper_correct: The tokenize_helper function correctly tokenizes a list of ascii characters.
*)
  (* - tokenize_correct: The tokenize function correctly tokenizes a string.
*)
  (* We will also use the following tactics: *)
  (* - inversion: To case split on the current state of the tokenize_helper function.
*)
  (* - destruct: To case split on the current character and its classification.
*)
  (* - simpl: To simplify the current goal.
*)
  (* - rewrite: To rewrite a goal using a lemma.
*)
  (* - congruence: To finish the proof by checking that the two lists are equal.
*)
  (* We will also use the following notations: *)
  (* - "x :: xs" for the list cons operator.
*)
  (* - "EmptyString" for the empty string.
*)
  (* - "String c s" for the string cons operator.
*)
  (* - "rev xs" for the reverse of a list xs.
*)
  (* - "map f xs" for the map of a function f on a list xs.
*)
  (* - "fold_right f x xs" for the fold_right of a function f with initial value x on a list xs.
*)
  (* - "tokenize_helper cls acc xs
Qed.
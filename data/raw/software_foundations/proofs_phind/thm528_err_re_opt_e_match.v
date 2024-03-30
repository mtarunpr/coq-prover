



Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith List.
From LF Require Import IndProp.



Fixpoint re_opt_e {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App EmptyStr re2 => re_opt_e re2
  | App re1 re2 => App (re_opt_e re1) (re_opt_e re2)
  | Union re1 re2 => Union (re_opt_e re1) (re_opt_e re2)
  | Star re => Star (re_opt_e re)
  | _ => re
  end.





Lemma re_opt_e_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.

Proof.
(* We will proceed by induction on the structure of the regular expression re.
*)
  intros T re s H.
induction re as [|re1 re2 Hre1 Hre2].
(* Case re = Empty: *)
  - (* In this case, we have s =~ Empty, which is false by definition of =~.
*)
    intros H.
exfalso.
now apply H.
(* Case re = Epsilon: *)
  - (* In this case, we have s =~ Epsilon, which is true by definition of =~.
*)
    intros H.
reflexivity.
(* Case re = Symbol a: *)
  - (* In this case, we have s =~ Symbol a, which is true if and only if s = a.
*)
    intros H.
now apply H.
(* Case re = Star re1: *)
  - (* We know that s =~ Star re1.
We need to prove that s =~ re_opt_e (Star re1).
*)
    (* By definition of =~, this is equivalent to proving that for all s', s' =~ re1 -> s' =~ re_opt_e re1.
*)
    intros H.
induction H as [s' Hs'].
(* In this case, we have s' =~ re1.
We need to prove that s' =~ re_opt_e re1.
*)
    (* By definition of =~, this is equivalent to proving that for all s'', s'' =~ re1 -> s'' =~ re_opt_e re1.
*)
    intros Hs'.
induction Hs' as [s'' Hs''].
(* In this case, we have s'' =~ re1.
We need to prove that s'' =~ re_opt_e re1.
*)
    (* By definition of =~, this is equivalent to proving that for all s''', s''' =~ re1 -> s''' =~ re_opt_e re1.
*)
    intros Hs''.
induction Hs'' as [s''' Hs'''].
(* In this case
Qed.
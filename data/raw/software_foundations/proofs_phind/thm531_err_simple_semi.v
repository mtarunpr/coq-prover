



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
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  -  simpl. apply MEmpty.
  -  simpl. apply MChar.
  -  simpl.
    destruct re1.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + inversion Hmatch1. simpl. apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
    + apply MApp.
      * apply IH1.
      * apply IH2.
  -  simpl. apply MUnionL. apply IH.
  -  simpl. apply MUnionR. apply IH.
  -  simpl. apply MStar0.
  -  simpl. apply MStarApp.
    * apply IH1.
    * apply IH2.
Qed.













Theorem silly1 : forall n, 1 + n = S n.
Proof. try reflexivity.  Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  Fail reflexivity.
  try reflexivity. 
  apply HP.
Qed.












Lemma simple_semi : forall n, (n + 1 =? 0) = false.

Proof.
(*
    We will proceed by induction on n.
Base case: n = 0
    (n + 1 =? 0) = false
    Since n = 0, (0 + 1 =? 0) = false
    This is true because 1 <> 0.
*)
  intros n.
induction n as [|n' IHn'].
- simpl.
reflexivity.
(*
    Inductive case: n = S n'
    (S n' + 1 =? 0) = false
    By the induction hypothesis, we know that (n' + 1 =? 0) = false.
We will prove that (S n' + 1 =? 0) = false.
We have two cases to consider:
    1.
n' + 1 = 0
    2.
n' + 1 <> 0
    Case 1 is impossible because n' + 1 = 0 would mean n' = -1, which is not possible.
Therefore, we only need to consider case 2.
Since n' + 1 <> 0, S n' + 1 <> S 0 = 1.
Hence, (S n' + 1 =? 0) = false.
*)
  - simpl.
destruct (n' + 1 =? 0) eqn:E.
+ contradiction.
+ reflexivity.
Qed.
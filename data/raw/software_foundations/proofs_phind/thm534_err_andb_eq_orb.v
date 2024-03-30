



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
  intros n.
  destruct n eqn:E.
    
    -  simpl. reflexivity.
    -  simpl. reflexivity.
Qed.



Lemma simple_semi' : forall n, (n + 1 =? 0) = false.
Proof.
  intros n.
  
  destruct n;
  
  simpl;
  
  reflexivity.
Qed.



Lemma simple_semi'' : forall n, (n + 1 =? 0) = false.
Proof.
  destruct n; reflexivity.
Qed.







Theorem andb_eq_orb : forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.

Proof.
(*
     We will prove the theorem by induction on the boolean values of b and c.
The base case will be when b and c are both false, and the inductive case
     will be when b and c are either both true or one is true and the other is false.
*)
  intros b c H.
destruct b as [|b].
- (* b = false *)
    destruct c as [|c].
+ (* b = false, c = false *)
      (* In this case, andb false false = false and orb false false = false.
Since andb false false = orb false false, we have b = c = false.
*)
      reflexivity.
+ (* b = false, c = true *)
      (* In this case, andb false true = false and orb false true = true.
Since andb false true ≠ orb false true, we have a contradiction.
*)
      contradiction.
+ (* b = true *)
    destruct c as [|c].
+ (* b = true, c = false *)
      (* In this case, andb true false = false and orb true false = true.
Since andb true false ≠ orb true false, we have a contradiction.
*)
      contradiction.
+ (* b = true, c = true *)
      (* In this case, andb true true = true and orb true true = true.
Since andb true true = orb true true, we have b = c = true.
*)
      reflexivity.
Qed.
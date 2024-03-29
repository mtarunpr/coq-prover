



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





Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof. destruct b; destruct c; try reflexivity; try discriminate. Qed.

Theorem add_assoc : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. intros n m p; induction n as [| n' IHn']; try (simpl; rewrite IHn'); reflexivity. Qed.

Fixpoint nonzeros (lst : list nat) :=
  match lst with
  | [] => []
  | 0 :: t => nonzeros t
  | h :: t => h :: nonzeros t
  end.

Lemma nonzeros_app : forall lst1 lst2 : list nat,
  nonzeros (lst1 ++ lst2) = (nonzeros lst1) ++ (nonzeros lst2).
Proof. intros lst1 lst2; induction lst1 as [|h t IH]; try (destruct h; simpl; rewrite <- IH); reflexivity. Qed.





Lemma re_opt_e_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2];
    
    simpl.
  -  apply MEmpty.
  -  apply MChar.
  - 
    destruct re1;
    
    try (apply MApp; try apply IH1; apply IH2).
    
    inversion Hmatch1. simpl. apply IH2.
  -  apply MUnionL. apply IH.
  -  apply MUnionR. apply IH.
  -  apply MStar0.
  -   apply MStarApp. apply IH1.  apply IH2.
Qed.






Theorem app_length : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros; induction lst1;
    [reflexivity | simpl; rewrite IHlst1; reflexivity].
Qed.



Theorem app_length' : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).
Proof.
  intros; induction lst1;
    [idtac | simpl; rewrite IHlst1];
    reflexivity.
Qed.





Theorem add_assoc' : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. intros n m p; induction n as [| n' IHn']; [| simpl; rewrite IHn']; reflexivity. Qed.





Lemma re_opt_e_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt_e re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2];
    
    simpl.
  -  apply MEmpty.
  -  apply MChar.
  - 
    destruct re1;
    try (apply MApp; [apply IH1 | apply IH2]).  
    inversion Hmatch1. simpl. apply IH2.
  -  apply MUnionL. apply IH.
  -  apply MUnionR. apply IH.
  -  apply MStar0.
  -   apply MStarApp; [apply IH1 | apply IH2].  
Qed.






Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.



Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.







Theorem ev100 : ev 100.

Proof.
(* 100 is even if 98 is even *)
  apply ev_SS.
(* 98 is even if 96 is even *)
  apply ev_SS.
(* 96 is even if 94 is even *)
  apply ev_SS.
(* 94 is even if 92 is even *)
  apply ev_SS.
(* 92 is even if 90 is even *)
  apply ev_SS.
(* 90 is even if 88 is even *)
  apply ev_SS.
(* 88 is even if 86 is even *)
  apply ev_SS.
(* 86 is even if 84 is even *)
  apply ev_SS.
(* 84 is even if 82 is even *)
  apply ev_SS.
(* 82 is even if 80 is even *)
  apply ev_SS.
(* 80 is even if 78 is even *)
  apply ev_SS.
(* 78 is even if 76 is even *)
  apply ev_SS.
(* 76 is even if 74 is even *)
  apply ev_SS.
(* 74 is even if 72 is even *)
  apply ev_SS.
(* 72 is even if 70 is even *)
  apply ev_SS.
(* 70 is even if 68 is even *)
  apply ev_SS.
(* 68 is even if 66 is even *)
  apply ev_SS.
(* 66 is even if 64 is even *)
  apply ev_SS.
(* 64 is even if 62 is even *)
  apply ev_SS.
(* 62 is even if 60 is even *)
  apply ev_SS.
(* 60 is even if 58 is even *)
  apply ev_SS.
(* 58 is even if 56 is even *)
  apply ev_SS.
(* 56 is even if 54 is even *)
  apply ev_SS.
(* 54 is even if 52 is even *)
  apply ev_SS.
(* 52 is even if 50 is even *)
  apply ev_SS.
(* 50 is even if 48 is even *)
  apply ev_SS.
(* 48 is even if 46 is even *)
  apply ev_SS.
(* 46 is even if 44 is even *)
  apply ev_SS.
(* 44 is even if 42 is even *)
  apply ev_SS.
(* 42 is even if 40 is even *)
  apply ev_SS.
(* 40 is even if 38 is even *)
  apply ev_SS.
(* 38 is even if 36 is even *)
  apply ev_SS.
(* 36 is even if 34 is even *)
  apply ev_SS.
(* 34 is even if 32 is even *)
  apply ev_SS.
(* 32 is even if 30 is even *)
  apply ev_SS.
(* 30 is even if 28 is even *)
  apply ev_SS.
(* 28 is even if 26 is even *)
  apply ev_SS.
(* 26 is even if 24 is even *)
  apply ev_SS.
(* 24 is even if 22 is even *)
  apply ev_SS.
(* 22 is even if 20 is even *)
  apply ev_SS.
(* 20 is even if 18 is even *)
  apply ev_SS.
(* 18 is even if 16 is even *)
  apply ev_SS.
(* 16 is even if 14 is even *)
  apply ev_SS.
(* 14 is even if 12 is even *)
  apply ev_SS.
(* 12 is even if 10 is even *)
  apply ev_SS.
(* 10 is even if 8 is even *)
  apply ev_SS.
(* 8 is even if 6 is even *)
  apply ev_SS.
(* 6 is even if 4 is even *)
  apply ev_SS.
(* 4 is even if 2 is even *)
  apply ev_SS.
(* 2 is even because 0 is even (base case) *)
  apply ev_SS.
apply ev_0.
Qed.
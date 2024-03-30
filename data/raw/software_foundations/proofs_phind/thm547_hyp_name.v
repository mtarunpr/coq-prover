



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





Theorem ev100: ev 100.
Proof. repeat (apply ev_SS). apply ev_0. Qed.









Fixpoint re_opt {T:Type} (re: reg_exp T) : reg_exp T :=
  match re with
  | App _ EmptySet => EmptySet
  | App EmptyStr re2 => re_opt re2
  | App re1 EmptyStr => re_opt re1
  | App re1 re2 => App (re_opt re1) (re_opt re2)
  | Union EmptySet re2 => re_opt re2
  | Union re1 EmptySet => re_opt re1
  | Union re1 re2 => Union (re_opt re1) (re_opt re2)
  | Star EmptySet => EmptyStr
  | Star EmptyStr => EmptyStr
  | Star re => Star (re_opt re)
  | EmptySet => EmptySet
  | EmptyStr => EmptyStr
  | Char x => Char x
  end.



Lemma re_opt_match : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
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
    + inversion IH1.
    + inversion IH1. simpl. destruct re2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
      * apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r.  apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. apply IH1.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
      * apply MApp.
        -- apply IH1.
        -- apply IH2.
  -  simpl.
    destruct re1.
    + inversion IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
    + destruct re2.
      * apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
      * apply MUnionL. apply IH.
  -  simpl.
    destruct re1.
    + apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
    + destruct re2.
      * inversion IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
      * apply MUnionR. apply IH.
 -  simpl.
    destruct re.
    + apply MEmpty.
    + apply MEmpty.
    + apply MStar0.
    + apply MStar0.
    + apply MStar0.
    + simpl.
      destruct re.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
      * apply MStar0.
 -  simpl.
   destruct re.
   + inversion IH1.
   + inversion IH1. inversion IH2. apply MEmpty.
   + apply star_app.
     * apply MStar1. apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
   + apply star_app.
     * apply MStar1.  apply IH1.
     * apply IH2.
Qed.



Lemma re_opt_match' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  -  simpl; apply MEmpty.
  -  simpl; apply MChar.
  - 
    simpl;
      destruct re1;
      [inversion IH1 | inversion IH1; simpl; destruct re2; apply IH2 | | | |];
      (destruct re2;
       [inversion IH2 | inversion IH2; rewrite app_nil_r; apply IH1 | | | | ];
       (apply MApp; [apply IH1 | apply IH2])).
  - 
    simpl;
      destruct re1;
      [inversion IH | | | | |];
      destruct re2; try apply MUnionL; apply IH.
  - 
    simpl;
      destruct re1;
      [apply IH | | | | |];
      (destruct re2; [inversion IH | | | | |]; apply MUnionR; apply IH).
 - 
   simpl;
     destruct re; try apply MEmpty; try apply MStar0.
 - 
   simpl;
    destruct re;
    [inversion IH1 | inversion IH1; inversion IH2; apply MEmpty | | | |];
    (apply star_app; [apply MStar1; apply IH1 | apply IH2]).
Qed.

Definition manual_grade_for_re_opt : option (nat*string) := None.









Theorem hyp_name : forall (P : Prop), P -> P.

Proof.
(* The theorem is an instance of the "silly2" theorem, which is a tautology.
The proof is trivial because the statement "P -> P" is true for any proposition P.
*)
intros P H.
apply H.
Qed.
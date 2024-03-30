



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
  intros P HP. apply HP.
Qed.








Theorem no_hyp_name : forall (P : Prop), P -> P.
Proof.
  intros. assumption.
Qed.








Theorem false_assumed : False -> 0 = 1.
Proof.
  intros H. destruct H.
Qed.

Theorem false_assumed' : False -> 0 = 1.
Proof.
  intros. contradiction.
Qed.

Theorem contras : forall (P : Prop), P -> ~P -> 0 = 1.
Proof.
  intros P HP HNP. exfalso. apply HNP. apply HP.
Qed.

Theorem contras' : forall (P : Prop), P -> ~P -> 0 = 1.
Proof.
  intros. contradiction.
Qed.






Theorem many_eq : forall (n m o p : nat),
  n = m ->
  o = p ->
  [n; o] = [m; p].
Proof.
  intros n m o p Hnm Hop. rewrite Hnm. rewrite Hop. reflexivity.
Qed.

Theorem many_eq' : forall (n m o p : nat),
  n = m ->
  o = p ->
  [n; o] = [m; p].
Proof.
  intros. subst. reflexivity.
Qed.








Check ev_0 : ev 0.
Check ev_SS : forall n : nat, ev n -> ev (S (S n)).

Example constructor_example: forall (n:nat),
    ev (n + n).
Proof.
  induction n; simpl.
  - constructor. 
  - rewrite add_comm. simpl. constructor. 
    assumption.
Qed.













From Coq Require Import Lia.

Theorem lia_succeed1 : forall (n : nat),
  n > 0 -> n * 2 > n.
Proof. lia. Qed.

Theorem lia_succeed2 : forall (n m : nat),
    n * m = m * n.
Proof.
  lia. 
Qed.

Theorem lia_fail1 : 0 = 1.
Proof.
  Fail lia. 
Abort.

Theorem lia_fail2 : forall (n : nat),
    n >= 1 -> 2 ^ n = 2 * 2 ^ (n - 1).
Proof.
  Fail lia. 
Abort.



Require Import Ring.

Theorem mult_comm : forall (n m : nat),
    n * m = m * n.
Proof.
  intros n m. ring.
Qed.






Theorem eq_example1 :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  intros. rewrite H. reflexivity.
Qed.







Theorem eq_example1' :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (x : A) (y : B),
    y = f x -> g y = g (f x).
Proof.
  congruence.
Qed.



Theorem eq_example2 : forall (n m o p : nat),
    n = m ->
    o = p ->
    (n, o) = (m, p).
Proof.
  congruence.
Qed.

Theorem eq_example3 : forall (X : Type) (h : X) (t : list X),
    [] <> h :: t.
Proof.
  congruence.
Qed.






Theorem intuition_succeed1 : forall (P : Prop),
    P -> P.
Proof. intuition. Qed.

Theorem intuition_succeed2 : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof. intuition. Qed.

Theorem intuition_simplify1 : forall (P : Prop),
    ~~P -> P.
Proof.
  intuition. 
Abort.

Theorem intuition_simplify2 : forall (x y : nat) (P Q : nat -> Prop),
  x = y /\ (P x -> Q x) /\ P x -> Q y.
Proof.
  Fail congruence. 
  intuition. 
  congruence.
Qed.



Theorem intuition_simplify2' : forall (x y : nat) (P Q : nat -> Prop),
  x = y /\ (P x -> Q x) /\ P x -> Q y.
Proof.
  intuition congruence.
Qed.






Theorem plus_id_exercise_from_basics : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. lia. Qed.

Theorem add_assoc_from_induction : forall n m p : nat,
    n + (m + p) = (n + m) + p.
Proof. lia. Qed.

Theorem S_injective_from_tactics : forall (n m : nat),
  S n = S m ->
  n = m.
Proof. congruence. Qed.

Theorem or_distributes_over_and_from_logic : forall P Q R : Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof. intuition. Qed.













Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2. apply H1. apply H3.
Qed.



Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.







Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof. auto. Qed.



Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  
  auto.
  
  auto 6.
Qed.



Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof. auto. Qed.



Example auto_example_5 : 2 = 2.
Proof.
  
  auto.
Qed.



Lemma le_antisym : forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof. intros. lia. Qed.

Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto using le_antisym.
Qed.



Create HintDb le_db.
Hint Resolve le_antisym : le_db.

Example auto_example_6' : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto with le_db.
Qed.



Definition is_fortytwo x := (x = 42).

Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  auto.  
Abort.

Hint Unfold is_fortytwo : le_db.

Example auto_example_7' : forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof. auto with le_db. Qed.



Example auto_example_8 : forall (n m : nat),
    n + m = m + n.
Proof.
  auto. 
  auto with arith. 
Qed.





Create HintDb re_db.
Hint Constructors exp_match : re_db.

Lemma re_opt_match'' : forall T (re: reg_exp T) s,
  s =~ re -> s =~ re_opt re.
Proof.
  intros T re s M.
  induction M
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  -  auto with re_db.
  -  auto with re_db.
  -  simpl.
    destruct re1.
    + inversion IH1.
    + inversion IH1. simpl. destruct re2; auto.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. auto.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. auto.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. auto.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
    + destruct re2.
      * inversion IH2.
      * inversion IH2. rewrite app_nil_r. auto.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
  -  simpl.
    destruct re1.
    + inversion IH.
    + destruct re2; auto with re_db.
    + destruct re2; auto with re_db.
    + destruct re2; auto with re_db.
    + destruct re2; auto with re_db.
    + destruct re2; auto with re_db.
  -  simpl.
    destruct re1.
    + apply IH.
    + destruct re2.
      * inversion IH.
      * constructor. auto.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
    + destruct re2.
      * inversion IH.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
    + destruct re2.
      * inversion IH.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
    + destruct re2.
      * inversion IH.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
    + destruct re2.
      * inversion IH.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
      * auto with re_db.
 -  simpl.
    destruct re; auto with re_db.
 -  simpl.
   destruct re.
   + inversion IH1.
   + inversion IH1. inversion IH2. auto with re_db.
   + auto with re_db.
   + auto with re_db.
   + auto with re_db.
   + auto with re_db.
Qed.

Definition manual_grade_for_re_opt_match'' : option (nat*string) := None.




Import Pumping.

Lemma weak_pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - 
    simpl. lia.
  - 
    simpl. lia.
  - 
    intros H. simpl in H.
    rewrite app_length in H.
    apply add_le_cases in H. destruct H.
    + apply IH1 in H.
      destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
      exists s1'. exists s2'. exists (s3' ++ s2).
      split. rewrite Happ.
      rewrite <- app_assoc with T s1' (s2' ++ s3') s2.
      rewrite <- app_assoc with T s2' s3' s2.
      reflexivity.
      split. auto.
      intros m.
      rewrite app_assoc with T s1' (napp m s2') (s3' ++ s2).
      rewrite app_assoc with T (s1' ++ napp m s2') s3' s2.
      rewrite <- app_assoc with T s1' (napp m s2') s3'.
      auto with re_db.
    + apply IH2 in H.
      destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
      exists (s1 ++ s1'). exists s2'. exists s3'.
      split. rewrite Happ.
      rewrite <- app_assoc with T s1 s1' (s2' ++ s3').
      reflexivity.
      split. apply Hne.
      intros m.
      rewrite <- app_assoc with T s1 s1' (napp m s2' ++ s3').
      auto with re_db.
  - 
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H H'].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
    exists s1'. exists s2'. exists s3'. auto with re_db.
  - 
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H' H].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne Hnapp]]]]].
    exists s1'. exists s2'. exists s3'. auto with re_db.
  - 
    intros H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    inversion H as [H0|]. rewrite H0 in Hp. inversion Hp.
  - 
    intros H.
    rewrite app_length in H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    assert (Hl: (1 <= length s1 \/ 1 <= length s2)).
    { destruct s1. right. apply le_trans with (pumping_constant re). apply Hp. apply H. left. simpl. apply n_le_m__Sn_le_Sm. apply O_le_n. }
    exists []. exists (s1 ++ s2). exists [].
    split. rewrite app_nil_r. reflexivity.
    split. destruct Hl as [Hl | Hl].
    + destruct s1. inversion Hl. discriminate.
    + destruct s2. inversion Hl. destruct s1. discriminate. discriminate.
    + induction m.
      * apply MStar0.
      * simpl in IHm. simpl. rewrite <- app_assoc.
        apply star_app.
        apply (MStarApp s1 s2 re Hmatch1 Hmatch2).
        apply IHm.
Qed.

Definition manual_grade_for_pumping_redux : option (nat*string) := None.




Lemma pumping : forall T (re : reg_exp T) s,
    s =~ re ->
    pumping_constant re <= length s ->
    exists s1 s2 s3,
      s = s1 ++ s2 ++ s3 /\
        s2 <> [] /\
        length s1 + length s2 <= pumping_constant re /\
        forall m, s1 ++ napp m s2 ++ s3 =~ re.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - 
    simpl. intros contra. lia.
  - 
    intros contra. apply Sn_le_Sm__n_le_m in contra. lia.
  - 
    intros H.
    rewrite app_length in H. simpl in H.
    destruct (lt_ge_cases (length s1) (pumping_constant re1)) as [H1 | H1].
    + destruct (lt_ge_cases (length s2) (pumping_constant re2)) as [H2 | H2].
      * apply add_le_cases in H. destruct H as [H1' | H2'].
        ** lia.
        ** lia.
      * apply IH2 in H2.
        destruct H2 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists (s1 ++ s1'). exists s2'. exists s3'.
        split. rewrite Happ.
        rewrite <- app_assoc with T s1 s1' (s2' ++ s3').
        reflexivity.
        split. apply Hne.
        split. simpl. rewrite app_length. rewrite <- add_assoc.
        apply le_trans with (n := length s1 + pumping_constant re2).
        apply plus_le_compat_l. apply Hlen.
        apply plus_le_compat_r. apply n_lt_m__n_le_m in H1. apply H1.
        intros m.
        rewrite <- app_assoc with T s1 s1' (napp m s2' ++ s3').
        auto with re_db.
    + apply IH1 in H1.
      destruct H1 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
      exists s1'. exists s2'. exists (s3' ++ s2).
      split. rewrite Happ.
      rewrite <- app_assoc with T s1' (s2' ++ s3') s2.
      rewrite <- app_assoc with T s2' s3' s2.
      reflexivity.
      split. apply Hne.
      split. simpl.
      apply le_trans with (n := pumping_constant re1).
      apply Hlen. apply le_plus_l.
      intros m.
      rewrite app_assoc with T s1' (napp m s2') (s3' ++ s2).
      rewrite app_assoc with T (s1' ++ napp m s2') s3' s2.
      rewrite <- app_assoc with T s1' (napp m s2') s3'.
      auto with re_db.
  - 
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H H'].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
    exists s1'. exists s2'. exists s3'.
    split. apply Happ.
    split. apply Hne.
    split. simpl. apply le_trans with (n := pumping_constant re1). apply Hlen. apply le_plus_l.
    auto with re_db.
  - 
    intros H. simpl in H.
    apply plus_le in H. destruct H as [H' H].
    apply IH in H.
    destruct H as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
    exists s1'. exists s2'. exists s3'.
    split. apply Happ.
    split. apply Hne.
    split. simpl. apply le_trans with (n := pumping_constant re2). apply Hlen. rewrite add_comm. apply le_plus_l.
    intros m. apply MUnionR. apply Hnapp.
  - 
    intros H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    inversion H as [H0|]. rewrite H0 in Hp. inversion Hp.
  - 
    intros H.
    rewrite app_length in H.
    assert (Hp : (pumping_constant re) >= 1).
    { apply pumping_constant_ge_1. }
    assert (Hl: (1 <= length s1 \/ 1 <= length s2)).
    { destruct s1. right. apply le_trans with (pumping_constant re). apply Hp. apply H. left. simpl. apply n_le_m__Sn_le_Sm. apply O_le_n. }
    destruct s1 as [| x s11].
    + destruct (lt_ge_cases (length s2) (pumping_constant (Star re))) as [H2 | H2].
      * exists []. exists s2. exists [].
        split. rewrite app_nil_r. reflexivity.
        split. destruct Hl as [Hl | Hl].
        ** inversion Hl.
        ** destruct s2. inversion Hl. discriminate.
        ** split. apply n_lt_m__n_le_m in H2. apply H2.
        induction m. apply MStar0. simpl. rewrite <- app_assoc. apply star_app. apply Hmatch2. apply IHm.
      * apply IH2 in H2.
        destruct H2 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists s1'. exists s2'. exists s3'. auto.
    + remember (x :: s11) as s1.
      destruct (lt_ge_cases (length s1) (pumping_constant re)) as [H1 | H1].
      * exists []. exists s1. exists s2.
        split. reflexivity.
        split. rewrite Heqs1. discriminate.
        split. apply n_lt_m__n_le_m in H1. apply H1.
        intros m. simpl. apply napp_star. apply Hmatch1. apply Hmatch2.
      * apply IH1 in H1.
        destruct H1 as [s1' [s2' [s3' [Happ [Hne [Hlen Hnapp]]]]]].
        exists s1'. exists s2'. exists (s3' ++ s2).
        split. rewrite Happ. simpl.
        rewrite <- app_assoc with (m := s2' ++ s3').
        rewrite <- app_assoc with (m := s3').
        reflexivity.
        split. apply Hne.
        split. apply Hlen.
        intros m. rewrite app_assoc. rewrite app_assoc. apply MStarApp.
        rewrite <- app_assoc. apply Hnapp. apply Hmatch2.
Qed.

Definition manual_grade_for_pumping_redux_strong : option (nat*string) := None.







Example trans_example1:  forall a b c d,
    a <= b + b * c  ->
    (1 + c) * b <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  apply le_trans with (b + b * c).
    
  - apply H1.
  - simpl in H2. rewrite mul_comm. apply H2.
Qed.



Example trans_example1':  forall a b c d,
    a <= b + b * c  ->
    (1 + c) * b <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  eapply le_trans. 
  - apply H1. 
  - simpl in H2. rewrite mul_comm. apply H2.
Qed.





Example trans_example2:  forall a b c d,
    a <= b + b * c  ->
    b + b * c <= d ->
    a <= d.
Proof.
  intros a b c d H1 H2.
  info_eauto using le_trans.
Qed.













Ltac simpl_and_try tac := simpl; try tac.



Example sat_ex1 : 1 + 1 = 2.
Proof. simpl_and_try reflexivity. Qed.

Example sat_ex2 : forall (n : nat), 1 - 1 + n + 1 = 1 + n.
Proof. simpl_and_try reflexivity. lia. Qed.





Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  - destruct c.
    + reflexivity.
    + reflexivity.
  - destruct c.
    + reflexivity.
    + reflexivity.
Qed.



Ltac destructpf x :=
  destruct x; try reflexivity.

Theorem plus_1_neq_0' : forall n : nat,
    (n + 1) =? 0 = false.
Proof. intros n; destructpf n. Qed.

Theorem negb_involutive' : forall b : bool,
  negb (negb b) = b.
Proof. intros b; destructpf b. Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c; destructpf b; destructpf c.
Qed.



Theorem andb3_exchange :
  forall b c d, andb (andb b c) d = andb (andb b d) c.
Proof. intros; destructpf b; destructpf c; destructpf d. Qed.




Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  - simpl. intros H. rewrite H. reflexivity.
  - simpl. intros H. destruct c eqn:Ec.
    + reflexivity.
    + rewrite H. reflexivity.
Qed.



Ltac destructpf' x := destruct x ; auto.



Theorem andb_true_elim2' : forall b c : bool,
    andb b c = true -> c = true.
Proof. intros b c; destructpf' b; destructpf' c. Qed.





Lemma bool_and_true_intro_1 : forall d : bool, true && d = d && true.

Proof.
(* The lemma bool_and_true_intro_1 is to be proven for all boolean values d.
We will proceed by induction on d.
*)
  intros d.
(* First, we consider the case where d is true.
*)
  destruct d as [d_true | d_false].
- (* If d is true, then true && d is true.
*)
    reflexivity.
- (* If d is false, then true && d is false.
*)
    reflexivity.
Qed.

Lemma bool_and_false_idempotent_2 : forall d : bool, false && d = d && false.

Proof.
(* Idea of the proof: We will prove this lemma by induction on the boolean value d.
Base case: When d is false, the statement false && d is obviously equal to d && false, which is false.
Inductive case: When d is true, the statement true && d is obviously equal to d && true, which is true.
*)
  intros d.
destruct d as [|d_true].
- (* d = false *)
    reflexivity.
- (* d = true *)
    reflexivity.
Qed.

Lemma bool_false_equality_3 : forall c d : bool, false = false.

Proof.
(* Base case: When both c and d are false *)
  intros c d.
reflexivity.
Qed.

Lemma bool_and_associativity_0 : forall b c d : bool, b && c && d = b && d && c.




Proof.
(* The goal is to prove that b && c && d = b && d && c for all booleans b, c, and d.
We will proceed by induction on b.
*)
  
intros b c d.
(* First, we consider the case where b is true.
*)
  
destruct b as [b_true | b_false].
-
 (* b is true.
*)
    
simpl.
(* We now need to prove that c && d = d && c.
*)
    
destruct c as [c_true | c_false].
apply (@bool_and_true_intro_1 d).
apply (@bool_and_false_idempotent_2 d).
-
 (* d is false.
*)
        
simpl.
(* We now need to prove that false = true, which is impossible.
*)
        
apply (@bool_false_equality_3 c d).
Qed.

Theorem andb3_exchange' : forall b c d, andb (andb b c) d = andb (andb b d) c.




Proof.
(* andb3_exchange' is a statement about boolean values.
We will proceed by induction on b, c, and d.
*)
  
intros b c d.
(* We will consider two cases: when b is true and when b is false.
*)
  
apply (@bool_and_associativity_0 b c d).
Qed.
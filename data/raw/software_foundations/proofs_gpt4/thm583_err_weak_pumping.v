



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
(* The lemma requires the use of the pumping lemma for regular expressions.
We perform induction on the regular expression `re` to construct the proof.
*)

  intros T re.
(* Introduce the type `T` and regular expression `re` *)
  induction re.
(* Case EmptySet: The lemma is trivially false because no string matches EmptySet.
We can prove by contradiction, using the fact that s =~ EmptySet is always False.
*)
  - intros s Hmatch Hlength.
exfalso.
(* Apply lemma `null_matches_none` to get a contradiction with `Hmatch` *)
    apply (null_matches_none T s).
assumption.
(* Case EmptyStr: The lemma is trivially false because the only string that matches
     EmptyStr is the empty string [].
Since pumping_constant EmptyStr is 1,
     the only case we need to consider is the empty string which has length 0.
But the assumption pumping_constant re <= length s leads to a contradiction
     as 1 <= 0 is not possible.
*)
  - intros s Hmatch Hlength.
simpl in Hlength.
(* Since the only string that matches EmptyStr is [], we have s = [] *)
    destruct s.
2: discriminate.
(* s cannot be non-empty *)
    simpl in Hlength.
exfalso.
lia.
(* We derive a contradiction *)
  
  (* Case Char: The lemma holds as the only string s that matches Char t is [t],
     and the pumping_constant for Char t is 1.
We take s1 = [], s2 = [t], s3 = [].
*)
  - intros s Hmatch Hlength.
exists [], [t], [].
(* The string s has to be [t] *)
    inversion Hmatch.
split; [ reflexivity | ].
(* Solve the first part of the conjunction *)
    split.
(* Split the conjunction to solve each part separately *)
    + (* Prove s2 is non-empty *)
      intros H.
discriminate H.
+ (* Prove that for all m, s1 ++ napp m s2 ++ s3 matches the regex.
Since s1 and s3 are [], and s2 = [t], m copies of s2 is just a string with m t's, *)
      intros m.
simpl.
(* which matches the Char t regex exactly `m` times.
*)
      induction m; simpl; constructor; assumption.
(* Case App: This case requires us to apply the inductive hypothesis for both re1 and re2,
     using the lemma `app_exists`.
Additionally, we have to consider the match_eps for re1
     as per the definition of derive in the case for App.
*)
  - intros s Hmatch Hle.
apply (app_exists T s) in Hmatch.
destruct Hmatch as [s1 [s2 [Hsplit [Hmatch1 Hmatch2]]]].
rewrite app_length in Hle.
(* The length of s is the sum of the lengths of s1 and s2 *)
    apply eq_add_S in Hle.
apply leb_complete in Hle.
(* Apply the inductive hypothesis to re1 or re2 depending on whether match_eps re1 is true.
*)
    destruct (match_eps_refl T re1) with (ReflectT Heps1 | ReflectF Hneps1).
+ (* Case when match_eps re1 is true.
We can pump s2 with respect to re2.
*)
      destruct (IHre2 s2 Hmatch2 Hle) as [s21 [s22 [s23 [Hsplit2 [Hnonempty2 Hall]]]]].
exists s1, s21, (s22 ++ s23).
(* Concatenate s2 with s21 and split it *)
      split; [ (* Prove the three-part conjunction *)
        rewrite <- Hsplit2, <- Hsplit, app_assoc; reflexivity | ].
split.
* (* Prove s21 is non-empty *)
        apply Hnonempty2.
* (* Prove that for all m in N, s1 ++ napp m s21 ++ s23 matches re *)
        intros m.
rewrite app_assoc, <- app_assoc with (n := s1).
apply (MStar' T).
intros s0 H.
rewrite <- Hsplit.
apply Heps1 in Hmatch1.
rewrite <- Hmatch1.
apply Heps1.
apply Hall.
+ (* Case when match_eps re1 is false.
We can apply the IH on s1 with respect to re1 *)
      destruct (IHre1 s1 Hmatch1 Hle) as [s11 [s12 [s13 [Hsplit1 [Hnonempty1 Hall]]]]].
exists s11, s12, (s13 ++ s2).
(* Concatenate s13 with s2 and split it *)
      split; [ (* Prove the three-part conjunction *)
        rewrite <- app_assoc, <- Hsplit, <- Hsplit1; reflexivity | ].
split.
* (* Prove s12 is non-empty *)
        apply Hnonempty1.
* (* Prove that for all m in N, s11 ++ napp m s12 ++ (s13 ++ s2) matches re *)
        intros m.
rewrite <- app_assoc.
apply MApp.
-- apply Hall.
(* s11 ++ napp m s12 ++ s13 matches re1 *)
        -- assumption.
(* s2 matches re2 *)
  
  (* Case Union: Apply pumping lemma to the matching part of the union.
*)
  - intros s Hmatch Hle.
inversion Hmatch; subst.
+ (* Apply the inductive hypothesis on s with respect to re1 *)
      apply IHre1 in H1.
2: assumption.
destruct H1 as [s11 [s12 [s13 [Hsplit [Hnonempty1 Hall]]]]].
exists s11, s12, s13.
(* use the s1 s2 s3 from re1 *)
      split; [assumption |].
(* Prove the three-part conjunction *)
      split; [assumption |].
(* Prove that s2 is non-empty *)
      intros m.
(* Prove that for all m in N, s1 ++ napp m s2 ++ s3 matches re *)
      apply MUnionL.
apply Hall.
+ (* Apply the inductive hypothesis on s with respect to re2 *)
      apply IHre2 in H1.
2: assumption.
destruct H1 as [s21 [s22 [s23 [Hsplit [Hnonempty2 Hall]]]]].
exists s21, s22, s23.
(* use the s1 s2 s3 from re2 *)
      split; [assumption |].
(* Prove the three-part conjunction *)
      split; [assumption |].
(* Prove that s2 is non-empty *)
      intros m.
(* Prove that for all m in N, s1 ++ napp m s2 ++ s3 matches re *)
      apply MUnionR.
apply Hall.
(* Case Star: Use the lemma `MStar''` to handle the Star case.
*)
  - intros s Hmatch Hle.
remember (Star re) as re_star.
induction Hmatch; inversion Heqre_star; subst; clear Heqre_star.
+ (* Base case with s =~ Star re, but s is empty.
Since [ ] =~ Star re, we take s = [].
This is a contradiction because by definition
         pumping_constant (Star re) is 1, so we cannot have 1 <= |[]|.
Hence, this case leads to contradiction.
*)
      exfalso.
simpl in Hle.
lia.
+ (* Inductive case with concatenation inside Star.
*)
      destruct s1.
* (* s1 is empty, we can proceed with IHexp_match2 as "|s1| = 0 < pumping_constant re".
*)
        simpl in H.
apply IHexp_match2 in H.
-- assumption.
-- simpl.
assumption.
* (* s1 is non-empty.
We can take s1 itself to be s2, and use an empty s1 and s3.
*)
        exists [], (x::s1), s2.
split; [ reflexivity | ].
(* solve the first part of the conjunction *)
        split; [ (* Prove s2 is non-empty *)
          unfold not.
intros Hcontradiction.
discriminate Hcontradiction | ].
(* Prove that for all m in N, napp m s2 ++ s3 matches Star re.
Use induction on m.
*)
        intros m.
induction m.
-- (* Base case m = 0 *)
           simpl.
assumption.
-- (* Inductive step *)
           simpl.
apply MApp.
++ (* Prove that x::s1 matches re, which comes from the hypothesis H *)
              assumption.
++ (* s1 ++ IHm s2 matches Star re by inductive hypothesis *)
              apply IHm.
Qed.
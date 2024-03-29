



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





Lemma length_cons_append_distributive_2 : forall X : Type, forall x : X, forall lst1' : list X, forall IHlst1' : forall lst2 : list X,
length (lst1' ++ lst2) =
length lst1' + length lst2, forall lst2 : list X, S (length (lst1' ++ lst2)) =
S (length lst1' + length lst2).

Proof.
(* The Lemma states that the length of a list can be computed as the length of its first part plus the length of the second part.
The statement uses an inductive hypothesis IHlst1' that has already established the length property for lst1'.
It expects us to show that this property will hold for S (length...), where S represents the successor function (or "one plus" operation).
*)
  intros X x lst1' IHlst1' lst2.
(* Apply the inductive hypothesis which gives us the length of (lst1' ++ lst2) *)
  rewrite IHlst1'.
(* After using rewrite, we have to prove that S (length lst1' + length lst2) is equal to itself, which is reflexive and thus trivial.
*)
  reflexivity.
Qed.

Lemma length_cons_append_distributive_1 : forall X : Type, forall x : X, forall lst1' : list X, forall IHlst1' : forall lst2 : list X,
length (lst1' ++ lst2) =
length lst1' + length lst2, forall lst2 : list X, S (length (lst1' ++ lst2)) =
S (length lst1' + length lst2).

Proof.
(* The lemma directly follows from the hypothesis (IHlst1') stating the Law of Associativity for addition with respect to the length of appended lists.
We apply the hypothesis to lst2 for lst1' and derive the required conclusion.
*)
  intros X x lst1' IHlst1' lst2.
apply (@length_cons_append_distributive_2 X x lst1' IHlst1' lst2).
Qed.

Lemma length_cons_append_distr_0 : forall X : Type, forall x : X, forall lst1' : list X, forall IHlst1' : forall lst2 : list X,
length (lst1' ++ lst2) =
length lst1' + length lst2, forall lst2 : list X,
S (length (lst1' ++ lst2)) =
S (length lst1' + length lst2).

Proof.
intros X x lst1' IHlst1' lst2.
(* We use the provided induction hypothesis, IHlst1', which states that for any list lst2,
     the length of lst1' appended with lst2 is equal to the length of lst1' plus the length of lst2.
*)
  apply (@length_cons_append_distributive_1 X x lst1' IHlst1' lst2).
Qed.

Theorem app_length' : forall (X : Type) (lst1 lst2 : list X),
    length (lst1 ++ lst2) = (length lst1) + (length lst2).

Proof.
(* The proof proceeds by induction on the first list lst1, 
     as the structure of lst1 directly affects the length after append.
*)
  induction lst1 as [| x lst1' IHlst1'].
- (* Base case: lst1 is an empty list, which does not affect lst2's length *)
    reflexivity.
- (* Inductive case: lst1 is x :: lst1', with x prepended to lst1'.
We apply the inductive hypothesis to lst1'.
*)
    simpl.
(* simplifying the append operation and length function *)
    apply (@length_cons_append_distr_0 X x lst1' IHlst1').
Qed.
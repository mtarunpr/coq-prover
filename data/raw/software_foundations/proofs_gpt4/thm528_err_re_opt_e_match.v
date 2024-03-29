



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
intros T re s H.
induction H.
(* Case EmptySet: regex that matches no strings.
*)
  - simpl.
apply H.
(* Case EmptyStr: regex that matches empty string, s = [].
*)
  - simpl.
constructor.
(* Case Char: regex that matches single character a, s = [a].
*)
  - simpl.
constructor.
(* Case App: regex that matches concatenation of re1 and re2.
*)
  - simpl.
destruct (re_opt_e re1), (re_opt_e re2); try constructor; try assumption; try apply MApp.
+ apply MApp; try assumption; apply IHmatch1.
+ apply MApp; try assumption; apply IHmatch2.
+ apply IHmatch1.
+ apply IHmatch2.
(* Case Union: regex that matches anything matching re1 or re2.
*)
  - simpl.
apply MUnionL.
apply IHmatch.
- simpl.
apply MUnionR.
apply IHmatch.
(* Case Star: regex that matches zero or more concatenations of re.
*)
  - simpl.
apply MStar0.
- simpl.
apply MStarApp; assumption.
Qed.
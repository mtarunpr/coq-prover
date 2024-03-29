

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.



Check (3 = 3) : Prop.

Check (forall n m : nat, n + m = m + n) : Prop.



Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.





Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.



Definition plus_claim : Prop := 2 + 2 = 4.
Check plus_claim : Prop.



Theorem plus_claim_is_true :
  plus_claim.
Proof. reflexivity.  Qed.





Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.



Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. injection H as H1. apply H1.
Qed.



Check @eq : forall A : Type, A -> A -> Prop.











Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.



Proof.
  split.
  -  reflexivity.
  -  reflexivity.
Qed.



Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.



Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  -  reflexivity.
  -  reflexivity.
Qed.


Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - destruct m in H.
    + rewrite <- plus_n_O in H. apply H.
    + rewrite <- plus_n_Sm in H. discriminate H.
  - destruct n in H.
    + rewrite -> plus_n_O in H. apply H.
    + simpl in H. discriminate H.
Qed.




Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.



Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.



Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.



Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  
  intros n m H.
  apply and_exercise in H.
  destruct H as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.



Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q HPQ.
  destruct HPQ as [HP _].
  apply HP.  Qed.


Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [_ HQ].
  apply HQ.
Qed.




Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    -  apply HQ.
    -  apply HP.  Qed.



Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  + split. apply HP. apply HQ.
  + apply HR.
Qed.




Check and : Prop -> Prop -> Prop.








Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  
  intros n m [Hn | Hm].
  - 
    rewrite Hn. reflexivity.
  - 
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.



Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.



Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  
  intros [|n'].
  - left. reflexivity.
  - right. reflexivity.
Qed.


Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n.
  - left. reflexivity.
  - right. destruct m.
    + reflexivity.
    + discriminate H.
Qed.



Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.







Module NotPlayground.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not : Prop -> Prop.

End NotPlayground.



Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  
  intros P contra.
  destruct contra.  Qed.





Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P HNP Q contra.
  unfold not in HNP.
  apply HNP in contra. destruct contra.
Qed.






Theorem zero_not_one : 0 <> 1.
Proof.
  
  unfold not.
  
  intros contra.
  
  discriminate contra.
Qed.



Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  
  intros P H. unfold not. intros G. apply G. apply H.  Qed.






Definition manual_grade_for_double_neg_inf : option (nat*string) := None.



Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HQ HP.
  unfold not in HQ. apply HPQ in HP. apply HQ in HP. apply HP.
Qed.



Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros P H.
  apply contradiction_implies_anything with (Q:=False) in H.
  apply H.
Qed.







Definition manual_grade_for_informal_not_PNP : option (nat*string) := None.



Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  intros P Q HPQ.
  unfold not in HPQ.
  split.
  - intros HP. apply or_intro_l  with (B:=Q) in HP. apply HPQ. apply HP.
  - intros HQ. apply or_intro_l  with (B:=P) in HQ. apply or_commut in HQ. apply HPQ. apply HQ.
Qed.




Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros b H.
  destruct b eqn:HE.
  - 
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - 
    reflexivity.
Qed.



Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.          
  - 
    unfold not in H.
    exfalso.                
    apply H. reflexivity.
  -  reflexivity.
Qed.






Lemma True_is_true : True.
Proof. apply I. Qed.







Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn O). { simpl. apply I. }
  rewrite H1 in H2. simpl in H2. apply H2.
Qed.








Module IffPlayground.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End IffPlayground.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  
  intros P Q [HAB HBA].
  split.
  -  apply HBA.
  -  apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  
  intros b. split.
  -  apply not_true_is_false.
  - 
    intros H. rewrite H. intros H'. discriminate H'.
Qed.



Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
  intros P Q R Hiff H HP. apply H.  apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
  intros P Q R Hiff H HQ. apply H.  apply Hiff. apply HQ.
Qed.



Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split. intros H. apply H. intros H. apply H.  Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H1 H2. split.
  - intros H. apply proj1 in H1. apply H1 in H. apply proj1 in H2. apply H2 in H. apply H.
  - intros H. apply proj2 in H2. apply H2 in H. apply proj2 in H1. apply H1 in H. apply H.
Qed.



Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  -  intros [HP | [HQ HR]].
    +  split. left. apply HP. left. apply HP.
    +  split.  right. apply HQ. right. apply HR.
  -  intros [[HP1 | HQ] [HP2 | HR]].
    + left. apply HP1.
    + left. apply HP1.
    + left. apply HP2.
    + right. apply and_intro. apply HQ. apply HR.
Qed.







From Coq Require Import Setoids.Setoid.





Lemma mul_eq_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.



Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0. rewrite mul_eq_0. rewrite or_assoc.
  reflexivity.
Qed.








Definition Even x := exists n : nat, x = double n.

Lemma four_is_Even : Even 4.
Proof.
  unfold Even. exists 2. reflexivity.
Qed.



Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  
  intros n [m Hm]. 
  exists (2 + m).
  apply Hm.  Qed.



Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H [x E].
  unfold not in E. apply E. apply H.
Qed.




Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.



Theorem leb_plus_exists : forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
  induction n.
  - intros. exists m. reflexivity.
  - destruct m.
    + simpl. discriminate.
    + simpl.
      intros H. apply IHn in H. destruct H as [x0 H].
      rewrite H. exists x0. reflexivity.
Qed.

Theorem plus_exists_leb : forall n m, (exists x, m = n+x) -> n <=? m = true.
Proof.
  intros.
  destruct H.
  generalize dependent m.
  induction n.
  - reflexivity.
  - intros.
    destruct m.
    + discriminate H.
    + rewrite add_comm in H. rewrite <- plus_n_Sm in H. injection H as H.
      rewrite add_comm in H.
      apply IHn in H. apply H.
Qed.









Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.



Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.






Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l ->
         In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - 
    simpl. intros [].
  - 
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.






Lemma map_preserves_injection_on_element_0 : forall A : Type, forall B : Type, forall f : A -> B, forall a : A, forall l' : list A, forall y : B, forall x : A, forall H1 : f x = y, forall H2 : a = x, forall IHl' : In x l' -> In y (map f l'), f a = y.

Proof.
intros A B f a l' y x H1 H2 IHl'.
rewrite H2.
(* Replace `a` with `x` using the hypothesis H2 that a = x *)
  apply H1.
(* Apply hypothesis H1 stating f x = y, concluding the proof.
*)

Qed.

Lemma in_map_preserves_element_3 : forall (A B : Type) (f : A -> B),
A ->
forall (l' : list A) (y : B) (x : A),
f x = y ->
In x l' -> (In x l' -> In y (map f l')) -> In x l'.

Proof.
(* This Lemma is simply stating that if `x` is an element in the list `l'`,
    then `x` is in `l'`, under the condition that `f` applied to `x`
    is `y` and this resulting `y` is in the list `map f l'`.
However, the condition is irrelevant since In x l' is among the assumptions,
    thus the final part of the statement is trivially true.
The "proof" consists
    of just restating that `x` is in `l'`.
*)
  intros A B f x0 l' y x Hfx Hin_x_l' Hin_implies.
exact Hin_x_l'.
Qed.

Lemma in_map_preserves_element_2 : forall (A B : Type) (f : A -> B),
A ->
forall (l' : list A) (y : B) (x : A),
f x = y ->
In x l' -> (In x l' -> In y (map f l')) -> In x l'.

Proof.
(* The given statement is trivially true because the conclusion is the same as one of the premises.
We can prove it directly by assuming the premises and restating one of them as the conclusion.
We don't even need the assumptions about types A and B, or the function f, or the elements y and x.
*)
  apply (@in_map_preserves_element_3 ).
Qed.

Lemma in_map_preserves_existence_1 : forall A : Type, forall B : Type, forall f : A -> B, forall a : A, forall l' : list A, forall y : B, forall x : A, forall H1 : f x = y, forall H2 : In x l', forall IHl' : In x l' -> In y (map f l'), In x l'.

Proof.
(* We apply the exact tactic to use the `In x l'` hypothesis directly.
*)
  apply (@in_map_preserves_element_2 ).
Qed.

Theorem In_map_iff : forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.

Proof.
(* We proceed by splitting the bidirectional implication and proving both directions.
*)
  split.
- (* -> (if y is in the image of l under f, then there exists some x in l such that f x = y *)
    intros H.
induction l as [| a l' IHl'].
+ (* Case l is empty *)
      simpl in H.
contradiction.
+ (* Case l is non-empty *)
      simpl in H.
destruct H as [H | H].
* (* Case y is the image of the first element *)
        exists a.
split; [ assumption | left; reflexivity ].
* (* Case y is in the image of the rest of the list *)
        apply IHl' in H.
destruct H as [x [H1 H2]].
exists x.
split; [ assumption | right; assumption ].
- (* <- (if such an x exists, then y is in the image of l under f) *)
    intros [x [H1 H2]].
induction l as [| a l' IHl'].
+ (* Case l is empty *)
      contradiction.
+ (* Case l is non-empty *)
      simpl.
destruct H2 as [H2 | H2].
* (* Case x is the first element of l *)
        left.
apply (@map_preserves_injection_on_element_0 A B f a l' y x H1 H2 IHl').
* (* Case x is in the rest of the list *)
        right.
apply IHl'.
apply (@in_map_preserves_existence_1 A B f a l' y x H1 H2 IHl').
Qed.
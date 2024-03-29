

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export IndProp.









Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).







Check ev_SS
  : forall n,
    ev n ->
    ev (S (S n)).





Theorem ev_4 : ev 4.
Proof.
  apply ev_SS. apply ev_SS. apply ev_0. Qed.



Print ev_4.




Check (ev_SS 2 (ev_SS 0 ev_0))
  : ev 4.





Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.






Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.





Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).



Print ev_4.

Print ev_4'.

Print ev_4''.

Print ev_4'''.




Theorem ev_8 : ev 8.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.

Definition ev_8' : ev 8
  := ev_SS 6 (ev_SS 4 (ev_SS 2 (ev_SS 0 ev_0))).









Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.



Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).



Definition ev_plus4'' (n : nat) (H : ev n)
                    : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''
  : forall n : nat,
    ev n ->
    ev (4 + n).







Definition ev_plus2 : Prop :=
  forall n, forall (E : ev n), ev (n + 2).



Definition ev_plus2' : Prop :=
  forall n, forall (_ : ev n), ev (n + 2).



Definition ev_plus2'' : Prop :=
  forall n, ev n -> ev (n + 2).








Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.


Compute add1 2.









Module Props.






Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.



Print prod.




Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
  Show Proof.
Qed.



Lemma and_comm : forall P Q : Prop, P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HQ HP]. split.
    + apply HP.
    + apply HQ.
Qed.

End And.



Definition and_comm'_aux P Q (H : P /\ Q) : Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).



Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R
  := fun P Q R HPQ HQR => conj (proj1 P Q HPQ) (proj2 Q R HQR).







Module Or.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].

Notation "P \/ Q" := (or P Q) : type_scope.





Definition inj_l : forall (P Q : Prop), P -> P \/ Q :=
  fun P Q HP => or_introl HP.

Theorem inj_l' : forall (P Q : Prop), P -> P \/ Q.
Proof.
  intros P Q HP. left. apply HP.
Qed.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R HPQ HPR HQR =>
    match HPQ with
    | or_introl HP => HPR HP
    | or_intror HQ => HQR HQ
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R HPQ HPR HQR.
  destruct HPQ as [HP | HQ].
  - apply HPR. apply HP.
  - apply HQR. apply HQ.
Qed.

End Or.



Definition or_commut' : forall P Q, P \/ Q -> Q \/ P
  := fun P Q HPQ =>
       match HPQ with
       | or_introl HP => or_intror HP
       | or_intror HQ => or_introl HQ
       end.







Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> ex P.

Notation "'exists' x , p" :=
  (ex (fun x => p))
    (at level 200, right associativity) : type_scope.

End Ex.





Check ex (fun n => ev n) : Prop.



Definition some_nat_is_even : exists n, ev n :=
  ex_intro ev 4 (ev_SS 2 (ev_SS 0 ev_0)).



Definition ex_ev_Sn : ex (fun n => ev (S n))
  := ex_intro (fun n => ev (S n)) 1 (ev_SS 0 ev_0).







Inductive True : Prop :=
  | I : True.





Definition p_implies_true : forall P, P -> True
  := fun _ _ => I.




Inductive False : Prop := .



Fail Definition contra : False :=
  0 = 1.



Definition false_implies_zero_eq_one : False -> 0 = 1 :=
  fun contra => match contra with end.





Definition ex_falso_quodlibet' : forall P, False -> P
  := fun _ contra => match contra with end.


End Props.






Module EqualityPlayground.

Inductive eq {X:Type} : X -> X -> Prop :=
  | eq_refl : forall x, eq x x.

Notation "x == y" := (eq x y)
                       (at level 70, no associativity)
                     : type_scope.





Lemma four: 2 + 2 == 1 + 3.
Proof.
  apply eq_refl.
Qed.



Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), []++[x] == x::[]  :=
  fun (X:Type) (x:X) => eq_refl [x].



Definition eq_add : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2) :=
  fun n1 n2 Heq =>
    match Heq with
    | eq_refl n => eq_refl (S n)
    end.





Lemma succ_inj_eq_transitive_3 : forall n1 n2 : nat, forall H : n1 == n2, forall x : nat, S x == S x.

Proof.
intros.
(* We apply eq_refl because any term is equal to itself.
*)
  apply eq_refl.
Qed.

Lemma eq_succ_preserves_eq_2 : forall n1 n2 : nat, forall H : n1 == n2, S n1 == S n2.

Proof.
(* Direct application of eq_ind *)
  intros n1 n2 H.
apply eq_ind with (x := n1) (y := n2).
- (* Trivial reflextivity case to be proven *)
    apply (@succ_inj_eq_transitive_3 n1 n2 H).
- (* Hypothesis provided *)
    exact H.
Qed.

Lemma eq_succ_preserves_eq_1 : forall n1 n2 : nat, forall H : n1 == n2, S n1 == S n2.




Proof.
(* Since `H` is a hypothesis stating that `n1 = n2`, we can directly use `eq_ind` *)
(* which is also known as the `rewrite` tactic when proving equalities.
*)

intros n1 n2 H.
(* Apply `eq_ind` to change `S n1` to `S n2` given `n1 = n2` *)

apply (@eq_succ_preserves_eq_2 n1 n2 H).
Qed.

Lemma eq_succ_preserves_eq_0 : forall n1 n2 : nat, forall H : n1 == n2, S n1 == S n2.

Proof.
(* Introduce n1 and n2, and their equality hypothesis H.
*)
  intros n1 n2 H.
(* By the principle of substitutivity (replacing equals with equals), we use H *)
  (* to replace n1 with n2 in the goal, resulting in S n2 == S n2.
*)
  apply (@eq_succ_preserves_eq_1 n1 n2 H).
Qed.

Theorem eq_add' : forall (n1 n2 : nat), n1 == n2 -> (S n1) == (S n2).

Proof.
intros n1 n2 H.
(* Introduce the natural numbers n1 and n2, and the hypothesis H that n1 == n2 *)
  apply (@eq_succ_preserves_eq_0 n1 n2 H).
Qed.







From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import Imp Maps.



Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
    | <{ skip }> =>
        st
    | <{ l := a1 }> =>
        (l !-> aeval st a1 ; st)
    | <{ c1 ; c2 }> =>
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | <{ if b then c1 else c2 end }> =>
        if (beval st b)
          then ceval_step1 st c1
          else ceval_step1 st c2
    | <{ while b1 do c1 end }> =>
        st  
  end.








Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | O => empty_st
  | S i' =>
    match c with
      | <{ skip }> =>
          st
      | <{ l := a1 }> =>
          (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step2 st c1 i'
            else ceval_step2 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.



Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step3 st c1 i'
            else ceval_step3 st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.



Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (l !-> aeval st a1 ; st)
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.



Definition pup_to_n : com
  := <{ Y := 0;
        while X > 0 do
          Y := Y + X;
          X := X - 1
        end }>.

Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.




Definition peven : com
  := <{ Z := 0;
        while X > 0 do
          if Z = 0 then Z := 1 else Z := 0 end;
          X := X - 1
        end }>.

Example peven0 :
  test_ceval (X !-> 0) peven = Some (0, 0, 0).
Proof. reflexivity. Qed.

Example peven1 :
  test_ceval (X !-> 1) peven = Some (0, 0, 1).
Proof. reflexivity. Qed.

Example peven2 :
  test_ceval (X !-> 2) peven = Some (0, 0, 0).
Proof. reflexivity. Qed.

Example peven3 :
  test_ceval (X !-> 3) peven = Some (0, 0, 1).
Proof. reflexivity. Qed.

Example peven4 :
  test_ceval (X !-> 4) peven = Some (0, 0, 0).
Proof. reflexivity. Qed.






Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  - 
    intros c st st' H. discriminate H.

  - 
    intros c st st' H.
    destruct c;
           simpl in H; inversion H; subst; clear H.
      +  apply E_Skip.
      +  apply E_Asgn. reflexivity.

      + 
        destruct (ceval_step st c1 i') eqn:Heqr1.
        * 
          apply E_Seq with s.
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. assumption.
        * 
          discriminate H1.

      + 
        destruct (beval st b) eqn:Heqr.
        * 
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        * 
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      +  destruct (beval st b) eqn :Heqr.
        * 
         destruct (ceval_step st c i') eqn:Heqr1.
         { 
           apply E_WhileTrue with s. rewrite Heqr.
           reflexivity.
           apply IHi'. rewrite Heqr1. reflexivity.
           apply IHi'. assumption. }
         {  discriminate H1. }
        * 
          injection H1 as H2. rewrite <- H2.
          apply E_WhileFalse. apply Heqr. Qed.






Definition manual_grade_for_ceval_step__ceval_inf : option (nat*string) := None.


Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  - 
    simpl in Hceval. discriminate Hceval.
  - 
    destruct i2 as [|i2']. inversion Hle.
    assert (Hle': i1' <= i2') by lia.
    destruct c.
    + 
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + 
      simpl in Hceval. inversion Hceval.
      reflexivity.
    + 
      simpl in Hceval. simpl.
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * 
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * 
        discriminate Hceval.

    + 
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval;
        assumption.

    + 
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption.
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      * 
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite -> Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      * 
        simpl in Hceval. discriminate Hceval.  Qed.





Lemma aeval_ceval_step_assignment_existence_0 : forall st : state, forall a : aexp, forall n : nat, forall x : string, forall H : aeval st a = n, exists i : nat,
  ceval_step st <{ x := a }> i = Some (x !-> n; st).

Proof.
(* Since assignment is a single step in our operational semantics,
     we can choose i = 1, which means the command will complete in one step.
*)
  intros st a n x H.
exists 1.
(* We provide 1 as the existential witness *)

  (* And now we prove that ceval_step for assignment evaluates correctly *)
  simpl.
(* This unfolds the first step of ceval_step function *)
  rewrite H.
(* We apply the hypothesis H to match aeval st a with n *)
  reflexivity.
(* The ceval_step with i = 1 evaluates to x !-> n; st, as required *)

Qed.

Theorem ceval__ceval_step : forall c st st',
      st =[ c ]=> st' ->
      exists i, ceval_step st c i = Some st'.

Proof.
(* Induction on the derivation of st =[ c ]=> st' *)
  intros c st st' Hce.
induction Hce.
- (* <{skip}> *)
    exists 1; simpl; reflexivity.
- (* <{l := a}> *)
    apply (@aeval_ceval_step_assignment_existence_0 st a n x H).
- (* <{c1;c2}> *)
    (* For the sequential composition, we have to find an i such that
       the first command takes up to i steps, then show that the second
       command can be done in one additional step since we will use
       the result of the first command as the new state *)
    destruct IHHce1 as [i1 Hce1].
destruct IHHce2 as [i2 Hce2].
exists (S (i1 + i2)); simpl.
rewrite Hce1.
simpl.
apply Hce2.
- (* <{if b then c1 else c2 end}> *)
    (* For if statements, the situation is similar to the sequence,
       we just need to account for the additional step for the evaluation
       of the conditional itself.
*)
    destruct IHHce as [i Hce1].
exists (S i); simpl.
rewrite H.
simpl.
apply Hce1.
- (* <{while b1 do c1 end}; bas case where b1 is false *)
    (* For the while loop with the guard evaluating to false initially
       we can use 1 as the number of required steps.
*)
    exists 1.
simpl.
rewrite H.
reflexivity.
- (* <{while b1 do c1 end}; recursive case where b1 is true initially *)
    (* For the while loop where the guard evaluates to true, we need to take into
       account the number of steps the body takes and then show that there is
       one additional step for one more iteration of the while loop *)
    destruct IHHce1 as [i1 Hce1].
destruct IHHce2 as [i2 Hce2].
exists (S (i1 + i2)).
simpl.
rewrite H.
simpl.
rewrite Hce1.
simpl.
apply Hce2.
Qed.







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




Theorem ceval_step_more : forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.

Proof.
intros i1 i2 st st' c Hle Hceval1.
generalize dependent st'.
generalize dependent st.
generalize dependent c.
induction i2 as [|i2' IH]; intros c st st' Hle Hceval1.
- (* Case i2 = 0: contradiction, because i1 cannot be less than or equal to 0 with a Some result *)
    inversion Hle; subst; inversion Hceval1.
- (* Case i2 = S i2': We consider if i1 is zero or has a successor *)
    destruct i1 as [|i1'].
+ (* Case i1 = 0 *)
      inversion Hceval1.
+ (* Case i1 = S i1' *)
      simpl in Hceval1.
simpl.
(* we must show that ceval_step st c (S i2') = Some st' *)
      destruct c; try (rewrite Hceval1; reflexivity).
* (* Case c = c1; c2 *)
        remember (ceval_step st c1 i1') as st_c1_result.
destruct st_c1_result as [st_c1 | ]; inversion Hceval1; subst.
apply IH with (st':=st'0) in H1; try (apply le_S_n; assumption).
rewrite <- Heqst_c1_result in H1.
simpl.
rewrite H1.
now apply IH.
* (* Case c = if b then c1 else c2 *)
        destruct (beval st b);
          now apply IH.
* (* Case c = while b1 do c1 end *)
        destruct (beval st b1).
-- remember (ceval_step st c1 i1') as st_c1_result.
destruct st_c1_result as [st_c1 | ]; inversion Hceval1; subst.
apply IH with (st':=st'0) in H1; try (apply le_S_n; assumption).
rewrite <- Heqst_c1_result in H1.
simpl.
rewrite H1.
now apply IH.
-- simpl.
now rewrite Hceval1.
Qed.
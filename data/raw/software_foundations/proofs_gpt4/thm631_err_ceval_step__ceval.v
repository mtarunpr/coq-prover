






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








Theorem ceval_step__ceval : forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      st =[ c ]=> st'.

Proof.
intros c st st' H.
(* We need to induct over the command `c`, remembering `st` and `st'`.
*)
  remember c as c'.
generalize dependent st.
generalize dependent st'.
induction c' as [| a1 l | c1 IHc1 c2 IHc2
                      | b c1 IHc1 c2 IHc2
                      | b1 c1 IHc1];
  intros st' st H Hceval.
- (* skip *)
    exists 1; simpl.
rewrite <- Hceval.
reflexivity.
- (* := *)
    exists 1; simpl.
rewrite <- Hceval.
reflexivity.
- (* ; *)
    (* We first extract the existential from the hypothesis.
*)
    inversion H as [i Hi].
simpl.
simpl in Hi.
revert Hi.
(* We need to work with the monadic structure of the statements - essentially sequence the operations.
*)
    destruct (ceval_step st c1 i) eqn:E1.
+ (* First part of sequence computes to some state, using IHc1 *)
      apply IHc1 in E1.
* (* Use the fact that E1: st =[ c1 ]=> s, and now we use IHc2 with the new state 's'.
*)
        intros E2.
apply IHc2 in E2.
-- (* s =[ c2 ]=> st' by IHc2, now we combine the two to show st =[ c1;c2 ]=> st' *)
           eapply E_Seq; eauto.
-- (* Provide the existential proof for c2 part *)
           rewrite <- Hceval.
exists i.
auto.
* (* Provide the existential proof for c1 part *)
        exists i.
auto.
+ (* In case the first part computes to None, we won't find a rule that matches.
*)
      discriminate.
- (* if *)
    (* Extract the existential proof from the hypothesis.
*)
    inversion H as [i Hi].
simpl.
(* Depending on the value of `beval`, the `if` will proceed with `c1` or `c2`.
*)
    destruct (beval st b) eqn:Eb.
+ (* Case where `beval st b` is true *)
      simpl in Hi.
apply IHc1 in Hi.
* (* Using the fact that st =[ c1 ]=> st' due to the induction hypothesis *)
        eapply E_IfTrue.
-- (* Converting `beval st b = true` assumption to the statement form *)
           auto.
-- (* From the induction hypothesis *)
           apply Hi.
* (* Provide the existential proof for c1 *)
        exists i.
auto.
+ (* Case where `beval st b` is false *)
      simpl in Hi.
apply IHc2 in Hi.
* (* Using the fact that st =[ c2 ]=> st' due to the induction hypothesis *)
        eapply E_IfFalse.
-- (* Converting `beval st b = false` assumption to the statement form *)
           auto.
-- (* From the induction hypothesis *)
           apply Hi.
* (* Provide the existential proof for c2 *)
        exists i.
auto.
- (* while *)
    inversion H as [i Hi].
(* We destructure the `while` to show evidence of `Some st'`, trying both cases of beval.
*)
    remember (beval st b1) as bv.
destruct bv;
    simpl in Hi;
    [
      | remember (ceval_step st c1 i) as cv;
        destruct cv;
        [| discriminate]
    ].
+ (* Case where `beval st b1` is false, directly apply E_WhileFalse *)
      eapply E_WhileFalse.
rewrite Heqbv.
reflexivity.
+ (* Case where `beval st b1` is true *)
      (* Use the lemma ceval_step_more to obtain more steps *)
      symmetry in Heqcv.
apply IHc1 in Heqcv.
assert (G: forall i1 i2 st st', ceval_step st c1 (i1 + i2) = Some st' -> ceval_step st c1 i2 = Some st').
{ intros i1 i2.
induction i1 as [| i1' ].
- auto.
- simpl.
intros.
destruct (ceval_step st c1 i1').
apply IHi1'.
auto.
discriminate.
}
      apply G in Hi.
apply IHc in Hi.
* (* Using the IHc that st =[ WHILE b1 DO c1 END ]=> st' *)
        eapply E_WhileTrue with (st' := s).
-- rewrite Heqbv.
reflexivity.
-- apply Heqcv.
-- apply Hi.
* exists i.
auto.
Qed.
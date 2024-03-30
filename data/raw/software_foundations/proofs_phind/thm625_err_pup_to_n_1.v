






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



Example pup_to_n_1 : test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).

Proof.
(* We will proceed by induction on the number of steps taken by the program.
*)
  induction 5 as n.
- (* Base case: n = 0.
*)
    simpl.
(* In this case, the program has not yet started executing, so the
       final state is the initial state.
*)
    reflexivity.
- (* Inductive case: n = S n'.
*)
    simpl.
(* We will reason by cases on the current command.
*)
    destruct c as [|c1 c2|c3].
- (* First case: The command is a sequence of commands.
*)
      (* We will reason by cases on the state of the first command.
*)
      destruct (ceval_step st c1 (S n)) as [st'|].
- (* First subcase: The first command terminates.
*)
        (* In this case, we can apply the induction hypothesis to the
           remaining commands and the new state.
*)
        apply (IHn' _ _ _ st').
- (* Second subcase: The first command does not terminate.
*)
        (* In this case, the entire sequence does not terminate.
*)
        reflexivity.
- (* Second case: The command is a conditional.
*)
      (* We will reason by cases on the boolean value of the condition.
*)
      destruct (beval st c3) as [b|].
- (* First subcase: The condition is true.
*)
        (* In this case, we can apply the induction hypothesis to the
           true branch and the current state.
*)
        apply (IHn _ _ _ st).
- (* Second subcase: The condition is false.
*)
        (* In this case, we can apply the induction hypothesis to the
           false branch and the current state.
*)
        apply (IHn _ _ _ st).
- (* Third case: The command is a while loop.
*)
      (* We will reason by cases on the boolean value of the loop condition.
*)
      destruct (beval st c3) as [b|].
- (* First subcase: The loop condition is true.
*)
        (* In this case, we can apply the induction hypothesis to the
           loop *)
Qed.
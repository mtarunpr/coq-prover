

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Tactics.



Check (3 = 3) : Prop.

Check (forall n m : nat, n + m = m + n) : Prop.



Check 2 = 2 : Prop.

Check 3 = 2 : Prop.

Check forall n : nat, n = 2 : Prop.







Theorem plus_2_2_is_4 : 2 + 2 = 4.

Proof.
(* We will use the reflexivity tactic to prove this theorem.
Reflexivity is a simple tactic that checks if the two terms are equal and 
     if so, it closes the proof.
In this case, 2 + 2 is indeed equal to 4, 
     so reflexivity will work.
*)
  reflexivity.
Qed.
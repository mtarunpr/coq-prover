

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





Theorem plus_claim_is_true : plus_claim.

Proof.
(* plus_claim is defined as 2 + 2 = 4 which is the same as the proven theorem plus_2_2_is_4.
We can just apply this theorem to prove plus_claim *)
apply plus_2_2_is_4.
Qed.
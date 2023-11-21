Require Import Arith.

Lemma helper_lemma_0 : forall a b n' : nat, forall Hneq : S n' <> 0, forall Heq : S n' * a = S n' * b, a = b.

Proof.

(* Still, our goal is to prove that 'a' and 'b' are equal knowing that 'a' and 'b' multiplied by the same non-zero number 'S n' give the same result. 
   I intended to use the property of the cancellation for multiplication in the previous proof, but it seems that there was an issue with flipping the equation. 
   Now I need to ensure that the first factor in the product is not equal to zero, not the second factor. *)

intros a b n' Hneq Heq.
apply Nat.mul_cancel_l with (p := S n').

(* Coq does not accept 'S n' <> 0 in this case as the 'n' is successor of some natural number. It means that 'S n' is always non-zero. We can just assert it using 'Nat.neq_succ_0'. *)
apply Nat.neq_succ_0.

(* Now, we can use our hypothesis. *)
apply Heq.


Qed.

Theorem mult_lemma6 : forall (a b n:nat),(n <> O)->(n*a=n*b)->(a=b).


Proof.



  (* We will use induction on n *)
  
intros a b n Hneq Heq.


  (* If n isn't zero, n has to be 1 or (S (n - 1)). We perform a case analysis *)
  
destruct n as [| n'].
 
  (* contradiction: n cannot be zero because we assumed n is not zero *)
  
contradict Hneq; reflexivity.


  (* At this point, our goal is to prove a = b given n' * a = n' * b *)
  
apply (@helper_lemma_0 a b n' Hneq Heq).

Qed.
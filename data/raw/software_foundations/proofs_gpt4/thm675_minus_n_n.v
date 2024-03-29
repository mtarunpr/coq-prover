






From LF Require Export Basics.








Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.



Proof.
  intros n.
  simpl. 
Abort.



Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - 
    reflexivity. 
  - 
    simpl.       
Abort.





Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  -     reflexivity.
  -  simpl. rewrite -> IHn'. reflexivity.  Qed.





Theorem minus_n_n : forall n,
  minus n n = 0.

Proof.
(* We apply induction on the variable n.
*)
  induction n as [| n' IHn'].
- (* Case n = 0 *)
    (* The goal simplifies to: 0 - 0 = 0 which is trivially true *)
    simpl.
reflexivity.
- (* Case n = S n', where n' is a natural number *)
    (* We have the inductive hypothesis IHn' that n' - n' = 0 *)
    (* To prove: (S n') - (S n') = 0 *)
    simpl.
(* The goal now contains n' - n', which we can replace by using IHn' *)
    apply IHn'.
Qed.
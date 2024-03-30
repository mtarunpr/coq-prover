

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
(* We will use the induction principle for ev to prove ev_4''.
*)
  induction 4 as [ | n IHn].
- (* Base case: n = 0 *)
    (* We need to prove ev 0.
This is the ev_0 constructor of ev.
*)
    apply ev_0.
- (* Inductive case: n = S (S n') *)
    (* We need to prove ev (S (S n')).
This is the ev_SS constructor of ev.
*)
    (* We will use the induction hypothesis IHn.
*)
    apply (ev_SS (S n') IHn).
Qed.
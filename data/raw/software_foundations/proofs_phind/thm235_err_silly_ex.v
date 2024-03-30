



Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Poly.






Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.



  apply eq.  Qed.



Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.



Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m)  ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.




Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.

Proof.
(*
     We will proceed by induction on p.
The base case will show that if even 0 = true, then odd (S 0) = true.
The inductive step will show that if even p = true and odd (S p) = true, then even (S (S p)) = false.
*)
  intros.
generalize dependent p.
induction p as [|p' IHp'].
- (* Base case: p = 0 *)
    intros H0 H1 H2.
(* We need to show that odd (S 0) = true.
By definition, odd 0 = false and even 0 = true.
Therefore, we need to show that odd 1 = true.
By the first hypothesis, H0, we have even 1 = false.
Therefore, by the second hypothesis, H1, we have odd 1 = true.
*)
    apply H1.
apply H0.
- (* Inductive step: IHp' : even p' = true -> odd (S p') = true *)
    intros H0 H1 H2.
(* We need to show that odd (S (S p')) = true.
By the inductive hypothesis, IHp', we have even p' = true.
Therefore, by the first hypothesis, H0, we have even (S p') = false.
Therefore, by the second hypothesis, H1, we have odd (S (S p')) = true.
*)
    apply IHp'.
apply H0.
Qed.
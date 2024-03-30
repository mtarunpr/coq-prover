



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
(*
     We will proceed by induction on the equality n = m.
The base case will be when n = m is true, and the inductive
     case will be when n = m is false.
*)
  intros n m H H2.
(*
     Base case: n = m is true.
We will apply H2 with q := n and r := m to prove [n] = [m].
*)
  subst.
apply H2.
reflexivity.
(*
     Inductive case: n = m is false.
We will show that this leads to a contradiction.
We know that n <> m, so we can apply the induction hypothesis
     on the equality (n, n) = (m, m) to derive a contradiction.
*)
  assert (H3 : (n, n) = (m, m) -> False).
{
    intros H4.
induction H4 as [H5 [H6 H7]].
(*
       In this subgoal, we have H5 : n = m and H6 : n = m -> False.
We will apply H6 to H5 to derive a contradiction.
*)
    apply H6 in H5.
contradiction.
}
  (*
     Now we have H3 : (n, n) = (m, m) -> False.
We will apply the induction hypothesis on the equality (n, n) = (m, m)
     to derive a contradiction.
*)
  apply H3 in H.
contradiction.
Qed.




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
(* The goal is to prove [n;o] = [m;p].
We are given that n = m and n = m -> [n;o] = [m;p].
We can use the given hypothesis n = m to rewrite the goal as [m;o] = [m;p].
Now we need to prove [m;o] = [m;p].
Since m is the same in both lists, we just need to prove o = p.
But we are given n = m -> [n;o] = [m;p], which means that if n = m, then o = p.
So, we can apply this hypothesis with m in place of n to get o = p.
*)
  intros n m o p H1 H2.
rewrite H1 in H2.
apply H2.
Qed.
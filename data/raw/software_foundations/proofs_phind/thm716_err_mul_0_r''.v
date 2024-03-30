



Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export ProofObjects.






Check nat_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.





Theorem mul_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind.
  -  reflexivity.
  -  simpl. intros n' IHn'. rewrite -> IHn'.
    reflexivity.  Qed.





Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n' IHn'. simpl. rewrite IHn'. reflexivity. Qed.








Inductive time : Type :=
  | day
  | night.

Check time_ind :
  forall P : time -> Prop,
    P day ->
    P night ->
    forall t : time, P t.



Inductive rgb : Type :=
  | red
  | green
  | blue.
Check rgb_ind :
  forall P : rgb -> Prop,
    P red ->
    P green ->
    P blue ->
    forall x : rgb, P x.




Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).

Check natlist_ind :
  forall P : natlist -> Prop,
    P nnil  ->
    (forall (n : nat) (l : natlist),
        P l -> P (ncons n l)) ->
    forall l : natlist, P l.





Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat).



Check natlist'_ind :
  forall P : natlist' -> Prop,
    P nnil' ->
    (forall l : natlist', P l -> forall n : nat, P (nsnoc l n)) ->
    forall n : natlist', P n.



Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).



Definition booltree_property_type : Type := booltree -> Prop.

Definition base_case (P : booltree_property_type) : Prop
  := P bt_empty.

Definition leaf_case (P : booltree_property_type) : Prop
  := forall b : bool, P (bt_leaf b).

Definition branch_case (P : booltree_property_type) : Prop
  := forall (b : bool) (t1 : booltree), P t1 -> forall (t2 : booltree), P t2 -> P (bt_branch b t1 t2).

Definition booltree_ind_type :=
  forall (P : booltree_property_type),
    base_case P ->
    leaf_case P ->
    branch_case P ->
    forall (b : booltree), P b.



Theorem booltree_ind_type_correct : booltree_ind_type.
Proof. exact booltree_ind. Qed.





Inductive Toy : Type :=
  | con1 (b : bool)
  | con2 (n : nat) (t : Toy)
.



Theorem Toy_correct : exists f g,
  forall P : Toy -> Prop,
    (forall b : bool, P (f b)) ->
    (forall (n : nat) (t : Toy), P t -> P (g n t)) ->
    forall t : Toy, P t.
Proof. exists con1. exists con2. exact Toy_ind. Qed.












Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind :
  forall (X : Type) (P : tree X -> Prop), (forall (x : X), P (leaf X x)) -> (forall (t1 : tree X), P t1 -> forall (t2 : tree X), P t2 -> P (node X t1 t2)) -> forall (t : tree X), P t.


 
Inductive mytype (X:Type) : Type :=
  | constr1 (x:X)
  | constr2 (n:nat)
  | constr3 (m:mytype X) (n:nat).
Check mytype_ind :
  forall (X : Type) (P : mytype X -> Prop),
    (forall x : X, P (constr1 X x)) ->
    (forall n : nat, P (constr2 X n)) ->
    (forall m : mytype X, P m ->
      forall n : nat, P (constr3 X m n)) ->
    forall m : mytype X, P m.


 
Inductive foo (X Y : Type) : Type :=
  | bar (x : X)
  | baz (y : Y)
  | quux (f : nat -> foo X Y).
Check foo_ind :
  forall (X Y : Type) (P : foo X Y -> Prop),
    (forall x : X, P (bar X Y x)) ->
    (forall y : Y, P (baz X Y y)) ->
    (forall f1 : nat -> foo X Y,
      (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
    forall f2 : foo X Y, P f2.




Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.


Check foo'_ind :
  forall (X : Type) (P : foo' X -> Prop),
    (forall (l : list X) (f : foo' X),
      P f -> P (C1 X l f)) ->
    P (C2 X) ->
    forall f : foo' X, P f.








Definition P_m0r (n:nat) : Prop :=
  n * 0 = 0.



Definition P_m0r' : nat -> Prop :=
  fun n => n * 0 = 0.





Theorem mul_0_r'' : forall n:nat,
  P_m0r n.

Proof.
(* We will prove the theorem by induction on n.
*)
  intros n.
induction n as [|n' IHn'].
(* Base case: n = 0 *)
  - simpl.
(* We need to prove P_m0r 0, which is n * 0 = 0.
*)
    reflexivity.
(* Inductive case: n = S n' *)
  - simpl.
(* We need to prove P_m0r (S n'), which is (S n') * 0 = 0.
*)
    (* By definition of multiplication, (S n') * 0 = S (n' * 0).
*)
    rewrite IHn'.
(* Now we have S (n' * 0) = S 0, which is true by definition of successor.
*)
    reflexivity.
Qed.
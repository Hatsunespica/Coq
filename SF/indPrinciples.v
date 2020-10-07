Set Warnings "-notation-overridden,-parsing".
Require Export proofObjects.

Theorem mult_0_r' : forall n:nat,
    n*0 =0.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. assert(tmpH: S n = 1 + n). reflexivity.
    rewrite tmpH. rewrite PeanoNat.Nat.mul_add_distr_r.  simpl. apply H.
Qed.

Theorem plus_one_r' : forall n : nat,
    n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. assert(tmpH: S n + 1 = S(n + 1)). reflexivity.
    rewrite tmpH,H. reflexivity.
Qed.

Inductive yesno :Type:=
| yes
| no.

Inductive rgb:Type:=
| red
| green
| blue.

Inductive natlist:Type:=
| nnil
| ncons (n : nat) (l : natlist).

Inductive byntree :Type :=
| bempty
| bleaf (yn:yesno)
| nbranch (yn:yesno) (t1 t2:byntree).

Inductive ExSet :Type:=
| con1 (b : bool)
| con2 (n: nat) (e :ExSet).

Inductive list (X:Type) :Type :=
| nil : list X
| cons : X -> list X -> list X.

Inductive tree (X:Type) : Type :=
| leaf (x :X)
| node (t1 t2:tree X).

Inductive mytype (X :Type) :Type:=
| constr1 (x:Type)
| constr2 (n:nat)
| constr3 (m : mytype X) (n:nat).

Inductive foo(X Y :Type)  : Type :=
| bar (x :X)
| baz (y:Y)
| quux (f1 : nat -> foo X Y).

Inductive foo' (X:Type) :Type :=
| C1 (l :list X) (f : foo' X)
| C2 .

Definition P_m0r (n:nat) : Prop :=
  n*0=0.

Definition P_m0r' : nat-> Prop :=
  fun n => n*0 =0.

Theorem mult_0_r'' : forall n:nat,
    P_m0r n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros. unfold P_m0r. unfold P_m0r in H. simpl. apply H.
Qed.

Theorem plus_assoc' : forall n m p :nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [| n'].
  -  reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_comm' : forall n m : nat,
    n + m = m + n.
Proof.
  induction n as [| n'].
  - intros m. rewrite <- plus_n_O. reflexivity.
  - intros m. simpl. rewrite IHn'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem plus_comm'' : forall n m: nat,
    n + m = m + n.
Proof.
  induction m as [| m'].
  - simpl. rewrite <-plus_n_O. reflexivity.
  - simpl. rewrite <- IHm'. rewrite <- plus_n_Sm. reflexivity.
Qed.

Definition P_comm (n m : nat)  : Prop :=
  n + m = m + n.
Theorem plus_comm''' : forall n m, P_comm n m.
Admitted.
Definition P_assoc ( n m p :nat) : Prop:=
  n + (m+ p) = (n + m)+p.
Theorem plus_assoc'' : forall n m p, P_assoc n m p.
Admitted.

Inductive le (n:nat) : nat -> Prop :=
| le_n : le n n
| le_S m (H: le n m) : le n (S m).

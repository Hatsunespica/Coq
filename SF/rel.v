Set Warnings "-notation-overridden,-parsing".
Require Export indProp.

Definition relation (X:Type) := X -> X -> Prop.
Definition partial_function {X:Type} (R: relation X) :=
  forall x y1 y2: X, R x y1 -> R x y2 -> y1 = y2.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function. intros.
  inversion H. inversion H0. reflexivity.
Qed.

Theorem le_not_a_paritial_function :
  ~(partial_function le).
Proof.
  unfold partial_function.
  intros H. pose proof (H 0 0 1) as H1.
  assert(tmpH1: 0 =1). apply H1. apply (le_n 0).  apply le_S, (le_n 0). inversion tmpH1.
Qed.

Theorem total_relation_not_a_partial_function :
  ~(partial_function total_relation).
Proof.
  unfold partial_function. intros H.
  pose proof (H 0 0 1) as H1.
  assert(tmpH: 0=1). apply H1. apply tr_1.  apply tr_2.   unfold lt. apply le_n.
  inversion tmpH.
Qed.

Print empty_relation.

Definition reflexive {X:Type} (R:relation X) :=
  forall a : X, R a a.
Theorem le_reflexive :
  reflexive le.
Proof.
  intros a. apply le_n.
Qed.

Definition transitive {X:Type} (R:relation X) :=
  forall a b c :X, (R a b) -> (R b c) -> (R a c).


Theorem le_trans:
  transitive le.
Proof.
  unfold transitive. intros.
  apply (PeanoNat.Nat.le_trans a b c).
  congruence. congruence.
Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold transitive. intros.
  apply (PeanoNat.Nat.lt_trans a b c).
  apply H. apply H0.
Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  - apply le_S. apply Hnm.
  - apply le_S. apply IHHm'o.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold transitive. unfold lt.
  intros a b c Hab Hbc.
  induction c.
  - inversion Hbc.
  - simpl. inversion Hbc.
    + apply le_S. subst c. congruence.
    + subst m. apply le_S. apply IHc in H0. congruence.
Qed.

Theorem le_S_n : forall n m,
    (S n <= S m) -> n <= m.
Proof.
  intros.
  inversion H.
  - apply le_n.
  - subst m0. apply (le_trans n (S n) m).
    + apply le_S, le_n.
    + congruence.
Qed.

Theorem le_Sn_n :forall n,
    ~(S n<= n).
Proof.
  intros.
  intros H.
  induction n.
  - inversion H.
  - apply IHn, le_S_n, H.
Qed.

Definition symmetric {X:Type} (R:relation X):=
  forall a b :X, (R a b) -> (R b a).

Theorem le_not_symmetric:
  ~(symmetric le).
Proof.
  unfold symmetric. unfold not.
  intros. pose proof (H 0 1) as H1.
  assert(tmpH: 0<=1). apply le_S, le_n.
  apply H1 in tmpH. inversion tmpH.
Qed.

Definition antisymmetric {X:Type} (R:relation X) :=
  forall a b: X, (R a b) -> (R b a) -> a =b.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros a.
  induction a.
  - intros. inversion H. reflexivity. subst b. inversion H0.
  - intros. inversion H0.
    + reflexivity.
    + subst m. apply le_S in H as H3. apply le_S_n in H3.
      assert(tmpH: a =b). apply IHa. apply H3. apply H2.
      subst b. apply le_Sn_n in H. inversion H.
Qed.

Theorem le_step : forall n m p,
    n < m -> m <= S p -> n <= p.
Proof.
  intros.
  induction H.
  - apply le_S_n in H0. apply H0.
  - apply IHle. apply le_S in H0. apply le_S_n in H0. apply H0.
Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X:Type} (R : relation X):=
  (reflexive R) /\ (antisymmetric R) /\(transitive R).

Definition preorder{X:Type} (R:relation X):=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  split.
  - unfold reflexive. intros. apply le_n.
  - split.
    + apply le_antisymmetric.
    + apply le_trans.
Qed.

Inductive clos_refl_trans {A:Type} (R:relation A) :relation A:=
| rt_step x y (H: R x y) :clos_refl_trans R x y
| rt_refl x : clos_refl_trans R x x
| rt_trans x y z
           (Hxy : clos_refl_trans R x y)
           (Hyz: clos_refl_trans R y z) :
    clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall  n m,
    (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros. split.
  - intros H.
    induction H.
    + apply rt_refl.
    + apply (rt_trans next_nat n m (S m)).
      * apply IHle.
      * apply rt_step. apply nn.
  - intros H. induction H.
    + inversion H. apply le_S, le_n.
    + apply le_n.
    + apply (le_trans x y z). apply IHclos_refl_trans1. apply IHclos_refl_trans2.
Qed.

Inductive clos_refl_trans_1n {A:Type}
          (R: relation A)(x :A) : A -> Prop :=
| rt1n_refl : clos_refl_trans_1n R x x
| rt1n_trans (y z :A)
             (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z):
    clos_refl_trans_1n  R x z.

Lemma rsc_R: forall (X:Type) (R:relation X) (x y :X),
    R x y -> clos_refl_trans_1n R x y.
Proof.
  intros.
  apply (rt1n_trans R x  y y). apply H. apply rt1n_refl.
Qed.

Lemma rsc_trans:
  forall (X:Type) (R:relation X) (x y z :X),
    clos_refl_trans_1n R x y ->
    clos_refl_trans_1n R y z ->
    clos_refl_trans_1n R x z.
Proof.
  intros.
  induction H.
  - apply H0.
  - apply IHclos_refl_trans_1n in H0. apply rt1n_trans with y. apply Hxy. apply H0.
Qed.

Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y :X),
    clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  intros.
  split.
  - intros H. induction H.
    + apply rsc_R. apply H.
    + apply rt1n_refl.
    + apply rsc_trans with y. congruence. congruence.
  - intros H. induction H.
    + apply rt_refl.
    + apply rt_step in Hxy. apply rt_trans with y. congruence. congruence.
Qed.

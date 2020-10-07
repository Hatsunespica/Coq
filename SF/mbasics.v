Set Warning "-notation-overridden,-parsing".
Require Export poly.

Theorem silly:
  (forall n, evenb n =true -> oddb (S n) = true) ->  evenb 3 =true -> oddb 4 = true.
Proof.
  intros h1 h2.
  apply h1, h2.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
    l = rev l' -> l' = rev l.
Proof.
  intros l l' h1.
  rewrite  h1, rev_involutive.
  reflexivity.
Qed.

Lemma trans_eq: forall (X : Type) ( n m o : X),
    n = m -> m = o -> n = o.
Proof.
  intros X n m o h1 h2.
  rewrite h1.
  apply h2.
Qed.

Example trans_eq_example : forall (a b c d e f: nat),
    [a;b]=[c;d] -> [c;d]=[e;f] -> [a;b]=[e;f].
Proof.
  intros a b c d e f h1 h2.
  apply trans_eq with (m:=[c;d]).
  congruence.
  congruence.
Qed.

Example trans_sq_exercise : forall (n m o p:nat),
    m = (minustwo o) -> (n + p) = m -> (n + p) = (minustwo o).
Proof.
  intros n m o p h1 h2.
  rewrite h2.
  congruence.
Qed.

Theorem S_injective : forall (n m:nat),
    S n = S m -> n = m.
Proof.
  intros n m H.
  assert (H2: n = pred (S n)). { reflexivity. }
                               rewrite H2.
  rewrite H.
  reflexivity.
Qed.

Theorem S_injective' : forall (n m: nat),
    S n = S m ->
    n = m.
Proof.
  intros n m H.
  injection H.
  congruence.
Qed.

Theorem injection_ex1 : forall (n m o: nat),
    [n; m]=[o; o] -> [n] = [m].
Proof.
  intros n m o H.
  injection H.
  intros H1 H2.
  rewrite H1, H2.
  reflexivity.
Qed.

Theorem injection_ex2 : forall (n m :nat),
    [n] = [m] -> n = m.
Proof.
  intros n m H.
  injection H.
  congruence.
Qed.

Example injection_ex3 : forall (X: Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->  y :: l = x :: j -> x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H2.
  intros H3 H4.
  congruence.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
    S n = 0 -> 2 + 2 = 5.
Proof.
  intros n H.
  discriminate.
Qed.

Theorem discriminate_ex2 : forall (n m : nat),
    false = true -> [n] = [m].
Proof.
  intros n m H.
  discriminate.
Qed.


Example discriminate_ex3 :
  forall (X :Type) (x y z : X) ( l j : list X),
    x :: y :: l = [] -> x = z.
Proof.
  intros X x y z l j H.
  discriminate.
Qed.

Theorem plus_n_n_injective : forall n m,
    n + n = m + m -> n = m.
Proof.
  intros n.
  induction  n as [| n'].
  - intros m H.
    destruct m as [| m'].
    + reflexivity.
    + discriminate.
  - intros m.
    destruct m as [| m'].
    + discriminate.
    + intros H1.
      injection H1.
      intros H2.
      rewrite <- plus_n_Sm in H2.
      rewrite <- plus_n_Sm in H2.
      injection H2.
      intros H3.
      apply IHn' in H3.
      congruence.
Qed.

Fixpoint double (n : nat) :=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.

Theorem double_injective : forall n m,
    double n = double m -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  - simpl.
    destruct m as [| m'].
    + reflexivity.
    + discriminate.
  - simpl.
    intros m.
    destruct m as [| m'].
    + discriminate.
    + simpl.
      intros H.
      injection H.
      intros H1.
      apply IHn' in H1.
      congruence.
Qed.

Theorem nth_error_after_last : forall ( n : nat) (X :Type) (l : list X),
    length l = n -> nth_error l n =None.
Proof.
  intros n X l.
  generalize dependent n.
  generalize dependent X.
  induction l as [| s  t].
  - destruct n as [| n'].
    + reflexivity.
    + discriminate.
  - destruct n as [| n'].
    + discriminate.
    + simpl.
      intros H.
      injection H as H2.
      apply IHt in H2.
      congruence.
Qed.

Definition square n :=  n * n.

Definition bar x :=
  match x with
  | 0 => 5
  | S _ => 5
  end.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  unfold bar.
  intros [| m'].
  + reflexivity.
  + reflexivity.
Qed.

Definition sillyfun (n: nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false : forall ( n : nat),
    sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (beq_nat n 3).
  - reflexivity.
  - destruct (beq_nat n 5).
    + reflexivity.
    + reflexivity.
Qed.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
    | (lx, ly) => (x :: lx, y :: ly)
    end
  end.

Theorem combine_add: forall X Y (t: list(X*Y)) s1 s2 l1 l2,
    split t = (l1, l2) -> split ((s1, s2) :: t) = (s1 :: l1, s2 :: l2).
Proof.
  intros X Y t s1 s2 l1 l2 H.
  simpl.
  rewrite H.
  reflexivity.
Qed.


Theorem combine_split : forall X Y (l : list (X*Y)) l1 l2,
    split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| (s1, s2) t].
  - simpl.
    intros l1 l2 H.
    inversion H.
    reflexivity.
  - intros l1 l2 H.
    destruct (split t) as [t1 t2] eqn:E.
    assert (tmpH: split ((s1, s2) :: t) = (s1 :: t1, s2 :: t2)).
    {
      apply combine_add.
      congruence.
    }
    simpl.
    rewrite tmpH in H.
    injection H.
    intros H1 H2.
    rewrite <- H1, <- H2.
    simpl.
    assert (tmpH1 : (t1, t2) = (t1, t2)).
    {
      reflexivity.
    }
    apply IHt in tmpH1.
    rewrite tmpH1.
    reflexivity.
Qed.

Definition sillyfun1 (n :nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.

Theorem bool_fn_applied_thrice:
  forall (f : bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f true) eqn: ft.
  - destruct (f false) eqn : ff.
    + destruct b.
      congruence.
      congruence.
    + destruct b.
      congruence.
      congruence.
  - destruct (f false) eqn: ff.
    + destruct b.
      congruence.
      congruence.
    + destruct b.
      congruence.
      congruence.
Qed.

Theorem beq_injective :forall (n m:nat),
    beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  - intros [| m'] H.
    reflexivity.
    discriminate.
  - intros [| m'] H.
    + discriminate.
    + simpl.
      simpl in H.
      apply IHn' in H.
      congruence.
Qed.


Theorem beq_nat_sym : forall (n m:nat),
    beq_nat n m = beq_nat m n.
Proof.
  intros n.
  induction n as [| n'].
  - intros [| m'].
    + reflexivity.
    + reflexivity.
  - intros [| m'].
    + reflexivity.
    + simpl.
      apply IHn'.
Qed.

Theorem beq_nat_trans: forall n m p,
    beq_nat n m = true ->
    beq_nat m p = true ->
    beq_nat n p = true.
Proof.
  intros n m p H1 H2.
  apply beq_injective in H1.
  apply beq_injective in H2.
  rewrite <-  H1 in H2.
  rewrite H2.
  assert (H: forall (p0 : nat), beq_nat p0 p0 =true).
  {
    intros p0.
    induction p0 as [| p'].
    - reflexivity.
    - simpl.
      congruence.
  }
  apply H.
Qed.

Definition split_combine_statement :Prop :=
  forall X Y  (l1 : list X) (l2 : list Y),
    length l1 = length l2 -> split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l1.
  induction l1 as [| s1 t1].
  - intros [|s2 t2].
    + reflexivity.
    + discriminate.
  - intros [| s2 t2].
    + discriminate.
    + intros H.
      simpl in H.
      assert (tmpH: combine (s1 :: t1) (s2 :: t2) = (s1, s2) :: (combine t1 t2)).
      {
        reflexivity.
      }
      rewrite tmpH.
      simpl.
      injection H as H1.
      apply IHt1 in H1.
      rewrite H1.
      reflexivity.
Qed.

Theorem filter_exercise : forall (X :Type) (test : X -> bool)
                                 (x :X)(l lf:list X),
    filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l.
  induction l as [| s t].
  - discriminate.
  - destruct (test s) as [|] eqn:E.
    + simpl.
      rewrite E.
      intros lf H.
      injection H as H1.
      rewrite H1 in E.
      congruence.
    + simpl.
      rewrite E.
      intros lf H.
      apply IHt in H.
      congruence.
Qed.

Fixpoint forallb {X: Type} (test : X -> bool) (l :list X) :=
  match l with
  | nil => true
  | s :: t => match (test s) with
              | false => false
              | true => forallb test t
              end
  end.

Fixpoint existsb {X :Type} (test: X-> bool) (l : list X) :=
  match l with
  | nil => false
  | s :: t => match (test s) with
              | true => true
              | false => existsb test t
              end
  end.

Definition existsb' {X: Type} (test: X -> bool) (l : list X) : bool  :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existsb_eq : forall (X :Type) (test : X -> bool) (l : list X),
    existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l as [| s t].
  - unfold existsb'.
    reflexivity.
  - simpl.
    destruct (test s) eqn :E.
    + unfold existsb'.
      simpl.
      rewrite E.
      reflexivity.
    + simpl.
      assert (H: test s = false -> existsb' test (s :: t) = existsb' test t).
      {
        intros H1.
        unfold existsb'.
        simpl.
        rewrite H1.
        simpl.
        reflexivity.
      }
      apply H in E.
      rewrite E.
      rewrite IHt.
      congruence.
Qed.
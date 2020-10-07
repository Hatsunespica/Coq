Set Warnings "-notation-overridden, -parsing".
Require Export logic.
Require Coq.omega.Omega.

Inductive even : nat -> Prop:=
| ev_0 : even 0
| ev_ss  (n: nat) (H : even n) : even (S (S n)).

Theorem ev_4: even 4.
Proof.
  apply ev_ss.
  apply ev_ss.
  apply ev_0.
Qed.

Theorem  ev_4' : even 4.
Proof.
  apply (ev_ss 2 (ev_ss 0 ev_0)).
Qed.

Theorem ev_plus4 : forall n, even n -> even (4+ n).
Proof.
  intros n. simpl. intros H.
  apply ev_ss. apply ev_ss.
  congruence.
Qed.

Theorem ev_double : forall n,
    even (double n).
Proof.
  intros n.
  induction n as [| n' H].
  - simpl. apply ev_0.
  - simpl. apply ev_ss. apply H.
Qed.

Theorem ev_inversion:
  forall (n : nat), even n ->
                    (n = 0) \/ (exists n', n = S ( S n') /\ even n').
Proof.
  intros n E.
  destruct E as [| n' E'].
  - left. reflexivity.
  - right. exists n'. split. reflexivity. congruence.
Qed.

Theorem ev_minus2: forall n,
    even n -> even (pred (pred n)).
Proof.
  intros n [| n' E'].
  - simpl. apply ev_0.
  - simpl. congruence.
Qed.

Theorem evSS_ev : forall n,
    even (S (S n)) -> even n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H.
  - discriminate H.
  - destruct H as [n' [Hnm Hev]].
    injection Hnm. intros Heq. congruence.
Qed.

Theorem evSS_ev' : forall n,
    even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

Theorem one_not_even: ~even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [| [m [Hm _]]].
  - discriminate.
  - discriminate.
Qed.

Theorem one_not_even' : ~even 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev_even:forall n,
    even (S (S (S (S n)))) -> even n.
Proof.
  intros n H.
  inversion H as [| n' ].
  apply evSS_ev in H0.
  congruence.
Qed.

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H as [| n'].
  inversion H0. inversion H3.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
    [n; m] = [o; o] -> [n]=[m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 : forall (n : nat),
    S n = 0 -> 2 + 2 = 5.
Proof.
  intros n H.
  inversion H.
Qed.

Theorem ev_even : forall n,
    even n -> exists k,  n = double k.
Proof.
  intros n H.
  induction H as [|].
  - exists 0. reflexivity.
  - destruct IHeven as [k' H'].
    exists (S k'). simpl. rewrite H'. reflexivity.
Qed.


Theorem ev_even_iff:  forall n,
    even n <-> exists k, n=double k.
Proof.
  intros n. split.
  - apply ev_even.
  - intros H. destruct H as [k' H'].
    rewrite H'. apply ev_double.
Qed.

Theorem ev_sum : forall n m,
    even n -> even m -> even (n + m).
Proof.
  intros n m H1 H2.
  generalize dependent m.
  induction H1 as [| n' E' H1'].
  - simpl. congruence.
  - intros m H2.
    assert (tmpH: S (S n') + m = n' + S (S m)).
    {
      simpl. rewrite <- plus_n_Sm.  rewrite <- plus_n_Sm. reflexivity.
    }
    rewrite tmpH.
    apply (H1' (S (S m))).
    apply ev_ss in H2.
    apply H2.
Qed.

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn: even' n) (Hm : even' m) : even' (n + m).

Theorem even'_ev : forall n, even' n <-> even n.
Proof.
  intros n. split.
  - intros H.
    induction H as [| | n m H'].
    + apply ev_0.
    + apply ev_ss. apply ev_0.
    + simpl. apply ev_sum. congruence. congruence.
  - intros H.
    induction H as [| n H'].
    + apply even'_0.
    + simpl. assert(tmpH: S (S n) = 2 + n).  reflexivity.
      rewrite tmpH. apply even'_sum.
      * apply even'_2.
      * congruence.
Qed.

Theorem ev_ev_ev: forall n m,
    even (n+m) -> even n -> even m.
Proof.
  intros n m H1 H2.
  generalize dependent m.
  induction H2 as [| n' H' H2'].
  - intros m. simpl. congruence.
  - simpl. intros m H.  apply evSS_ev in H.
    apply H2' in H. apply H.
Qed.

Theorem ev_plus_plus: forall n m p,
    even (n + m) -> even (n + p)  -> even (m + p).
Proof.
  intros n m p H1 H2.
  rewrite <- even'_ev in H1.
  rewrite <- even'_ev in H2.
  assert(tmpH: even' ((n + m) +( n + p))). apply (even'_sum (n +m) (n + p)). congruence. congruence.
  assert(tmpH1: m + (n +p) = n + (m + p)). apply PeanoNat.Nat.add_shuffle3.
  assert(tmpH2: n+ m +( n + p) = n + n +(m + p)). rewrite <- plus_assoc. symmetry.
  rewrite <- plus_assoc. rewrite tmpH1. reflexivity.
  rewrite tmpH2 in tmpH.
  assert(tmpH3: even' (n + n)). rewrite even'_ev. rewrite <- double_plus. apply ev_double.
  rewrite even'_ev in tmpH. rewrite even'_ev in tmpH3.
  apply (ev_ev_ev (n+n) (m + p)). congruence. congruence.
Qed.

Module Playground.
  Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

  Notation "m <= n" := (le m n).

  Theorem test_le1:
    3 <= 3.
  Proof.
    apply le_n. Qed.

  Theorem test_le2:
    3 <=6.
  Proof.
    apply le_S. apply le_S. apply le_S. apply le_n.
  Qed.

  Theorem test_le3:
    (2 <= 1) -> 2 + 2 = 5.
  Proof.
    intros H. inversion H.
    inversion H2.
  Qed.

  End Playground.

  Definition lt (n m :nat) := le (S n) m.

  Notation " m < n " := (lt m n).

  Inductive square_of : nat -> nat -> Prop:=
  | sq n : square_of n (n * n).

  Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

  Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

  Inductive total_relation : nat -> nat -> Prop :=
  | tr_1 n : total_relation n n
  | tr_2 n m (H: lt n m) : total_relation n m
  | tr_3 n m (H: lt m n) : total_relation n m.

  Inductive empty_relation : nat -> Prop :=
  | er_1 n (H: lt n 0) : empty_relation n .

  Theorem Sle_le : forall n m, S n <= m -> n <= m.
  Proof.
    intros n m H.
    induction H as [| n' H'].
    - apply le_S, le_n.
    - apply le_S. apply IHH'.
  Qed.

  Lemma le_trans : forall m n o , m <= n -> n <= o -> m <= o.
  Proof.
    intros m n o H1 H2.
    inversion H2.
    - rewrite H in H1. apply H1.
    - induction H1 as [| n' H'].
      + apply le_S. apply H.
      + apply Sle_le in H. apply Sle_le in H2. apply IHH'.
        apply H2. apply H.
  Qed.

  Theorem O_le_n : forall n,
      0 <= n.
  Proof.
    intros n.
    induction n as [| n' H].
    - apply le_n.
    - apply le_S. apply H.
  Qed.

  Theorem n_le_m_Sn_le_Sm :forall n m,
      n <= m -> S n <= S m.
  Proof.
    intros n m H.
    induction H as [| n' H'].
    - apply le_n.
    - apply le_S. apply IHH'.
  Qed.

  Theorem Sn_le_Sm_n_le_m : forall n m,
      S n <= S m -> n <= m.
  Proof.
    intros n m H.
    inversion H.
    - apply le_n.
    - apply Sle_le in H1. apply H1.
  Qed.

  Theorem le_plus_1 : forall a b,
      a <= a + b.
  Proof.
    intros a b.
    induction b as [| b' H'].
    - rewrite <- plus_n_O. apply le_n.
    - rewrite <- plus_n_Sm. apply le_S. apply H'.
  Qed.

  Theorem  plus_lt : forall n1 n2 m,
      n1 + n2 < m -> n1 < m /\ n2 < m.
  Proof.
    unfold lt.
    intros n1 n2 m H.
    split.
    - assert(tmpH: S(n1 + n2) = S n1 + n2). reflexivity.
      rewrite tmpH in H.
      assert(tmpH2 : S n1 <= S n1 + n2). apply le_plus_1.
      apply (le_trans (S n1) (S n1 + n2) m).
      apply tmpH2. apply H.
    - assert(tmpH: S n2 <= S( n1 + n2)). rewrite plus_comm. rewrite <- plus_Sn_m. apply le_plus_1.
      apply (le_trans (S n2) (S n1 + n2) m) . apply tmpH. apply H.
  Qed.

  Theorem lt_S : forall  n m,
      n < m -> n < S m.
  Proof.
    unfold lt.
    intros n m H.
    apply le_S. apply H.
  Qed.

  Theorem leb_complete : forall n m,
      (leb n m) = true -> n <= m.
  Proof.
    intros n.
    induction n as [| n' H'].
    - intros m H. apply O_le_n.
    - intros [| m'].
      + intros H1. simpl in H1. discriminate.
      + intros H1. apply H' in H1. apply n_le_m_Sn_le_Sm. apply H1.
  Qed.

  Theorem leb_correct :forall n m,
      n <= m -> (leb n m) = true.
  Proof.
    intros n m. generalize dependent n.
    induction m as [| m' H'].
    - intros [| n']. reflexivity. intros H. simpl. inversion H.
    - intros [| n'] H.
      + reflexivity.
      + apply Sn_le_Sm_n_le_m in H. apply H' in H. simpl. apply H.
  Qed.

  Theorem leb_true_trans : forall n m o,
      (leb n m) = true -> (leb m o) = true -> (leb n o) = true.
  Proof.
    intros n m o H1 H2.
    apply leb_complete in H1. apply leb_complete in H2.
    apply leb_correct. apply (le_trans n m o).
    apply H1. apply H2.
  Qed.

  Module R.
    Inductive R : nat -> nat -> nat -> Prop:=
    | c1 : R 0 0 0
    | c2 m n o (H: R m n o) : R (S m) n (S o)
    | c3 m n o (H: R m n o): R m (S n) (S o)
    | c4 m n o (H :R (S m) (S n) (S (S o))) : R m n o
    | c5 m n o (H: R m n o) : R n m o.

    Theorem R_0_n :forall n,
        R 0 n n.
    Proof.
      intros n.
      induction n as [| n'].
      + apply c1.
      + apply c3 in IHn'.
        apply IHn'.
    Qed.

    Theorem R_n_0:forall n,
        R n 0 n.
    Proof.
      intros n.
      induction n as [| n'].
      + apply c1.
      + apply c2. apply IHn'.
    Qed.
    
    Definition fR : nat->nat->nat := plus.
    Theorem  R_equiv_fR: forall m n o, R m n o <-> fR m n = o.
    Proof.
      unfold fR.
      split.
      - intros H.
        induction H.
        + reflexivity.
        + rewrite plus_Sn_m. rewrite IHR. reflexivity.
        + rewrite <- plus_n_Sm. rewrite IHR. reflexivity.
        + simpl. rewrite <-  plus_n_Sm in IHR. injection IHR. intros H1. apply H1.
        + rewrite plus_comm. apply IHR.
      - generalize dependent m.
        induction n as [| n'].
        + intros m. intros H. rewrite <- plus_n_O in H. rewrite H. apply R_n_0.
        + intros m H. rewrite <- plus_n_Sm in H. rewrite <- plus_Sn_m in H.
          apply IHn' in H.  apply c3 in H. apply c3 in H. apply c4 in H. congruence.
    Qed.
    End R.

    Theorem neq_relf : forall (X: Type) (x : X),
        x <> x -> False.
    Proof.
      intros X x H.
      unfold not in H.
      assert(tmpH: x = x). reflexivity.
      apply H in tmpH.
      apply tmpH.
    Qed.
    

    Inductive subseq {T} : list T -> list T -> Prop :=
    | lnil n : subseq [] n
    | lapp x n m (H: subseq n m): subseq (x :: n) (x :: m)
    | lnapp x n m (H: subseq n m): subseq n (x :: m).

    Theorem subseq_a_ccl : forall T (a: T) (l1 l2 :list T),
        subseq (a :: l1) l2 -> subseq l1 l2.
    Proof.
      intros T a l1 l2.
      induction l2 as [| s t].
      - intros H. inversion H.
      - intros H. inversion H.
        + apply (lnapp s l1 t). apply H1.
        + apply IHt in H2. apply (lnapp s l1 t). apply H2.
    Qed.

    Theorem subseq_aa_ccl : forall T (a : T) (l1 l2 : list T),
        subseq (a :: l1 ) (a :: l2) -> subseq l1 l2.
    Proof.
      intros.
      inversion H.
      - apply H1.
      - apply subseq_a_ccl in H2. apply H2.
    Qed.

    Theorem subseq_ab_ccl: forall  T (a b : T) (l1 l2 : list T),
        subseq (a :: l1 ) (b :: l2) -> subseq l1 l2.
    Proof.
      intros T a b l1 l2 H.
      inversion H.
      - apply H1.
      - apply subseq_a_ccl in H2. apply H2.
    Qed.
    
    Theorem subseq_b_ccl : forall T ( a b : T) (l1 l2 : list T),
        a <> b /\ subseq (a :: l1 ) ( b :: l2) -> subseq (a :: l1 ) l2.
    Proof.
      intros T a b l1.
      induction l1 as [| s1 t1 H1].
      - intros l2 [H2 H3]. inversion H3.
        + rewrite H4 in H2. apply neq_relf in H2. inversion H2.
        + apply H1.
      - intros l2 [H2 H3]. inversion H3.
        + rewrite H5 in H2. apply neq_relf in H2. inversion H2.
        + apply H4.
    Qed.

    Theorem subseq_refl : forall  T (l : list T), subseq l l.
    Proof.
      intros T l.
      induction l as [| h t H'].
      - apply lnil.
      - apply (lapp h t t). apply H'.
    Qed.

    Theorem subseq_app : forall T  (l1 l2 l3 : list T),
        subseq l1 l2 -> subseq l1 (l2 ++ l3).
    Proof.
      intros  T l1 l2. generalize dependent l1.
      induction l2 as [| s2 t2 H2].
      - intros l1 l3 H. inversion H. apply lnil.
      - simpl. intros l1 l3 H. inversion H.
        + apply lnil.
        + apply (H2 n l3) in H3. apply (lapp s2 n (t2 ++ l3)) in H3. apply H3.
        + apply (H2 l1 l3) in H3. apply (lnapp s2 l1 (t2 ++ l3)) in H3. apply H3.
    Qed.

    Theorem subseq_trans : forall T  (l1 l2 l3 : list T),
        subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
    Proof.
      intros T l1 l2 l3. generalize dependent l2. generalize dependent l1.
      induction l3.
      - intros l1 l2 H1 H2. inversion H2. rewrite <- H in H1. inversion H1. apply lnil.
      - intros l1 l2 H1 H2. inversion H2.
        + rewrite <- H in H1. inversion H1. apply lnil.
        + inversion H1.
          * apply lnil.
          * rewrite <- H7 in H0. inversion H0.  rewrite H in H9. rewrite H9.
            apply lapp.  rewrite <- H6 in H1. rewrite <-H7 in H1.
            apply subseq_aa_ccl in H1. rewrite <- H7 in H2. rewrite H9 in H2.
            apply subseq_aa_ccl in H2. apply (IHl3 n0 m0). apply H5. apply H2.
          * rewrite <- H7 in H0. inversion H0. apply (lnapp x l1 l3).
            rewrite <- H7 in H2.
            apply (subseq_ab_ccl T x1 x m0 l3) in H2. apply (IHl3 l1 m0). apply H5. apply H2.
        + apply (lnapp x l1 l3). apply (IHl3 l1 l2). apply H1. apply H3.
    Qed.

    Inductive reg_exp {T: Type} : Type :=
    | EmptySet
    | EmptyStr
    | Char (t :T)
    | App (r1 r2  :reg_exp)
    | Union (r1 r2 : reg_exp)
    | Star (r : reg_exp).

    Inductive exp_match {T} : list T -> reg_exp -> Prop:=
    | MEmpty : exp_match [] EmptyStr
    | MChar  x : exp_match [x] (Char x)
    | MApp s1 re1 s2 re2
           (H1 : exp_match s1 re1)
           (H2 : exp_match s2 re2) :
        exp_match (s1 ++ s2) (App re1 re2)
    | MUnionL s1 re1 re2
              (H1 : exp_match s1 re1):
        exp_match s1 (Union re1 re2)
    | MUnionR re1 s2 re2
              (H2: exp_match s2 re2):
        exp_match s2 (Union re1 re2)
    | MStar0 re : exp_match [] (Star re)
    | MStar s1 s2 re
            (H1 : exp_match s1 re)
            (H2 : exp_match s2 (Star re)):
        exp_match (s1 ++ s2) (Star re).

    Notation " s =~ re " := (exp_match s re) (at level 80).

    Example reg_exp_ex1 : [1]  =~ Char 1.
    Proof.
      apply (MChar 1).
    Qed.

    Example reg_exp_ex2 : [1;2] =~ App (Char 1) (Char 2).
    Proof.
      apply (MApp [1] (Char 1) [2] (Char 2)).
      apply MChar. apply MChar.
    Qed.

    Example reg_exp_ex3 :~([1;2] =~ Char 1).
    Proof.
      unfold not. intros H. inversion H.
    Qed.

    Fixpoint reg_exp_of_list {T} (l : list T) :=
      match l with
      | [] => EmptyStr
      | x :: l' => App (Char x) (reg_exp_of_list l')
      end.

    Example reg_exp_ex4 : [1;2;3] =~ reg_exp_of_list [1;2;3].
    Proof.
      unfold reg_exp_of_list.
      apply (MApp [1]). apply MChar.
      apply (MApp [2]). apply MChar.
      apply (MApp [3]). apply MChar.
      apply MEmpty.
    Qed.

    Lemma MStar1 :
      forall T s (re : @reg_exp T),
        s =~ re -> s =~ Star re.
    Proof.
      intros T s re H.
      rewrite <- (app_nil_r T s).
      apply (MStar s [] re).
      apply H. apply MStar0.
    Qed.

    Lemma empty_is_empty : forall T (s : list T),
        ~(s =~ EmptySet).
    Proof.
      intros T s H. inversion H. Qed.

    Lemma MUnion' : forall T (s : list T) (re1 re2 :@reg_exp T),
        s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
    Proof.
      intros T s re1 re2 [H | H].
      -  apply (MUnionL s re1 re2). apply H.
      -  apply (MUnionR re1 s re2). apply H.
    Qed.

    Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
        (forall s, In s ss -> s =~ re) ->
        fold app ss [ ] =~ Star re.
    Proof.
      intros T ss re H.
      induction ss as [| ss st H1].
      - simpl. apply MStar0.
      - simpl. assert(tmpH: In ss (ss :: st)). simpl. left. reflexivity.
        apply H in tmpH. apply (MStar ss (fold app st [ ]) re).
        + apply tmpH.
        + apply H1. intros s H'. assert(tmpH2: In s (ss :: st)). simpl. right. apply H'.
          apply H in tmpH2. apply tmpH2.
    Qed.

    Theorem reg_exp_of_list_refl : forall T (s1 : list T),
        s1 =~ reg_exp_of_list s1.
    Proof.
      intros T s1.
      induction s1.
      - simpl. apply MEmpty.
      - simpl. apply (MApp [x]). apply MChar. apply IHs1.
    Qed.

    Theorem nil_app_nil : forall T (l1 l2 :list T),
        l1 ++ l2 = [ ] -> l1 = [ ]/\ l2 =[].
    Proof.
      intros T [| s1 t1] [| s2 t2] H.
      - split. reflexivity. reflexivity.
      - split. reflexivity. simpl in H. inversion H.
      - split. rewrite(app_nil_r T (s1 ::t1 )) in H. inversion H. reflexivity.
      - simpl in H. inversion H.
    Qed.

    Theorem reg_exp_of_list_nil: forall T (l1 : list T),
        [] =~ reg_exp_of_list l1 -> l1 = [].
    Proof.
      intros T l1.
      induction l1.
      - intros H. reflexivity.
      - simpl. intros H. inversion H.
        + apply nil_app_nil in H1. destruct H1 as [H11 H12]. rewrite H11 in H3. inversion H3.
    Qed.
          
    Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
        s1 =~ reg_exp_of_list s2 <-> s1 = s2.
    Proof.
      symmetry.
      split.
      - intros H. rewrite H. apply reg_exp_of_list_refl.
      - intros H. generalize dependent s1. induction s2.
        + simpl. intros s1 H. inversion H. reflexivity.
        + simpl. intros [| s1 t1] H.
          * inversion H. apply nil_app_nil in H1. destruct H1 as [H11 H12]. rewrite H11 in H3. inversion H3.
          * inversion H. inversion H3. simpl. apply IHs2 in H4. rewrite H4. reflexivity.
    Qed.

    Fixpoint re_chars {T} (re :reg_exp)  : list T :=
      match re with
      | EmptySet => []
      | EmptyStr => []
      | Char x => [x]
      | App re1 re2 => re_chars re1 ++ re_chars re2
      | Union re1 re2 => re_chars re1 ++ re_chars re2
      | Star re => re_chars re
      end.

    Theorem in_re_match : forall T (s : list T) (re :reg_exp) (x :T),
        s =~ re -> In x s -> In x (re_chars re).
    Proof.
      intros T s re x Hmatch Hin.
      induction Hmatch as
          [| x'
           | s1 re1 s2 re22 Hmatch1 IH1 Hmatch2 IH2
           | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
           | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
      - simpl in Hin. apply Hin.
      - apply Hin.
      - simpl. rewrite In_app_iff. rewrite In_app_iff in Hin. destruct Hin as [H|H]. apply IH1 in H. left. apply H. apply IH2 in H. right. apply H.
      - simpl. rewrite In_app_iff. apply IH in Hin. left. apply Hin.
      - simpl. rewrite In_app_iff. apply IH in Hin. right. apply Hin.
      - simpl. inversion Hin.
      - simpl. apply In_app_iff in Hin. destruct Hin as [H|H].
        + apply IH1 in H. apply H.
        + apply IH2 in H. apply H.
    Qed.

    Fixpoint re_not_empty {T:Type} (re :@reg_exp T) : bool :=
      match re with
      | EmptySet => false
      | EmptyStr => true
      | Char t => true
      | App re1 re2 => re_not_empty re1 && re_not_empty re2
      | Union re1 re2 => re_not_empty re1 || re_not_empty re2
      | Star r => true 
      end.

    Lemma re_not_empty_correct : forall T (re: @reg_exp T),
        (exists s, s =~ re) <-> re_not_empty re = true.
    Proof.
      intros T re.
      split.
      - intros [s H].
        induction H.
        + reflexivity.
        + reflexivity.
        + simpl. rewrite IHexp_match1. apply IHexp_match2.
        + simpl. rewrite IHexp_match. reflexivity.
        + simpl. rewrite IHexp_match. apply Bool.orb_true_r.
        + reflexivity.
        + reflexivity.
      - intros H. induction re.
        + inversion H.
        + exists []. apply MEmpty.
        + exists [t]. apply MChar.
        + simpl in H.
          assert(tmpH1: exists s: list T, s =~ re1). rewrite Bool.andb_comm in H. apply andb_true_elim2 in H. apply (IHre1 H).
          assert(tmpH2: exists s: list T, s =~ re2). apply andb_true_elim2 in H. apply (IHre2 H).
          destruct tmpH1 as [ s1 HH1]. destruct tmpH2 as [s2 HH2].
          exists (s1 ++ s2). apply MApp. apply HH1. apply HH2.
        + simpl in H. destruct (re_not_empty re1) eqn:E1.
          * simpl in H. apply IHre1 in H. destruct H as [s1 H1]. exists s1. apply MUnionL. apply H1.
          * destruct (re_not_empty re2) eqn:E2. simpl in H. apply IHre2 in H. destruct H as [s2 H2]. exists s2. apply MUnionR. apply H2. inversion H.
        + exists []. apply MStar0.
    Qed.

    Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
        s1 =~ Star re -> s2 =~  Star re -> s1 ++ s2 =~ Star re.
    Proof.
      intros T s1 s2 re H1.
      remember (Star re) as re'.
      generalize dependent s2.
      induction H1.
      - intros s2 H. simpl. apply H.
      - simpl. inversion Heqre'.
      - inversion Heqre'.
      - inversion Heqre'.
      - inversion Heqre'.
      - simpl. intros s2 H. congruence.
      - inversion Heqre'. intros s2' H1'. rewrite <- app_assoc. apply MStar.
        rewrite <- H0. apply H1_.
        rewrite <- H0. apply IHexp_match2. apply Heqre'. rewrite H0. apply H1'.
    Qed.

    Lemma MStar'' : forall T (s : list T) (re :reg_exp),
        s =~ Star re ->
        exists ss : list (list T),
          s = fold app ss []
          /\ forall s', In s' ss -> s' =~ re.
    Proof.
      intros T s re H.
      remember (Star re) as re'.
      induction H.
      - exists []. simpl. split. reflexivity. intros s' H. inversion H.
      - inversion Heqre'.
      - inversion Heqre'.
      - inversion Heqre'.
      - inversion Heqre'.
      - exists []. simpl. split. reflexivity. intros s' H. inversion H.
      - simpl. inversion Heqre'. apply IHexp_match2 in Heqre'.  destruct Heqre' as [ss [HL HR]].
        exists (s1 :: ss). split.
        + simpl. rewrite <- HL. reflexivity.
        + simpl. intros s' [H1|H1].
          * rewrite <- H1. rewrite <- H2. apply H.
          * apply (HR s' H1).
    Qed.

    Module Pumping.

      Fixpoint pumping_constant {T} (re : @reg_exp T): nat :=
        match re with
        | EmptySet => 0
        | EmptyStr => 1
        | Char _ => 2
        | App re1 re2 => pumping_constant re1 + pumping_constant re2
        | Union re1 re2 => pumping_constant re1 + pumping_constant re2
        | Star _ =>1
        end.

      Fixpoint napp {T} (n :nat) (l :list T) : list T :=
        match n with
        | 0 => []
        | S n' => l ++ napp n' l
        end.

      Lemma napp_plus : forall T (n m :nat) (l : list T),
          napp (n + m) l = napp n l ++ napp m l.
      Proof.
        intros T n m l.
        induction n.
        - reflexivity.
        - simpl. rewrite IHn. rewrite app_assoc. reflexivity.
      Qed.

      Import Coq.omega.Omega.

      Theorem lt_add: forall a b c d , a + b <= c + d -> a <=c \/ b <= d.
      Proof.
        intros a b c d. omega.
      Qed.

      Theorem lt_ccl: forall a b c,  a + b <= c ->a<=c.
      Proof.
        intros a b c. omega.
      Qed.
      Theorem lt_one_split_right: forall a b, 1 <= a + b -> 1 <=a \/  1 <=b.
      Proof.
        intros a b. omega.
      Qed.
        
      Theorem app_assoc_4 : forall T (l1 l2 l3 l4 : list T),
          (l1 ++ l2 ++ l3) ++ l4 = l1 ++ l2 ++ l3 ++ l4.
      Proof.
        intros T l1 l2 l3 l4. induction l1.
        - simpl. rewrite app_assoc. reflexivity.
        - simpl. rewrite IHl1. reflexivity.
      Qed.


      Lemma pumping : forall T (re: @reg_exp T) s,
          s =~ re ->
          pumping_constant re <= length s ->
          exists s1 s2 s3,
            s = s1 ++ s2 ++ s3 /\ s2 <> []  /\
            forall m, s1 ++ napp m s2 ++ s3 =~ re.
      Proof.
        intros T re s Hmatch.
        induction Hmatch as [| x| s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
                             | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
                             | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
        - simpl. omega.
        - simpl. omega.
        - simpl. intros H.  rewrite app_length in H. apply lt_add in H. destruct H as [H|H].
          + apply IH1 in H. destruct H as [ss [sm [st [H1 [H2 H3]]]]].
             exists ss, sm, (st ++ s2). split. rewrite H1. apply app_assoc_4. split. apply H2.
             intros m. rewrite <- app_assoc_4. apply (MApp (ss ++ napp m sm ++ st) re1 s2 re2). apply H3. apply Hmatch2.
          + apply IH2 in H. destruct H as [ss [sm [st [H1 [H2 H3]]]]].
            exists (s1 ++ ss), sm, st. split. rewrite H1. rewrite app_assoc. reflexivity. split. apply H2.
            intros m. rewrite <- app_assoc. apply (MApp s1 re1). apply Hmatch1. apply H3. 
        - simpl. intros H.  apply lt_ccl in H.
          apply IH in H. destruct H as [ss [sm [st [H1 [H2 H3]]]]]. exists ss,sm,st.
          split. apply H1. split. apply H2.
          intros m. apply MUnionL. apply H3.
        - simpl. intros H. rewrite plus_comm in H. apply lt_ccl in H.
          apply IH in H. destruct H as [ss [sm [st [H1 [H2 H3]]]]]. exists ss,sm,st.
          split. apply H1. split. apply H2.
          intros m. apply MUnionR. apply H3.
        - simpl. omega.
        - simpl. simpl in IH2. intros H.  rewrite  app_length in H. apply lt_one_split_right in H. destruct H as [H|H].
          exists [], s1 ,s2. split. reflexivity. split. destruct s1 as [| ss st]. simpl in H. inversion H.
          unfold not. intros HH. inversion HH.
          intros m. simpl. induction m.
          + simpl. apply Hmatch2.
          + simpl. rewrite <- app_assoc. apply (MStar s1  (napp m s1 ++ s2) re). apply Hmatch1. apply IHm.
          + simpl. apply IH2 in H. destruct H as [ss [sm [st [H1 [H2 H3]]]]].
            exists (s1 ++ ss), sm ,st. split. rewrite H1. rewrite app_assoc. reflexivity.
            split. apply H2. intros m. rewrite <- app_assoc. apply (MStar s1 (ss ++ napp m sm ++ st)). apply Hmatch1. apply H3.
      Qed.
      End Pumping.

      Theorem filter_not_empty_In : forall n l,
          filter (fun x => beq_nat n x) l <> [] -> In n l.
      Proof.
        intros n l H.
        induction l as [| s t H'].
        - simpl in H. simpl. apply H. reflexivity.
        - destruct (beq_nat s n) eqn:E.
          + left. rewrite beq_nat_true_iff in E. apply E.
          + simpl. right. simpl in H. apply H'. rewrite (beq_nat_sym s n) in E. rewrite E in H. apply H.
      Qed.

      Inductive reflect (P:Prop) : bool -> Prop :=
      | ReflectT (H:P) : reflect P true
      | ReflectF (H: ~P) : reflect P false.

      Theorem iff_reflect : forall P b, (P <-> b = true)  -> reflect P b.
      Proof.
        intros P b H. destruct b.
        - apply ReflectT. apply H. reflexivity.
        - apply ReflectF. rewrite H. intros H1. inversion H1.
      Qed.

      Theorem reflect_iff :forall P b, reflect P b -> (P <-> b = true).
      Proof.
        intros P b H. destruct b.
        - inversion H. split.
          + intros H1. reflexivity.
          + intros H1. apply H0.
        - inversion H. split.
          + intros H1. unfold not in H0. apply H0 in H1. inversion H1.
          + intros H1. discriminate.
      Qed.

      Lemma eqbP : forall n m, reflect (n = m) (beq_nat n m).
      Proof.
        intros n m. apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
      Qed.

      Theorem filter_not_empty_In' : forall n l,
          filter (fun x => beq_nat n x) l <> [] -> In n l.
      Proof.
        intros n l. induction l as [| s t H].
        - simpl. intros H. apply H. reflexivity.
        - simpl. destruct (eqbP n s) as [H1 | H1].
          + intros . left.  rewrite H1. reflexivity.
          + right. apply H,H0.
      Qed.

      Fixpoint count n l :=
        match l with
        | [] => 0
        | m :: l' => (if (beq_nat n m) then 1 else 0) + count n l'
        end.

      Theorem eqbP_practice : forall n l,
          count n l = 0 -> ~(In n l).
      Proof.
        intros n l H.
        induction l as [| s t H1].
        - simpl. intros H2. apply H2.
        - destruct (eqbP n s).
          + simpl in H. rewrite <- beq_nat_true_iff in H0. rewrite H0 in H. inversion H.
          + simpl. intros H2. destruct H2 as [H2|H2].
            * rewrite H2 in H0. apply neq_relf in H0. inversion H0.
            * simpl in H. rewrite <- nat_bat_neq in H0. rewrite H0 in H. simpl in H. apply H1 in H. unfold not in H. apply H in H2. inversion H2.
      Qed.

      Inductive nostutter {X:Type} : list X -> Prop:=
      | nosnil : nostutter []
      | nosapp x l (H: l = [] \/ exists s t, nostutter l /\ l = s ::t /\ s <>x) : nostutter (x :: l).

      Example test_nostutter_1 :nostutter [3;1;4;1;5;6].
      Proof.
        apply (nosapp 3). right.
        exists 1, [4;1;5;6]. split.
        - apply (nosapp 1). right.
          exists 4,[1;5;6]. split.
          + apply (nosapp 4). right.
            * exists 1,[5;6]. split.
              apply (nosapp 1). right.
              exists 5,[6]. split.
              apply (nosapp 5). right.
              exists 6,[]. split.
              apply (nosapp 6). left. reflexivity.
              split. reflexivity. congruence.
              split. reflexivity. congruence.
              split. reflexivity. congruence.
          + split. reflexivity. congruence.
        - split. reflexivity. congruence.
      Qed.

      Example test_nostutter_2 : nostutter (@nil nat).
      Proof.
        apply nosnil.
      Qed.

      Example test_nostutter_3 : nostutter [5].
      Proof.
        apply (nosapp 5). left. reflexivity.
      Qed.

      Example test_nostutter_4: not (nostutter [3;1;1;4]).
      Proof.
        intros H. inversion H.
        destruct H1 as [H1 | H1].
        - discriminate.
        - simpl. destruct H1 as [s1 [t1 [H11 [H12 H13]]]].
          + inversion H11.
            destruct H3 as [H3 | H3]. discriminate.
            destruct H3 as [s3 [t3 [H31 [H32 H33]]]].
            inversion H32. rewrite H5 in H33. apply neq_relf in H33. apply H33.
      Qed.

      Inductive in_order_merge {T:Type} : list T -> list T -> list T -> Prop := 
      | mnil : in_order_merge [] [] []
      | mapp1 x  l l1 l2 (H: in_order_merge l l1 l2) : in_order_merge (x :: l) (x :: l1) l2
      | mapp2 x l l1 l2 (H: in_order_merge l l1 l2): in_order_merge ( x :: l) l1 (x :: l2).

      Example in_order_merge_test : in_order_merge [1;4;6;2;3] [1;6;2] [4;3].
      Proof.
        apply (mapp1 1).
        apply (mapp2 4).
        apply (mapp1 6).
        apply (mapp1 2).
        apply (mapp2 3).
        apply mnil. 
      Qed.
      
      Theorem in_order_merge_in1: forall T (x :T) (l l1 l2 : list T),
          in_order_merge l l1 l2 -> In x l1 -> In x l.
      Proof.
        intros T x l l1 l2 H H1.
        induction H.
        - inversion H1.
        - destruct H1 as[H1 | H1].
          + left. apply H1.
          + right. apply (IHin_order_merge H1).
        - right. apply (IHin_order_merge H1).
      Qed.

      Theorem in_order_merge_in2 : forall T (x :T) (l l1 l2 :list T),
          in_order_merge l l1 l2 -> In x l2 -> In x l.
      Proof.
        intros T x l l1 l2 H H1.
        induction H.
        - inversion H1.
        - right. apply (IHin_order_merge H1).
        - destruct H1 as [H1 | H1].
          + left. apply H1.
          + right. apply (IHin_order_merge H1).
      Qed.
      

      Theorem filter_challenge : forall T (test: T -> bool) (l l1 l2 : list T) ,
          in_order_merge l l1 l2 /\
          (forall x : T,  In x l1 -> test x = true)  /\
          (forall x :T ,  In x l2 -> test x = false) -> filter test l = l1.
      Proof.
        intros T test l l1 l2 [H [H1 H2]].
        induction H.
        - reflexivity.
        - assert(tmpH: In x (x :: l1)). left. reflexivity.
          apply H1 in tmpH. simpl.
          rewrite tmpH.
          assert(tmpH1: filter test l = l1). {
            apply IHin_order_merge.
            intros x0 H3. apply H1. right. apply H3.
            apply H2.
            }
          rewrite tmpH1. reflexivity.
            - simpl.
              assert(tmpH: In x (x :: l2)). left. reflexivity.
              apply H2 in tmpH. rewrite tmpH.
              apply IHin_order_merge. apply H1.
              intros x0 H3.
              apply H2. right. apply H3.
            Qed.

      Theorem test_true: forall T (test: T -> bool) (l: list T),
          (forall x :T , In x l -> test x =true) -> (filter test l) = l.
      Proof.
        intros T test l H.
        induction l.
        - reflexivity.
        - assert(tmpH: In x (x :: l)). left. reflexivity.
          apply H in tmpH. simpl.
          rewrite tmpH.
          assert(tmpH1: filter test l = l). {
            apply IHl.
            intros x0 H1. apply H.
            right. apply H1.
          }
          rewrite tmpH1. reflexivity.
      Qed.

      Theorem subseq_in : forall T (l1 l2 : list T) (x :T),
          subseq l1 l2 -> In x l1 -> In x l2.
      Proof.
        intros T l1 l2 x H H1.
        induction H.
        - inversion H1.
        - destruct H1 as [H1 | H1].
          + left. apply H1.
          + apply IHsubseq in H1. right. apply H1.
        - apply IHsubseq in H1. right. apply H1.
      Qed.

      Theorem filter_challenge2 : forall T (test: T-> bool) (l1 l :list T) ,
          subseq l1 l
          -> (forall x: T, In x l -> test x = true)
          -> (length (filter test l1)) <= (length (filter test l)).
      Proof.
        intros T test l1 l H H1.
        assert(tmpHl: filter test l = l). apply (test_true T test l). apply H1.
        assert(tmpHl1: filter test l1 = l1). apply (test_true T test l1). intros x H2. apply H1. apply (subseq_in T l1 l). apply H. apply H2.
        rewrite tmpHl. rewrite tmpHl1.
        induction H.
        - simpl. apply O_le_n.
        - simpl.
          assert(tmpH: length n <=length m). {
            assert(tmpH1: In x (x :: m)). left. reflexivity.
            apply H1 in tmpH1. simpl in tmpHl. rewrite tmpH1 in tmpHl. inversion tmpHl.
            rewrite H2.
            simpl in tmpHl1. rewrite tmpH1 in tmpHl1. inversion tmpHl1. rewrite H3.
            apply IHsubseq. intros x0 HH. apply H1.
            right. apply HH.
            apply H2. apply H3.
          }
          apply n_le_m_Sn_le_Sm. apply tmpH.
        - simpl. apply le_S.
          assert(tmpH1 : In x (x :: m)). left. reflexivity.
          apply H1 in tmpH1. simpl in tmpHl. rewrite tmpH1 in tmpHl. inversion tmpHl.
          rewrite H2. apply IHsubseq.
          intros x0 HH. apply H1. right. apply HH. apply H2. apply tmpHl1.
      Qed.

      Inductive pal {T}:  list T -> Prop:=
      | palnil : pal nil
      | palChar x : pal [x]
      | palApp x l (H: pal l): pal ([x] ++ l ++ [x]).

      Theorem pal_app_rev: forall (T:Type) (l: list T),
          pal (l ++ rev l).
      Proof.
        intros T l.
        induction l as [| s t H].
        - simpl. apply palnil.
        - simpl. assert(tmpH: s :: t ++ rev t ++ [s] = [s] ++ (t ++ rev t) ++ [s]). simpl. rewrite app_assoc. reflexivity.
          rewrite tmpH. apply palApp. apply H.
      Qed.

      Theorem pal_rev: forall (T: Type) (l :list T),
          pal l -> l = rev l.
        intros T l H.
        induction H.
        - reflexivity.
        - reflexivity.
        - simpl. rewrite rev_app_distr. simpl.  rewrite <- IHpal. reflexivity.
      Qed.
      
      Theorem l_eq_revl_split : forall  (T:Type) (l: list T),
          l = rev l -> exists s t, l = s ++ t ++ s.
      Proof.
        intros T l H1.
        induction l as [| ls lt H].
        - exists [],[]. reflexivity.
        - simpl.  destruct (rev lt) as [| rs rt] eqn:E.
          + assert(tmpH: lt =[]). rewrite <- (rev_involutive T lt). rewrite E. reflexivity.
            rewrite tmpH. exists [],[ls]. reflexivity.
          + simpl in H1. rewrite E in H1. inversion H1. exists [rs], rt. reflexivity.
      Qed.

      Theorem nat_ind2 :
        forall (P : nat -> Prop),  P 0 -> P 1 ->
                                   (forall n : nat,  P n -> P (S (S n))) -> forall n :nat, P n.
      Proof.
        intros p H H0 H1.
        induction n;auto.
        assert (p n/\p (S n));try tauto.
        clear IHn. induction n;auto.
        destruct IHn.
        split;auto.
      Qed.

      Lemma length_zero_iff_nil : forall {T} (l: list T),
          length l = 0 <-> l = [].
      Proof.
        intros T l.
        split.
        - intros H.
          induction l as [| s t H1].
          + reflexivity.
          + simpl in H. inversion H.
        - intros H. rewrite H. reflexivity.
      Qed.
      

      Lemma list_ind2 : forall {A} (P: list  A -> Prop) (P_nil : P [])
                               (P_single : forall x, P [x])
                               (P_cons_snoc : forall x l x',  P l -> P ([x] ++ l ++ [x'])),
          forall l, P l.
      Proof.
        intros. remember (length l) as n. symmetry in Heqn. revert dependent l.
        induction n using nat_ind2; intros.
        - apply length_zero_iff_nil in Heqn. subst l. apply P_nil.
        - destruct l; [discriminate|]. simpl in Heqn. inversion Heqn; subst.
          apply length_zero_iff_nil in H0. subst l. apply P_single.
        - destruct l; [discriminate|]. simpl in Heqn.
          inversion Heqn; subst. pose proof (rev_involutive A l) as Hinv.
          destruct (rev l). destruct l; discriminate. simpl in Hinv. subst l.
          rewrite app_length in H0.
          rewrite PeanoNat.Nat.add_comm in H0. simpl in H0. inversion H0.
          apply P_cons_snoc. apply IHn. assumption.
      Qed.

      Theorem l1_eq_l2_to_revl1_eq_revl2: forall {T}  (l1 l2 :list T),
          l1 = l2 -> rev l1 = rev l2.
      Proof.
        intros. rewrite H. reflexivity.
      Qed.
      
      Theorem palindrome_converse : forall (T: Type) (l: list T),
          l = rev l -> pal l.
      Proof.
        intros T l H.
        induction l using list_ind2.
        - apply palnil.
        - apply palChar.
        - simpl in H. rewrite rev_app_distr in H. simpl in H.  inversion H.
          apply palApp. apply IHl.
          apply l1_eq_l2_to_revl1_eq_revl2 in H2. rewrite rev_app_distr in H2.
          rewrite rev_app_distr in H2. simpl in H2. inversion H2.
          rewrite  rev_involutive in H3. symmetry. apply H3.
      Qed.

      Definition disjoint {T} (l1 l2 : list T) : Prop :=
        forall x :T, (In x l1 -> ~(In x l2)) /\ (In x l2 -> ~(In x l1)).

      Inductive NoDup {T} : list T -> Prop:=
      | NoDupnil: NoDup []
      | NoDupApp x l (H: NoDup l) (H1: ~(In x l)): NoDup (x :: l).

      Theorem disjoint_bccl: forall {T} (l1 l2 :list T) (x :T),
          disjoint l1 (x :: l2) -> disjoint l1 l2.
      Proof.
        intros T l1 l2 x. unfold disjoint.
        intros H. intros x0. pose proof (H x0) as H2. destruct H2 as [H21 H22]. split.
        - intros H1. 
          apply H21 in H1. unfold not in H1. simpl in H1. unfold not. intros H3. apply H1. right. apply H3.
        - intros H1.  apply H22. simpl. right. apply H1.
      Qed.

      Theorem disjoint_accl : forall {T} (l1 l2 :list T) (x :T),
          disjoint (x :: l1 ) l2 -> disjoint l1 l2.
      Proof.
        intros T l1 l2 x. unfold disjoint.
        intros H x0. pose proof (H x0) as H1.
        split.
        - intros H2. destruct H1 as [H11 H12]. apply H11. right. apply H2.
        - destruct H1 as [H11 H12]. intros H3. apply H12 in H3.  simpl in H3.
          unfold not in H3. unfold not. intros H4. apply H3. right. apply H4.
      Qed.
      
      Theorem deMorgan: forall P Q :Prop,
          ~(P\/Q) -> ~P /\ ~Q.
      Proof.
        unfold not.
        intros P Q H.
        split.
        - intros H1. apply H. left. apply H1.
        - intros H1. apply H. right. congruence.
      Qed.
            

      Theorem disjoint_aadd : forall {T} (l1 l2 :list T) (x :T),
          ~In x (l1 ++ l2) -> disjoint l1 l2 -> disjoint (x :: l1 ) l2.
      Proof.
        intros T l1 l2 x H1. unfold disjoint.
        intros H. intros x0. pose proof (H x0) as IH. destruct IH as [H11 H12].
        split.
        - simpl. intros [HH|HH].
          + rewrite In_app_iff in H1. apply deMorgan in H1. destruct H1 as [HH1 HH2].
            rewrite <- HH. apply HH2.
          + apply H11. apply HH.
        - intros HH. simpl. unfold not.  intros [IH|IH].
          + rewrite In_app_iff in H1. apply deMorgan in H1. destruct H1 as [HH1 HH2].
            unfold not in HH2. apply HH2. rewrite IH. apply HH.
          + apply H11 in IH. unfold not in IH. apply IH. apply HH.
      Qed.

      Theorem  disjoint_and_NoDup : forall {T} (l l1 l2 :list T),
          l = l1 ++ l2 -> NoDup l -> disjoint l1 l2.
      Proof.
        intros T l l1 l2 H1 H2. generalize  dependent l2. generalize dependent l1.
        induction H2.
        - intros l1 l2 H. symmetry in H. apply nil_app_nil in H. destruct H as [H11 H12].
          subst l1. subst l2. unfold disjoint. intros x. split.
          intros []. intros [].
        - intros l1 l2. intros H.
          destruct l1 as [| s1 t1].
          + simpl in H. rewrite <- H. unfold disjoint. intros x0. split. intros []. intros tmpH [].
          + inversion H. apply disjoint_aadd. rewrite <- H4. rewrite <- H3. apply H1.
            apply( IHNoDup t1 l2). apply H4.
      Qed.

      Lemma in_split : forall (X:Type) (x:X) (l:list X),
          In x l -> exists l1 l2,  l = l1 ++ x  :: l2.
      Proof.
        intros X x l H.
        induction l as [| s t  Hl].
        - inversion H.
        - simpl in H. destruct H as [H|H].
          + rewrite H. exists [], t. reflexivity.
          + apply Hl in H. destruct H as [l1 [l2 H]].
            exists (s :: l1),l2. simpl. rewrite <- H. reflexivity.
      Qed.

      Inductive repeats {X:Type} : list X ->  Prop:=
      | rAppr x l (H: In x l) : repeats (x :: l)
      | rAppnr x l (H: repeats l): repeats (x :: l).

      Theorem app_length_S1: forall {T} (l l1 l2 : list T) (x :T),
          l = l1 ++ x :: l2 -> length l = S ( length (l1 ++ l2)).
      Proof.
        intros T l.
        induction l as [| s t H].
        - intros l1 l2 x H. remember (x :: l2 ) as l3.
          symmetry in H. apply nil_app_nil in H. destruct H as [H1 H2].
          rewrite Heql3 in H2. inversion H2.
        - intros l1 l2 x H1. simpl.
          destruct l1 as [| sl1 tl1].
          + simpl in H1. inversion H1. simpl. reflexivity.
          + simpl in H1. inversion H1. simpl.
            pose proof (H tl1 l2 x) as IH. apply IH in H3 as IH1. rewrite H3 in IH1.
            rewrite IH1. reflexivity.
      Qed.

      Theorem pigeonhole_principle : forall (X:Type) (l1 l2 : list X),
          excluded_middle ->
          (forall x, In x l1 -> In x l2) ->
          length l2 < length l1 ->
          repeats l1.
      Proof.
        intros X l1.
        induction l1 as [| x l1' IHl1'].
        - intros. inversion H1.
        - intros l2. intros em H Len.
          pose proof (em (In x l1')) as He.
          destruct He as [He |He].
          + apply rAppr. apply He.
          + assert(tmpH: forall x0, In x0 l1' -> In x0 l2). intros x0 HH. apply H. simpl. right. apply HH.
            assert(tmpH1:  In x l2). apply (H x). simpl. left. reflexivity.
            apply in_split in tmpH1.  destruct tmpH1 as [ls [lt Hl2]].
            pose proof (app_length_S1 l2 ls lt x)  as IH1. 
            apply IH1 in Hl2 as IH2.
            apply rAppnr. apply (IHl1' (ls ++ lt)). apply em.
            * intros x0 IIIH. 
              apply tmpH in IIIH as IIIH2. rewrite Hl2 in IIIH2. rewrite In_app_iff in IIIH2. 
              assert(tmpH3: x :: lt = [x] ++ lt). reflexivity.
              rewrite tmpH3 in IIIH2. rewrite In_app_iff in IIIH2.
              rewrite In_app_iff.
              destruct IIIH2 as [IIIH2 |[IIIH2| IIIH2]].
              left.  apply IIIH2.  simpl in IIIH2. destruct IIIH2 as [IIIH2 | IIIH2].
              rewrite IIIH2 in He. unfold not in He. exfalso. apply He. apply IIIH.
              inversion IIIH2.
              right. apply IIIH2.
            * rewrite IH2 in Len. simpl in Len. 
              apply Lt.lt_S_n in Len. apply Len.
      Qed.


      Require Export Coq.Strings.Ascii.
      Definition string := list ascii.

      Lemma provable_equiv_true : forall (P: Prop), P -> (P <-> True).
      Proof.
        intros. split.
        - intros. apply I.
        - intros. apply H.
      Qed.

      Lemma not_equiv_false : forall (P: Prop), ~P -> (P <-> False).
      Proof.
        intros. split.
        - apply H.
        - intros [].
      Qed.

      Lemma null_matches_none : forall (s :string), (s =~EmptySet) <-> False.
      Proof.
        intros.
        apply not_equiv_false.
        unfold not.  intros. inversion H.
      Qed.

      Lemma empty_matches_eps : forall (s :string) , s =~ EmptyStr <-> s = [].
      Proof.
        split.
        - intros. inversion H. reflexivity.
        - intros. rewrite H. apply MEmpty.
      Qed.

      Lemma empty_nomatch_ne : forall (a : ascii) s, ( a :: s =~EmptyStr) <-> False.
      Proof.
        intros.
        apply not_equiv_false.
        unfold not. intros H. inversion H.
      Qed.

      Lemma char_nomatch_char:
        forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
      Proof.
        intros.
        apply not_equiv_false.
        unfold not.  intros H0.
        inversion H0. rewrite H4 in H. apply neq_relf in H.
        inversion H.
      Qed.
      
      Lemma char_eps_suffix : forall (a: ascii) s, a :: s =~ Char a <-> s = [].
      Proof.
        split.
        - intros. inversion H. reflexivity.
        - intros. rewrite H. apply MChar.
      Qed.

      Lemma app_exists : forall (s : string) re0 re1,
          s =~ App re0 re1 <->
          exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
      Proof.
        intros.
        split.
        - intros. inversion H. exists s1, s2. split.
          reflexivity.
          split. apply H3. apply H4.
        - intros [s0 [s1 [Happ [Hmat0 Hmat1]]]].
          rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
      Qed.

      Lemma app_ne : forall (a :ascii) s re0 re1,
          a :: s =~ (App re0 re1) <->
          ([] =~ re0 /\  a :: s =~ re1) \/
          exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
      Proof.
        intros a s re0 re1. split.
        - intros H. inversion H.
          subst re2. subst re3. destruct s1 as [| ss1 st1].
          + simpl in H1. left. split. apply H3. simpl. apply H4.
          + right. inversion H1. subst ss1. exists st1, s2.
            split. reflexivity. split. apply H3. apply H4.
        - intros [H|H].
           destruct H as [H1 H2].
          + apply (MApp []  _ (a :: s)). apply H1. apply H2.
          + destruct H as [s0 [s1 H]]. destruct H as [H1 [H2 H3]].
            rewrite H1. apply (MApp (a :: s0) _ s1). apply H2. apply H3.
      Qed.

      Lemma union_disj : forall (s :string) re0 re1,
          s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
      Proof.
        intros. split.
        - intros. inversion H.
          + left. apply H2.
          + right. apply H1.
        - intros [H|H].
          + apply MUnionL. congruence.
          + apply MUnionR. congruence.
      Qed.

      Theorem star_ne : forall (a : ascii) s re,
          a :: s =~ Star re <->
          exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
      Proof.
        symmetry.
        split.
        - intros H. destruct H as [s0 [s1 [H1 [H2 H3]]]].
          subst s. apply (MStar (a::s0) s1). apply H2. apply H3.
        - intros H. remember (a :: s) as l.  remember (Star re) as re'. induction H.
          + inversion Heql.
          + inversion Heqre'.
          + inversion Heqre'.
          + inversion Heqre'.
          + inversion Heqre'.
          + inversion Heql.
          + destruct s1 as [| ss1 st1] eqn:E.
            * simpl in Heql. apply IHexp_match2. apply Heql. apply Heqre'.
            * simpl in Heql. inversion Heql. subst ss1. exists st1, s2.
              split. reflexivity. split. inversion Heqre'. subst re0. apply H. apply H0.
      Qed.

      Definition refl_match_eps m :=
        forall re: @reg_exp ascii, reflect ([] =~ re) (m re).
      
      Fixpoint match_eps (re: @reg_exp ascii) : bool :=
        match re with
        | EmptySet => false
        | EmptyStr => true
        | Union re1 re2 => (match_eps re1) || (match_eps re2)
        | App re1 re2 => (match_eps re1) && (match_eps re2)
        | Char _ => false
        | Star _ => true
        end.

      Lemma match_eps_refl : refl_match_eps match_eps.
      Proof.
        unfold refl_match_eps. intros re.
        destruct (match_eps re)as [] eqn:E.
        - apply ReflectT. induction re.
          + inversion E.
          + apply MEmpty.
          + inversion E.
          + simpl in E.  apply andb_prop in E. destruct E as [E1 E2]. apply (MApp [] _ [] _).  apply (IHre1 E1). apply (IHre2 E2).
          +  simpl in E. apply orb_true_iff in E. destruct E. apply MUnionL. apply (IHre1 H). apply MUnionR. apply (IHre2 H).
          + apply MStar0.
        - apply ReflectF. induction re.
          + unfold not. intros H. inversion H.
          + simpl in E. inversion E.
          + unfold not. intros H. inversion H.
          + unfold not. intros H. inversion H. subst re0. subst re3. apply nil_app_nil in H1. destruct H1 as [H11 H12]. subst s1. subst s2. simpl in E. apply Bool.andb_false_iff in E. destruct E as [E|E]. apply IHre1 in E. unfold not in E. apply (E H3). apply IHre2 in E. unfold not in E. apply (E H4).
          + simpl in E. apply Bool.orb_false_iff in E. destruct E as [E1 E2]. unfold not. intros H. inversion H. subst re0 re3. unfold not in IHre1. apply IHre1. apply E1. apply H2. subst re0 re3. unfold not in IHre2. apply IHre2. apply E2. apply H1.
          + simpl in E. inversion E.
      Qed.

      Definition is_der re (a : ascii ) re' :=
        forall s,  a :: s =~ re <-> s =~ re'.

      Definition derives d := forall a re, is_der re a (d a re).

      Example a1 : [1;2;3] =~ App EmptyStr (App (Char 1) (App (Char 2) (Char 3))).
      Proof.
        apply (MApp [] _ [1;2;3]). apply MEmpty.
        apply (MApp [1]). apply MChar.
        apply (MApp [2]). apply MChar. apply MChar.
      Qed.

      Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii :=
        match re with
        | EmptySet => EmptySet
        | EmptyStr => EmptySet
        | Char t => if beq_nat (nat_of_ascii a) (nat_of_ascii t) then EmptyStr else EmptySet
        | App re1 re2 => if match_eps re1 then Union (App (derive a re1) re2) (derive a re2) else App (derive a re1) re2
        | Union re1 re2 => Union (derive a re1) (derive a re2)
        | Star re => App (derive a re) (Star re)
        end.

      Theorem app_emptyStr :  forall (s :string) re0 re1,
          s =~ App re0 re1 -> []=~ re0 -> s =~ re1.
      Proof.
        intros. 



      Lemma derive_corr : derives derive.
      Proof.
        unfold derives. unfold is_der.
        split.
        - intros H.
          induction re.
          + inversion H.
          + inversion H.
          + inversion H. simpl. rewrite beq_nat_refl. apply MEmpty.
          + simpl. destruct  (match_eps_refl re1).
            
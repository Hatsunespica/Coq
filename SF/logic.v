Set Warnings "-notation-overridden,-parsing".
Require Export mbasics.
Require Export induction.

Theorem plus_comm:
  forall (n m :nat), n + m = m + n.
Proof.
  intros n.
  induction n as [| n' H].
  - simpl. intros [| m'].
    + reflexivity.
    + rewrite <- plus_n_O. reflexivity.
  - simpl. intros m. rewrite <- plus_n_Sm.
    rewrite H. reflexivity.
Qed.


Definition is_three (n :nat) :Prop :=
  n = 3.

Definition injective {A B} (f: A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros x y H.
  injection H.
  congruence.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - reflexivity.
  - reflexivity.
Qed.

Lemma and_intro : forall A B : Prop , A -> B -> A /\ B.
Proof.
  intros A B H1 H2.
  split.
  - congruence.
  - congruence.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 =4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m =0.
Proof.
  intros [|n'] m H.
  - split.
    + reflexivity.
    + simpl in H.
      congruence.
  - split.
    + discriminate.
    + discriminate.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [H1 H2].
  rewrite H1,H2.
  reflexivity.
Qed.

Lemma proj2: forall P Q:Prop,
    P /\ Q -> Q.
Proof.
  intros P Q [H1 H2].
  congruence.
Qed.

Theorem and_commut : forall P Q: Prop,
    P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
  - congruence.
  - congruence.
Qed.

Theorem and_assoc : forall P Q R :Prop,
    P /\ ( Q /\ R ) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [ HQ HR]].
  split.
  - split.
    + congruence.
    + congruence.
  - congruence.
Qed.

Lemma or_example :
  forall  n m: nat, n = 0 \/ m = 0 -> n * m =0.
Proof.
  intros n m [ Hn | Hm].
  - rewrite Hn.
    reflexivity.
  - rewrite Hm.
    rewrite <- mult_n_O.
    reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  congruence.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [| n'].
  - left.
    reflexivity.
  - right.
    reflexivity.
Qed.

Module MyNot.
  Definition not (P:Prop) := P -> False.
  Notation "~ x" := (not x) :type_scope.
End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
    False -> P.
Proof.
  intros P H.
  destruct H.
Qed.

Fact not_implies_our_not: forall (P:Prop),
    ~P -> (forall (Q:Prop), P-> Q).
Proof.
  intros P H Q  H1.
  destruct H.
  apply H1.
Qed.

Notation " x <> y " := (~ (x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros H.
  discriminate.
Qed.

Theorem not_False :
  ~ False.
Proof.
  intros H.
  congruence.
Qed.

Theorem contradiction_implies_anything : forall P Q:Prop,
    (P /\ ~ P) -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HNP].
  unfold not in HNP.
  apply HNP in HP.
  destruct HP.
Qed.

Theorem double_neg : forall P:Prop,
    P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros H1.
  apply H1 in H.
  destruct H.
Qed.

Theorem contrapositive : forall (P Q :Prop),
    (P -> Q) -> ( ~Q -> ~P).
Proof.
  intros P Q H H2 H3.
  unfold not in H2.
  unfold not.
  apply H in H3.
  apply H2 in H3.
  destruct H3.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
    ~(P /\ ~P).
Proof.
  intros H.
  unfold not.
  intros [Hs Hi].
  apply Hi in Hs.
  apply Hs.
Qed.

Theorem not_true_is_false : forall b: bool,
    b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    exfalso.
    apply H.
    reflexivity.
  - reflexivity.
Qed.

Lemma True_is_true : True.
Proof.
  apply I.
Qed.

Module MyIff.
  Definition iff (P Q :Prop) := (P -> Q) /\ (Q -> P).
  Notation "P <-> Q" := (iff P Q)
                          (at level 95, no associativity) : type_scope.
End MyIff.

Theorem iff_sym : forall P Q :Prop,
    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q [HAB HBA].
  split.
  - apply HBA.
  - apply HAB.
Qed.

Lemma not_true_iff_false : forall b,
    b <> true <-> b = false.
Proof.
  intros b.
  split.
  - apply not_true_is_false.
  - intros H.
    rewrite H.
    unfold not.
    intros H'.
    discriminate.
Qed.

Theorem or_distributes_over_and : forall P Q R :Prop,
    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  - intros [Ps | [Qs Rs]].
    + split.
      * apply or_intro with (B := Q) in Ps.
        apply Ps.
      * apply or_intro with (B := R) in Ps.
        apply Ps.
    + apply or_intro with (B := P) in Qs.
      apply or_comm in Qs.
      apply or_intro with (B := P) in Rs.
      apply or_comm in Rs.
      split.
      * apply Qs.
      * apply Rs.
  - intros [[Ps| Qs] [Ps1 | Rs]].
    + left.
      apply Ps.
    + left.
      apply Ps.
    + left.
      apply Ps1.
    + right.
      split.
      * apply Qs.
      * apply Rs.
Qed.

From Coq Require Import Setoids.Setoid.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma four_is_even: exists n : nat, 4= n + n.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
    (exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X:Type) (P: X -> Prop),
    (forall x, P x) -> ~(exists x, ~P x).
Proof.
  intros X P H.
  unfold not.
  intros [x E].
  apply E in H.
  destruct H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q :X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [Hp | Hq]].
    + left.
      exists x.
      apply Hp.
    + right.
      exists x.
      apply Hq.
  - intros [[x Hp] | [x Hq]].
    + exists x.
      left.
      apply Hp.
    + exists x.
      right.
      apply Hq.
Qed.

Fixpoint In {A:Type} (x : A) (l :list A) :Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B :Type) ( f : A -> B) ( l : list A) (x :A),
    In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [| x' l' IHl'].
  - simpl. intros[].
  - simpl.
    intros [H | H].
    + left. rewrite H. reflexivity.
    + right. apply IHl' in H. apply H.
Qed.

Lemma In_map_iff :
  forall (A B :Type) (f : A-> B) (l : list A) (y : B),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  induction l as [| s t H].
  - split.
    + simpl. intros[].
    + intros [x H ].
      destruct H as [H1 H2].
      simpl in H2.
      destruct H2.
  - simpl. split.
    + intros [H1 | H2].
      * exists s.
        split.
        apply H1.
        left. reflexivity.
      * apply H in H2.
        destruct H2 as [x [Hx1 Hx2]].
        exists x.
        split.
        apply Hx1.
        right. apply Hx2.
    +intros [x [H1 [H2 | H2]]].
     * left. rewrite H2. apply H1.
     * right. apply H. exists x.
       split.
       apply H1. apply H2.
Qed.

Lemma In_app_iff : forall A l l' (a:A),
    In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l.
  induction l as [| s t H].
  - simpl.
    intros l' a.
    split.
    intros tmpH. right. apply tmpH.
    intros [tmpH| tmpH].
    + destruct tmpH.
    + apply tmpH.
  - simpl.
    intros l' a.
    split.
    + intros [H1 | H1].
      * left. left. apply H1.
      * apply or_assoc. apply H in H1. right. apply H1.
    + intros H1.
      apply or_assoc in H1.
      destruct H1 as [H2 | H2].
      left. apply H2.
      apply H in H2. right. apply H2.
Qed.

Fixpoint All {T:Type} (P : T-> Prop) (l : list T) :Prop :=
  match l with
  | [] => True
  | s :: t => P s /\ All P t
  end.

Lemma All_In :
  forall T (P: T-> Prop) (l : list T),
    (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  induction l as [| s t H].
  - simpl.
    split.
    + intros H1. apply I.
    + intros H2 H3 [].
  - simpl.
    split.
    + intros H1.
      split.
      assert (tmpH : s = s \/ In s t).
      {
        left. reflexivity.
      }
      * apply H1 in tmpH. apply tmpH.
      * apply H. intros x H2.
        assert (tmpH2 : s = x \/ In x t).
        {
          right. apply H2.
        }
        apply H1 in tmpH2. apply tmpH2.

    + intros [Hs Ha] x [Hsx | Hi] .
      * rewrite <- Hsx. apply Hs.
      * rewrite <- H in Ha. apply Ha in Hi. apply Hi.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n =>
    match (oddb n) with
    | true => Podd n
    | false => Peven n
    end.

Theorem combine_odd_even_intro:
  forall (Podd Peven : nat-> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even.
  destruct (oddb n) as [].
  - apply H1. reflexivity.
  - apply H2. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) ( n : nat),
    combine_odd_even Podd Peven n ->
    oddb n =true ->
    Podd n.
Proof.
  intros Podd Pevn n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  congruence.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) ( n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  congruence.
Qed.

Lemma in_not_nil:
  forall A  (x : A) (l:list A), In x l -> l <> [].
Proof.
  intros A x l H. unfold not.
  intros H1.
  induction l as [| s t H2].
  - simpl in H. destruct H.
  - discriminate H1.
Qed.

Lemma in_not_nil_42:
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x:= 42).
  apply H.
Qed.

Lemma in_not_nil_42_2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Axiom functional_extensionality : forall { X Y :Type} {f g : X -> Y},
    (forall (x:X) , f x = g x) -> f = g.

Example functional_extensionality_ex2:
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  apply plus_comm.
Qed.

Fixpoint rev_append {X}(l1 l2 :list X) : list X:=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev  {X} (l : list X) : list X :=
  rev_append l [].

Theorem rev_append_para:
  forall (X:Type) (l1 l2 : list X),
    rev_append l1 l2 = rev_append l1 [] ++ l2.
Proof.
  intros X l1.
  induction l1 as [| s t H].
  - reflexivity.
  - simpl.
    intros l.
    assert(tmpH: rev_append t (s :: l) = (rev_append t []) ++ (s :: l)). apply H.
    assert(tmpH1: rev_append t [s] = (rev_append t []) ++ [s]). apply H.
    rewrite tmpH. rewrite  tmpH1.
    assert(tmpH2: (rev_append t [] ++ [s]) ++ l = rev_append t [] ++ [s] ++ l).
    {
      symmetry.
      apply app_assoc.
    }
    rewrite tmpH2.
    reflexivity.
Qed.

    
Lemma tr_rev_correct : forall X , @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intros l.
  unfold tr_rev.
  induction l as [| s t H].
  - reflexivity.
  - simpl.
    rewrite <- H.
    apply rev_append_para.
Qed.

Theorem evenb_double : forall k , evenb (double k) = true.
Proof.
  intros k. induction k as [| k'].
  - reflexivity.
  - simpl. congruence.
Qed.

Theorem evenb_double_conv : forall n,
    exists k, n = if evenb n then double k
                  else S (double k).
Proof.
  intros n.
  induction n as [| n' H'].
  - simpl. exists 0. reflexivity.
  - destruct (evenb n') as [] eqn:E.
    + assert(tmpH: evenb (S n') = false). rewrite evenb_S. rewrite E. reflexivity.
      rewrite tmpH. destruct H' as [k Hk]. exists k.
      rewrite Hk. reflexivity.
    + assert(tmpH: evenb (S n') = true). rewrite evenb_S. rewrite E. reflexivity.
      rewrite tmpH. destruct H' as [k Hk]. rewrite Hk. exists (k+1).
      assert(tmpH2: k + 1 = S k). apply plus_comm.

      rewrite tmpH2.
      reflexivity.
Qed.


Theorem even_bool_prop : forall  n,
    evenb n = true <-> exists k , n = double k.
Proof.
  intros n.
  split.
  - intros H.
    destruct (evenb_double_conv n) as [k0 H0].
    rewrite H in H0.
    exists k0. apply H0.
  - induction n as [| n' H'].
    + intros H1. reflexivity.
    + intros H1. destruct H1 as [k0 Hk].
      rewrite Hk. apply evenb_double.
Qed.

Theorem beq_nat_refl : forall n, beq_nat n n =true.
Proof.
  intros n. induction n as [| n' H].
  - reflexivity.
  - simpl. congruence.
Qed.


Theorem beq_nat_true_iff : forall n1 n2: nat,
    beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_injective.
  - intros H. rewrite H. apply beq_nat_refl.
Qed.

Lemma plus_eqb_example : forall  n m p : nat,
    beq_nat n m = true -> beq_nat (n+p) (m+p) = true.
Proof.
  intros n m p H.
  rewrite beq_nat_true_iff in H.
  rewrite H.
  rewrite beq_nat_true_iff.
  reflexivity.
Qed.

Lemma andb_true_iff : forall b1 b2 : bool,
    (andb b1 b2) = true <-> b1 = true /\ b2 = true.
Proof.
  intros [] [].
  split.
  - intros H.
    split.
    + reflexivity.
    + reflexivity.
  - intros H. reflexivity.
  -  split.
     + intros H. simpl in H. discriminate.
     + intros [H1 H2]. discriminate.
  - split.
    + intros H. simpl in H. discriminate.
    + intros [H1 H2]. discriminate.
  - split.
    + intros H. simpl in H. discriminate.
    + intros [H1 H2]. discriminate.
Qed.

Lemma orb_true_iff: forall b1 b2,
    (orb b1 b2) = true <-> b1 = true \/ b2 = true.
Proof.
  intros [] [].
  - split.
    + intros H. left. reflexivity.
    + intros H. reflexivity.
  - split.
    + intros H. left. reflexivity.
    + intros H. reflexivity.
  - split.
    + intros H. right. reflexivity.
    + intros H. reflexivity.
  - split.
    + intros H. simpl in H. discriminate.
    + intros [H1 | H2].
      discriminate.
      discriminate.
Qed.

Theorem nat_bat_neq: forall x y : nat,
    beq_nat x y = false <-> x<> y.
Proof.
  intros x y.
  unfold not.
  split.
  - intros H H1.
    rewrite H1 in H. rewrite beq_nat_refl in H.
    discriminate.

  - intros H.
    destruct (beq_nat x y) eqn:E.
    + apply beq_nat_true_iff in E.
      apply H in E. destruct E.
    + reflexivity.
Qed.

Fixpoint eqb_list {A:Type} (eqb: A -> A -> bool) (l1 l2 : list A) :=
  match l1 with
  | [] => match l2 with
          | [] => true
          | _ => false
          end
  | s1 :: t1 => match l2 with
                | [] => false
                | s2 :: t2 => match (eqb s1 s2) with
                              | true => eqb_list eqb t1 t2
                              | false => false
                              end
                end
  end.

Theorem eqb_relf:
  forall A (eqb: A-> A -> bool) (l : list A),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) -> eqb_list eqb l l = true.
Proof.
  intros A eqb l H.
  induction l as [| s t Hl].
  - reflexivity.
  - simpl. assert(tmpH: eqb s s = true). apply (H s s). reflexivity.
    rewrite tmpH. congruence.
Qed.

    
    

Lemma eqb_list_true_iff:
  forall A (eqb: A -> A->  bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) <->
    forall l1 l2 , eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros A eqb.
  split.
  - intros H.
    split.
    + generalize dependent l2.
      induction l1 as [| s1 t1 Hl1].
      * destruct l2 as [| s2 t2].
          reflexivity.
          simpl. intros H2. discriminate.
      * intros l2 H2. simpl.
        destruct l2 as [| s2 t2].
        discriminate.
        simpl in H2.
        destruct (eqb s1 s2) eqn:E.
        apply H in E. apply Hl1 in H2.
        rewrite E. rewrite H2. reflexivity.
        discriminate.
    + intros H1.
      rewrite H1.
      induction l2 as [| s2 t2 H2].
      * reflexivity.
      * assert(tmpH: eqb s2 s2 = true). apply (H s2 s2). reflexivity.
        apply eqb_relf. apply H.
  - intros H.
    split.
    + intros He. assert(tmpH: eqb_list eqb [a1] [a2] = true). simpl. rewrite He. reflexivity.
      assert(tmpH2: [a1] = [a2]). apply H. apply tmpH.
      injection tmpH2. congruence.
    + intros H1. assert(tmpH: [a1] = [a2]). rewrite H1. reflexivity.
      apply H in tmpH.
      unfold eqb_list in tmpH.
      destruct (eqb a1 a2) eqn: E.
      * reflexivity.
      * discriminate.
Qed.

Theorem foallb_true_iff : forall X test (l : list X),
    forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  intros X test l.
  split.
  - induction l as [| s t H].
    + reflexivity.
    + destruct (test s) eqn:E.
      *simpl. rewrite E. intros H1.
       split.
       reflexivity.
       apply H. apply H1.
      *simpl. rewrite E. intros H1. discriminate.
  - induction l as [| s t H].
    + reflexivity.
    + simpl.
      destruct (test s) eqn:E.
      intros [H11 H12]. apply H. apply H12.
      intros [H11 H12]. discriminate.
Qed.

Definition excluded_middle := forall P : Prop,
    P \/ ~P.

Theorem restricted_excluded_middle: forall P b,
    (P <-> b = true) -> P \/ ~P.
Proof.
  intros P [] H.
  - left. apply H. reflexivity.
  - right. unfold not. rewrite H. intros H1. discriminate.
Qed.

Theorem restricted_excluded_middle_eq: forall (n m : nat),
    n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry. apply beq_nat_true_iff.
Qed.

Theorem excluded_middle_irrefutable: forall (P:Prop),
    ~~(P \/ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  apply H.
  right. intros H1. apply H. left. apply H1.
Qed.

Theorem not_exists_dist :
  excluded_middle -> forall (X:Type) (P :X -> Prop),
    ~(exists x, ~P x) -> (forall x, P x).
Proof.
  intros He X P H. unfold excluded_middle in He.
  assert(tmpH: forall x: X, P x \/ ~ P x). intros x. apply (He (P x)).
  intros x.
  destruct (tmpH x).
  - congruence.
  - unfold not in H. unfold not in H0. exfalso.
    apply H. exists x. congruence.
Qed.

Definition peirce := forall P Q : Prop,
    ((P -> Q) -> P) -> P.

Definition double_negation_elimination := forall P:Prop,
    ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
    ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or := forall P Q :Prop,
    (P -> Q) -> (~P \/ Q).


Theorem one_iff_three:
  excluded_middle <-> double_negation_elimination.
Proof.
  unfold excluded_middle, double_negation_elimination.
  split.
  - intros H P.
    assert(tmpH: P \/ ~P). apply (H P).
    destruct tmpH.
    + intros H1.
      congruence.
    + intros H1. unfold not in H0, H1.
      apply H1 in H0. destruct H0.
  - intros H P.
    assert(tmpH: ~~(P \/ ~P) -> P \/ ~P). apply (H (P \/ ~P)).
    apply tmpH. unfold not. intros H1.
    apply H1. right. intros H2. apply H1. left. congruence.
Qed.

Theorem one_iff_four :
  excluded_middle <-> de_morgan_not_and_not.
Proof.
  unfold excluded_middle, de_morgan_not_and_not.
  split.
  - intros H P Q H1.
    destruct (H P).
    + left. congruence.
    + destruct (H Q).
      * right. congruence.
      * unfold not in H1, H0, H2. exfalso.
        apply H1.
        split.
        congruence.
        congruence.
  - intros H P.
    assert(tmpH: ~(~P/\~~P) -> P\/~P). apply (H P (~P)).
    apply tmpH.
    unfold not. intros [H1 H2].
    apply H2 in H1. destruct H1.
Qed.

Theorem disjunction_comm: forall P Q:Prop,
    P \/ Q <-> Q \/ P.
Proof.
  intros P Q.
  split.
  - intros [H|H].
    right. congruence.
    left. congruence.
  - intros [H|H].
    right. congruence.
    left. congruence.
Qed.


Theorem one_iff_five :
  excluded_middle <-> implies_to_or.
Proof.
  unfold excluded_middle, implies_to_or.
  split.
  - intros H P Q H1.
    destruct (H P).
    * apply H1 in H0. right. congruence.
    * left. congruence.
  - intros H P. 
    assert(tmpH: (P -> P) -> ~P \/ P). apply (H P P).
    apply disjunction_comm.
    apply tmpH. intros H1. congruence.
Qed.

Theorem one_iff_two:
  excluded_middle <-> peirce.
Proof.
  unfold excluded_middle, peirce.
  split.
  - intros H P Q H1.
    destruct (H P).
    + congruence.
    +  apply H0 in H1.
       * destruct H1.
       * intros H2. unfold not in H0. exfalso. apply H0. congruence.
  - intros H.
    apply one_iff_three.
    unfold double_negation_elimination.
    intros P. unfold not. intros H1.
    apply (H P False).
    intros H2. apply H1 in H2.
    destruct H2.
Qed.
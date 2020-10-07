Set Warnings "-notation-overridden,-parsing".
Require Import maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import omega.Omega.
Require Import imp.

Definition Assertion:= state -> Prop.

Definition assert_implies (P Q:Assertion) :Prop :=
  forall st, P st -> Q st.
Notation "P ->> Q" := (assert_implies P Q) (at level 80) :hoare_spec_scope.
Open Scope hoare_spec_scope.
Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) :hoare_spec_scope.

Definition hoare_triple (P:Assertion) (c:com)(Q:Assertion):Prop :=
  forall st st',
    st =[ c ]=> st' -> P st -> Q st'.
Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level):hoare_spec_scope.

Theorem hoare_post_true : forall (P Q:Assertion) c,
    (forall st, Q st) -> {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros. apply (H st').
Qed.

Theorem hoare_pre_false : forall (P Q:Assertion) c,
    (forall st, ~(P st)) ->
    {{P}} c {{Q}}.
Proof.
  unfold hoare_triple. intros. exfalso. apply (H st),H1.
Qed.

Definition assn_sub X a P : Assertion :=
  fun ( st : state) =>
    P (X !-> aeval st a ; st).
Notation "P [ X !-> a ]" := (assn_sub X a P) (at level 10, X at next level).

Theorem hoare_asgn : forall Q X a,
    {{Q [X !-> a]}} X ::= a {{ Q }}.
Proof.
  unfold hoare_triple. intros. inversion H;subst.
  unfold assn_sub in H0.  assumption.
Qed.

Example assn_sub_example : {{ (fun st => st X < 5) [X !-> X + 1]}}
                              X ::= X+1
                                        {{fun st => st X < 5}}.
Proof.
  apply hoare_asgn.
Qed.

Example assn_sub_ex1 :
  {{ (fun st => st  X <= 10) [X !-> 2 * X]}}
    X ::= 2 * X
                {{ fun st => st  X <= 10}}.
Proof.
  apply hoare_asgn.
Qed.

Example assn_sub_ex2 :
  {{ (fun st => (0 <= st X /\ st X <= 5))  [ X !-> 3]}}
    X ::=3
           {{ fun st => 0 <=st X /\ st X <= 5}}.
Proof.
  apply hoare_asgn.
Qed.

(*hoare_asgn_wrong: X ::= X+1*)

Theorem hoare_asgn_fwd :forall m a P,
  {{ fun st => P st /\ st X = m}}
    X ::=a
           {{ fun st => P (X !-> m ;st) /\ st X = aeval (X !->m;st) a}}.
Proof.
  unfold hoare_triple. intros. inversion H;subst. destruct H0 as [H00 H01].
  assert(tmpH: (X !-> st X ; X !-> aeval st a ; st) = (X !-> st X; st)) by apply t_update_shadow.
  assert(tmpH1:(X !-> st X ; st) = st) by apply t_update_same.
  rewrite <- H01.
  rewrite tmpH,tmpH1.
  split.
  - assumption.
  - apply t_update_eq.
Qed.

Theorem hoare_asgn_fwd_exists:
  forall a P,
    {{ fun st => P st}}
      X ::=a
             {{ fun st => exists m, P (X !-> m;st) /\ st X = aeval (X !-> m;st) a}}.
Proof.
  unfold hoare_triple.
  intros. inversion H;subst.
  exists (st X).
  assert(tmpH: (X !-> st X ; X !-> aeval st a ; st) = (X !-> st X; st)) by apply t_update_shadow.
  assert(tmpH1:(X !-> st X ; st) = st) by apply t_update_same.
  rewrite tmpH,tmpH1.
  split.
  - assumption.
  - apply t_update_eq.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q :Assertion) c,
    {{P'}} c {{Q}} -> P ->> P' -> {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros. apply H with st. assumption. apply H0. assumption.
Qed.

Theorem hoare_consequence_post :forall (P Q Q' : Assertion) c,
    {{P}} c {{Q'}} -> Q' ->> Q -> {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  apply H0. apply H with st;assumption.
Qed.

Example hoare_asgn_example1 :
  {{fun st => True}} X ::=1 {{fun st => st X = 1}}.
Proof.
  apply hoare_consequence_pre with (P' := (fun st => st X = 1) [X !-> 1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub,t_update. simpl. reflexivity.
Qed.

Example assn_sub_example2:
  {{ (fun st => st X < 4 )}}
     X ::= X+1
               {{ fun st => st X <5}}.
Proof.
  apply hoare_consequence_pre with ((fun st => st X <5) [X !-> X+1]).
  apply hoare_asgn.
  intros st H. unfold assn_sub,t_update. simpl. omega.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' :Assertion) c,
    {{P'}} c {{Q'}} -> P ->> P' -> Q' ->> Q -> {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  apply hoare_consequence_pre with P'.
  apply hoare_consequence_post with Q'.
  assumption. assumption. assumption.
Qed.

Example hoare_asgn_example1' :
  {{fun st => True}} X ::=1 {{fun st => st X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. reflexivity.
Qed.

Lemma silly2 : forall (P :nat -> nat -> Prop) (Q: nat -> Prop),
    (exists y, P 42 y) -> (forall x y:nat, P x y -> Q x) -> Q 42.
Proof.
  intros P Q HP HQ. destruct HP as [y HP]. eapply HQ.  eassumption.
Qed.

Example assn_sub_ex1' :
  {{ fun st => st X + 1 <=5}} X::= X+1{{fun st => st X <=5}}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl. assumption.
Qed.

Example assn_sub_ex2' :
  {{ fun st => 0<=3 /\ 3 <=5}}X::=3{{fun st => 0<=st X/\st X<=5}}.
Proof.
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros st H. unfold assn_sub,t_update. simpl. assumption.
Qed.

Theorem hoare_skip : forall P,
    {{P}} SKIP{{P}}.
Proof.
  unfold hoare_triple. intros. inversion H;subst. assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
    {{Q}} c2 {{R}} -> {{P}} c1 {{Q}} -> {{P}} c1 ;; c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros. inversion H1;subst. apply H with st'0. assumption. apply H0 with st;assumption.
Qed.

Example hoare_asgn_example3 : forall a n,
    {{ fun st => aeval st a = n}}
      X ::=a;;SKIP
            {{fun st => st X = n}}.
Proof.
  intros. eapply hoare_seq.
  apply hoare_skip.
  eapply hoare_consequence_pre. apply hoare_asgn.
  intros st H. subst. reflexivity.
Qed.

Example hoare_asgn_example4 :
  {{fun st => True}} X::=1 ;;Y::=2 {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  apply hoare_seq with (fun st => st X = 1).
  - eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. unfold assn_sub,t_update. simpl. split. assumption. reflexivity.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    intros st H. reflexivity.
Qed.

Definition swap_program : com := ((Z::=X;;X::=Y);;Y::=Z)%imp.

Theorem swap_exercise :
  {{fun st => st X <= st Y}}
    swap_program
    {{fun st => st Y <= st X}}.
Proof.
  eapply hoare_seq.
  - eapply hoare_asgn.
  - eapply hoare_seq.
    + eapply hoare_asgn.
    + eapply hoare_consequence_pre.
      * eapply hoare_asgn.
      * intros st H. unfold assn_sub,t_update. simpl. assumption.
Qed.

(** hoarestate1 : a may contain X  which is modified **)

Definition bassn b :Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true :forall b st,
    beval st b = true -> (bassn b ) st.
Proof.
  intros.  assumption.
Qed.

Lemma bexp_eval_false : forall b st,
    beval st b = false -> ~((bassn b) st).
Proof.
  intros b st H H1.
  unfold bassn in H1. rewrite H in H1. inversion H1.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
    {{fun st =>  P st /\ bassn b st}} c1 {{Q}} ->
    {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
    {{P}} TEST b THEN c1 ELSE c2 FI{{Q}}.
Proof.
  unfold hoare_triple. intros.
  inversion H1;subst.
  - eapply H. eassumption.  split. assumption. apply bexp_eval_true. assumption.
  - eapply H0. eassumption. split. assumption. apply bexp_eval_false. assumption.
Qed.

Example if_example :
  {{fun st => True}}
    TEST X = 0
               THEN Y::=3
                          ELSE Y::=X+1
                                       FI {{fun st => st X <= st Y}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre. eapply hoare_asgn.
    unfold bassn, assn_sub, t_update,assert_implies.  simpl. intros st [H1 H2].  rewrite eqb_eq in H2. omega.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    unfold assn_sub,t_update,assert_implies. simpl.
    intros st _. omega.
Qed.

Theorem if_minus_plus:
  {{fun st =>True}}
    TEST X <=Y THEN Z ::= Y - X ELSE Y ::= X +Z FI
                                                {{fun st => st Y = st X + st Z}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre. eapply hoare_asgn. unfold bassn,assert_implies, assn_sub,t_update. simpl. intros st [H1 H2].  apply le_plus_minus,leb_complete.  assumption.
  - eapply hoare_consequence_pre. eapply hoare_asgn. unfold bassn,assert_implies,assn_sub,t_update. intros st [H1 H2]. simpl. reflexivity.
Qed.

Module If1.
  Inductive com :Type :=
  |CSkip :com
  | CAss: string -> aexp -> com
  | CSeq : com->com->com
  | CIf : bexp -> com -> com ->com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

  Notation "'SKIP'" := CSkip :imp_scope.
  Notation " c1 ;; c2 " := (CSeq c1 c2)( at level 80, right associativity):imp_scope.
  Notation " X '::=' a" := (CAss X a) (at level 60) :imp_scope.
  Notation "'WHILE' b 'DO' c 'END'"  :=
    (CWhile b c) (at level 80, right associativity):imp_scope.
  Notation  "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" := (CIf e1 e2 e3) (at level 80, right associativity) :imp_scope.
  Notation "'IF1' b 'THEN' c 'FI'" := (CIf1 b c) (at level 80, right associativity) :imp_scope.

  Reserved Notation "st '=[' c ']=>' st'" (at level 40).
  Open Scope imp_scope.
  Inductive ceval : com -> state -> state ->  Prop :=
  | E_Skip : forall st, st  =[ SKIP]=> st
  | E_Ass: forall st a1 n x, aeval st a1 = n -> st =[ x ::=a1]=> (x !-> n;st)
  | E_Seq : forall c1 c2 st st' st'', st =[ c1 ]=> st' -> st' =[ c2]=> st'' -> st =[ c1 ;; c2]=> st''
  | E_IfTrue: forall st st' b c1 c2, beval st b = true -> st =[ c1]=> st' -> st =[ TEST b THEN c1 ELSE c2 FI]=> st'
  | E_IfFalse : forall st st' b c1 c2, beval st b = false -> st =[c2]=> st' -> st =[TEST b THEN c1 ELSE c2 FI]=> st'
  | E_WhileFalse : forall b st c , beval st b =false -> st =[WHILE b DO c END]=> st
  | E_WhileTrue : forall b st st' st'' c, beval st b = true -> st =[ c]=> st' -> st' =[ WHILE b DO c END]=> st'' -> st =[WHILE b DO c END]=> st''
  | E_If1True : forall b st st' c , beval st b =true -> st=[c]=> st' -> st=[ IF1 b THEN c FI]=> st'
  | E_If1False : forall b st c, beval st b = false -> st=[IF1 b THEN c FI]=> st
  where "st '=[' c ']=>' st'" := (ceval c st st').
  Close Scope imp_scope.
  
  Definition hoare_triple  (P:Assertion) (c:com) (Q:Assertion) :Prop :=
    forall st st', st=[c]=> st' -> P st -> Q st'.
  Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level) :hoare_spec_scope.

  Theorem hoare_if1: forall P Q b c,
      {{fun st => P st /\ bassn b st}} c {{Q}} -> {{fun st => P st /\ ~ (bassn b st)}} (SKIP)%imp {{Q}} -> {{P}} (IF1 b THEN c FI)%imp {{Q}}.
  Proof.
    unfold hoare_triple. intros. inversion H1;subst.
    - eapply H. eassumption. split. assumption. apply bexp_eval_true,H5.
    - eapply H0. apply E_Skip. split. assumption. apply bexp_eval_false,H7.
  Qed.

  Theorem hoare_consequence_pre : forall (P P' Q :Assertion) c,
      {{P'}} c {{Q}} -> P ->> P' -> {{P}} c {{Q}}.
  Proof.
    unfold hoare_triple.
    intros. apply H with st. assumption. apply H0. assumption.
  Qed.

  Theorem hoare_asgn : forall Q X a,
      {{Q [X !-> a]}} (X ::= a)%imp {{ Q }}.
  Proof.
    unfold hoare_triple. intros. inversion H;subst.
    unfold assn_sub in H0.  assumption.
  Qed.

  Theorem hoare_skip : forall P,
      {{P}} (SKIP)%imp{{P}}.
  Proof.
    unfold hoare_triple. intros. inversion H;subst. assumption.
  Qed.
  
  Lemma hoare_if1_good:
    {{fun st => st X + st Y = st Z}}
      (IF1 ~(Y=0) THEN X ::= X+Y FI)%imp
      {{fun st => st X = st Z}}.
  Proof.
    apply hoare_if1.
    - eapply hoare_consequence_pre. eapply hoare_asgn.
      intros st [H1 H2]. unfold assn_sub,t_update. simpl. assumption.
    - unfold hoare_triple,bassn. intros st st' H [H1 H2]. inversion H;subst.
      apply not_true_is_false in H2. simpl in H2. rewrite negb_false_iff,eqb_eq in H2. rewrite H2 in H1.  rewrite <- plus_n_O in H1. assumption.
  Qed.
End If1.


Theorem hoare_while :forall P b c,
    {{fun st => P st /\ bassn b st}} c {{P}} ->
    {{P}} WHILE b DO c END {{fun st => P st /\ ~(bassn b st)}}.
Proof.
  unfold hoare_triple.  intros.
  remember (WHILE b DO c END)%imp as ldef.
  induction H0;inversion Heqldef;subst.
  - apply bexp_eval_false in H0. split;assumption.
  - apply bexp_eval_true in H0. apply IHceval2,(H st). reflexivity. assumption. split;assumption.
Qed.

Example while_example :
  {{fun st => st X <=3}}
    WHILE X <=2
                DO X ::= X+1 END
                             {{fun st => st X = 3}}.
Proof.
  eapply hoare_consequence_post.
  apply hoare_while.
  - eapply hoare_consequence_pre. apply hoare_asgn.
    unfold bassn,assert_implies, assn_sub,t_update. simpl. intros. destruct H as [H1 H2]. apply  leb_complete in H2. omega.
  - unfold bassn,assert_implies,assn_sub,t_update. simpl. intros. destruct H as [H1 H2]. apply not_true_is_false in H2. apply leb_complete_conv in H2. omega.
Qed.

Theorem always_loop_hoare : forall P Q,
    {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  unfold hoare_triple. intros.  apply loop_never_stops in H. inversion H.
Qed.

Theorem always_loop_hoare1: forall P Q,
    {{P}} WHILE true DO SKIP END {{Q}}.
Proof.
  intros. apply hoare_consequence_pre with (fun st => True).
  eapply hoare_consequence_post.
  apply hoare_while.
  - apply hoare_post_true. intros. apply I.
  - simpl. intros st [Hinv Hguard].
    exfalso. apply Hguard. reflexivity.
  - intros st H. apply I.
Qed.

Module RepeatExercise.
  Inductive com:Type :=
  | CSkip : com
  | CAsgn : string->aexp->com
  | CSeq: com->com->com
  | CIf : bexp -> com -> com ->com
  | CWhile : bexp -> com -> com
  | CRepeat: com -> bexp -> com.

  Notation "'SKIP'" := CSkip.
  Notation "c1 ;; c2 " :=
    (CSeq c1 c2) (at level 80, right associativity).
  Notation "X '::=' a" := (CAsgn X a) (at level 60).
  Notation "'WHILE' b 'DO' c 'END'" := (CWhile b c) (at level 80, right associativity).
  Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" := (CIf e1 e2 e3) (at level 80, right associativity).
  Notation "'REPEAT' e1 'UNTIL' b2 'END'" := (CRepeat e1 b2) (at level 80, right associativity).

  Reserved Notation "st '=[' c ']=>' st'" (at level 40).
  Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st, st =[SKIP]=>st
  | E_Ass: forall st a1 n X, aeval st a1 = n -> st =[ X ::= a1]=> (X !-> n;st)
  | E_Seq : forall c1 c2 st st' st'', st =[ c1]=> st' -> st' =[ c2 ]=> st'' -> st =[ c1 ;; c2]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true -> st =[c1]=> st' -> st =[TEST b THEN c1 ELSE c2 FI]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false -> st=[c2]=> st' -> st =[TEST b THEN c1 ELSE c2 FI]=> st'
  | E_WhileFalse : forall st b c,
      beval st b =false -> st =[ WHILE b DO c END]=> st
  | E_WhileTrue: forall st st' st'' b c,
      beval st b =true -> st =[ c]=> st' -> st' =[ WHILE b DO c END]=> st'' -> st =[ WHILE b DO c END]=> st''
  | E_RepeatTrue : forall st st' b c, st =[c]=> st' -> beval st' b =true -> st =[ REPEAT c UNTIL b END]=> st'
  | E_RepeatFalse : forall st st' st'' b c, st =[c ]=> st' -> st'=[REPEAT c UNTIL b END]=> st'' -> beval st' b = false -> st=[REPEAT c UNTIL b END]=> st''
  where "st '=[' c ']=>' st'" := (ceval st c st').

  Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) :Prop :=
    forall st st', st =[c ]=> st' -> P st -> Q st'.
  Notation "{{ P }} c {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level).

  Definition ex1_repeat :=
    REPEAT
      X ::= 1 ;; Y::=Y+1
                         UNTIL X = 1 END.
  Theorem ex1_repeat_works:
    empty_st =[ ex1_repeat ]=> (Y!-> 1; X!->1).
  Proof.
    eapply E_RepeatTrue.
    - eapply E_Seq. apply E_Ass. trivial. apply E_Ass. reflexivity.
    - reflexivity.
  Qed.

  Theorem hoare_repeat : forall P b c,
      ({{P}} c {{fun st => P st /\ bassn b st}} \/ {{P}} c {{fun st => P st /\ ~(bassn b st)}}) ->
      {{P}} REPEAT c UNTIL b END {{fun st => P st /\ bassn b st}}.
  Proof.
    intros P b c.
    remember (REPEAT c UNTIL b END) as ldef eqn:E.
    unfold hoare_triple. intros.
    induction H0;inversion E;subst.
    - destruct H as [HH1 | HH2].
      + eapply HH1. eassumption. assumption.
      + assert(tmpH: ~ bassn b st'). eapply HH2. eassumption. assumption.
        unfold bassn in tmpH. rewrite H2 in tmpH. contradiction.
    - destruct H as [HH1 | HH2].
      + assert(tmpH: bassn b st'). eapply HH1. eassumption. assumption.
        unfold bassn in tmpH. rewrite H0 in tmpH. discriminate.
      + apply IHceval2. reflexivity.
        apply (HH2 st st') in H0_.  destruct H0_  as [H0_1 H0_2]. assumption. assumption.
  Qed.

  Theorem hoare_consequence_pre : forall (P P' Q :Assertion) c,
      {{P'}} c {{Q}} -> P ->> P' -> {{P}} c {{Q}}.
  Proof.
    unfold hoare_triple.
    intros. apply H with st. assumption. apply H0. assumption.
  Qed.

  Definition  ex2_repeat := REPEAT Y ::= X ;; X ::= X -1 UNTIL X = 0 END.
  Lemma ex2_repeat_works :
    {{ fun st => st X > 0}} ex2_repeat {{ fun st => st X = 0 /\ st Y >0}}.
  Proof.
    unfold ex2_repeat. remember (REPEAT Y ::= X;; X ::= X - 1 UNTIL X = 0 END) as ldef. unfold hoare_triple. intros. induction H;inversion Heqldef;subst.
    simpl in H1. apply beq_nat_true in H1. 

End RepeatExercise.


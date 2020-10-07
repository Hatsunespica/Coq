Set Warnings "-notation-overridden,-parsing".

Require Import maps.
Require Import Bool.Bool.
Require Import Arith.Arith.
Require Import Init.Nat.
Require Import Arith.PeanoNat. Import Nat.
Require Import Arith.EqNat.
Require Import omega.Omega.
Require Import Lists.List.
Require Import Logic.FunctionalExtensionality.
Import ListNotations.
Require Import imp.

Definition aequiv (a1 a2: aexp) : Prop :=
  forall (st :state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2: bexp) : Prop:=
  forall (st:state),
    beval st b1 = beval st b2.

Theorem aequiv_example: aequiv ( X - X) 0.
Proof.
  intros st. simpl. omega.
Qed.

Theorem bequiv_example: bequiv (X - X = 0)%imp true.
Proof.
  intros st. unfold beval. rewrite aequiv_example. reflexivity.
Qed.

Definition cequiv(c1 c2:com):Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').

Theorem skip_left : forall c,
    cequiv (SKIP ;; c) c.
Proof.
  intros c st st'. split;intros H.
  - inversion H. subst. inversion H2. subst. congruence.
  - apply E_Seq with st. apply E_Skip. congruence.
Qed.

Theorem skip_right: forall c,
    cequiv (c ;; SKIP) c.
Proof.
  intros c st st'.
  split;intros H.
  - inversion H. subst. inversion H5. subst. congruence.
  - apply E_Seq with st'. congruence. apply E_Skip.
Qed.

Theorem TEST_true_simple: forall c1 c2,
    cequiv (TEST true THEN c1 ELSE c2 FI)
           c1.
Proof.
  intros c1 c2 st st'. split;intros H.
  - inversion H. subst. congruence. subst. inversion H5.
  - apply E_IfTrue. reflexivity. congruence.
Qed.

Theorem TEST_true: forall b c1 c2,
    bequiv b BTrue ->
    cequiv (TEST b THEN c1 ELSE c2 FI)
           c1.
Proof.
  intros. intros st st'. split;intros H1.
  - inversion H1. congruence. subst. rewrite H in H6. inversion H6.
  - apply E_IfTrue. apply H. assumption.
Qed.

Theorem TEST_false:forall b c1 c2,
    bequiv b BFalse ->
    cequiv (TEST b THEN c1 ELSE c2 FI)
           c2.
Proof.
  intros. intros st st'. split;intros H1.
  - inversion H1. rewrite H in H6. discriminate. assumption.
  - apply E_IfFalse. apply H. assumption.
Qed.

Theorem swap_if_branches : forall b e1 e2,
    cequiv (TEST b THEN e1 ELSE e2 FI)
           (TEST BNot b THEN e2 ELSE e1 FI).
Proof.
  intros. intros st st'. split;intros H.
  - inversion H;subst.
    + apply E_IfFalse. simpl. rewrite H5. reflexivity. assumption.
    + apply E_IfTrue. simpl. rewrite H5. reflexivity. assumption.
  - inversion H;simpl in H5;subst.
    + apply E_IfFalse. apply negb_true_iff. assumption. assumption.
    + apply E_IfTrue. apply negb_false_iff. assumption. assumption.
Qed.

Theorem WHILE_false : forall b c,
    bequiv b BFalse ->
    cequiv (WHILE b DO c END) SKIP.
Proof.
  intros b c H st st'. split;intros H1.
  - inversion H1; subst. apply E_Skip. subst. rewrite H in H3. discriminate.
  - inversion H1. subst. apply E_WhileFalse. rewrite H. reflexivity.
Qed.

Lemma WHILE_true_nonterm: forall b c st st',
    bequiv b BTrue ->
    ~ (st =[WHILE b DO c END ]=> st').
Proof.
  intros. intros H1. remember (WHILE b DO c END)%imp as cw eqn:Heqcw.
  induction H1;inversion Heqcw;subst.
  - rewrite H in H0. discriminate.
  - apply IHceval2. reflexivity.
Qed.

Theorem WHILE_true : forall b c,
    bequiv b true ->
    cequiv (WHILE b DO c END) (WHILE true DO SKIP END).
Proof.
  intros. intros st st'. split;intros H1.
  - inversion H1;subst.
    + rewrite H in H5. discriminate.
    + apply (WHILE_true_nonterm b c st st') in H. exfalso. apply H, H1.
  - assert(tmpH: bequiv true BTrue). intros tst. reflexivity.
    apply (WHILE_true_nonterm true SKIP st st') in tmpH.
    exfalso. apply tmpH,H1.
Qed.

Theorem loop_unrolling : forall b c,
    cequiv
      (WHILE b DO c END)
      (TEST b THEN (c ;; WHILE b DO c END) ELSE SKIP FI).
Proof.
  intros b c st st'. split;intros H.
  - destruct (beval st b) eqn:E.
    + apply E_IfTrue. assumption. inversion H;subst. rewrite E in H4. discriminate.
      apply (E_Seq c (WHILE b DO c END) st st'0 st'). assumption. assumption.
    + apply E_IfFalse. assumption. inversion H. subst. apply E_Skip. subst. rewrite E in H2. discriminate.
  - destruct (beval st b) eqn:E.
    + inversion H;subst. inversion H6;subst. apply (E_WhileTrue st st'0);assumption. rewrite E in H5. discriminate.
    + inversion H;subst. rewrite E in H5. discriminate. inversion H6;subst. apply E_WhileFalse;assumption.
Qed.

Theorem seq_assoc:forall c1 c2 c3,
    cequiv ((c1 ;; c2) ;; c3) (c1 ;; (c2 ;; c3)).
Proof.
  intros. intros st st'. split; intros H.
  - inversion H;subst. inversion H2;subst.
    apply (E_Seq c1 (c2 ;; c3) st st'1 st'). assumption.
    apply E_Seq with st'0;assumption.
  - inversion H. subst. inversion H5;subst.
    apply E_Seq with st'1.  apply E_Seq with st'0;assumption. assumption.
Qed.

Theorem identity_assignment :forall x ,
    cequiv (x ::=  x) SKIP.
Proof.
  intros x st st'. split;intros H; inversion H;subst.
  - rewrite t_update_same. apply E_Skip.
  - assert(tmpH: st' =[ x ::= x]=> (x !-> st' x ; st')). apply E_Ass. reflexivity.
    rewrite t_update_same in tmpH. assumption.
Qed.

Theorem assign_aequiv :forall (x:string) e,
    aequiv x e->
    cequiv SKIP (x ::= e).
Proof.
  intros. intros st st'. split;intros H1;inversion H1;subst.
    - assert(tmpH: st' =[x ::= e]=> (x !-> (aeval st' e) ; st')). apply E_Ass. reflexivity.
    assert(tmpH1: st' x = aeval st' e). apply H. rewrite <- tmpH1 in tmpH. rewrite t_update_same in tmpH. assumption.
    - assert(tmpH1: st x = aeval st e). apply H. rewrite <- tmpH1. rewrite t_update_same. apply E_Skip.
Qed.

Lemma refl_aequiv : forall (a:aexp) , aequiv a a.
Proof.
  intros. intros st. reflexivity.
Qed.

Lemma sym_aequiv : forall (a1 a2 :aexp),
    aequiv a1 a2 -> aequiv a2 a1.
Proof.
  intros. intros st. symmetry. apply H.
Qed.

Lemma refl_bequiv :forall (b:bexp) ,bequiv b b.
Proof.
  intros. intros st. reflexivity.
Qed.

Lemma sym_bequiv :forall (b1 b2:bexp),
    bequiv b1 b2-> bequiv b2 b1.
Proof.
  intros. intros st. symmetry. apply H.
Qed.

Lemma trans_bequiv:forall (b1 b2 b3: bexp),
    bequiv b1 b2 -> bequiv b2 b3-> bequiv b1 b3.
Proof.
  intros. intros st. rewrite <- (H0 st). apply H.
Qed.

Lemma refl_cequiv:forall (c:com), cequiv c c.
Proof.
  intros. intros st. reflexivity.
Qed.

Lemma iff_trans: forall (P1 P2 P3:Prop),
    (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
Proof.
  intros. rewrite <- H0. assumption.
Qed.

Lemma trans_cequiv:forall (c1 c2 c3:com),
    cequiv c1 c2-> cequiv c2 c3->cequiv c1 c3.
Proof.
  intros. intros st st'. apply iff_trans with (st =[ c2]=> st').
  apply H. apply H0.
Qed.

Theorem CAss_congruence :forall x a1 a1',
    aequiv a1 a1' -> cequiv (CAss x a1) (CAss x a1').
Proof.
  intros. intros st st'.  split;intros H1;inversion H1;subst;apply E_Ass;(try apply H);symmetry;apply H.
Qed.

Theorem CWhile_congruence :forall b1 b1' c1 c1',
    bequiv b1 b1' -> cequiv c1 c1' ->
    cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
Proof.
  unfold bequiv, cequiv.
  intros. split;intros H1.
  - remember (WHILE b1 DO c1 END)%imp as cwhile eqn:Heqc.
    induction H1;inversion Heqc;subst.
    + apply E_WhileFalse. rewrite <- H1. congruence.
    + apply E_WhileTrue with st'. rewrite <- H1. congruence. apply H0. assumption. apply IHceval2. reflexivity.
  - remember (WHILE b1' DO c1' END)%imp as cwhile eqn:Heqc.
    induction H1;inversion Heqc;subst.
    + apply E_WhileFalse. rewrite <- H1. apply H.
    + apply E_WhileTrue with st'. rewrite <- H1. congruence. apply H0. assumption. apply IHceval2. reflexivity.
Qed.

Theorem CSeq_congruence : forall c1 c1' c2 c2',
    cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (c1 ;; c2) (c1' ;; c2').
Proof.
  unfold cequiv.
  intros. split;intros H1.
  - remember (c1 ;; c2)%imp as cseq eqn:Heq.
    induction H1;inversion Heq;subst.
    apply E_Seq with st'. apply H in H1_. assumption. apply H0 in H1_0. assumption.
  - remember (c1' ;; c2')%imp as cseq eqn:Heq.
    induction H1;inversion Heq;subst.
    apply E_Seq with st'. apply H in H1_. assumption. apply H0 in H1_0. assumption.
Qed.

Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
    bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
    cequiv (TEST b THEN c1 ELSE c2 FI) (TEST b' THEN c1' ELSE c2' FI).
Proof.
  unfold bequiv, cequiv.
  intros. split; intros H2.
  - remember (TEST b THEN c1 ELSE c2 FI)%imp  as cif eqn:Heq.
    induction H2;inversion Heq;subst.
    + apply E_IfTrue. rewrite <- H2. congruence. rewrite <- H0. assumption.
    + apply E_IfFalse. rewrite <- H2. congruence. rewrite <- H1. assumption.
  - remember (TEST b' THEN c1' ELSE c2' FI)%imp  as cif eqn:Heq.
    induction H2;inversion Heq;subst.
    + apply E_IfTrue. rewrite <- H2. congruence. apply H0. assumption.
    + apply E_IfFalse. rewrite <- H2. congruence. apply H1. assumption.
Qed.

Example congruence_example :
  cequiv
    (X ::= 0 ;; TEST X = 0 THEN Y ::= 0 ELSE Y ::= 42 FI)
    (X ::= 0 ;; TEST X = 0 THEN Y ::= X - X ELSE Y ::= 42 FI).
Proof.
  apply CSeq_congruence.
  - apply refl_cequiv.
  - apply CIf_congruence.
    apply refl_bequiv.
    apply CAss_congruence. unfold aequiv. simpl. symmetry. apply minus_diag.
    apply refl_cequiv.
Qed.

Definition atrans_sound (atrans: aexp ->aexp ):Prop :=
  forall (a:aexp),
    aequiv a (atrans a).

Definition btrans_sound (btrans:bexp -> bexp) :Prop :=
  forall (b:bexp),
    bequiv b (btrans b).

Definition ctrans_sound (ctrans:com -> com) :Prop :=
  forall (c:com),
    cequiv c (ctrans c).

Fixpoint fold_constants_aexp(a:aexp) :aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => APlus a1' a2'
    end
  | AMinus a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
        | (ANum n1, ANum n2) => ANum (n1 - n2)
        | (a1', a2') => AMinus a1' a2'
    end
  | AMult a1 a2=>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => AMult a1' a2'
    end
  end.

Example fold_aexp_ex1 :
  fold_constants_aexp ((1+2)*X) = (3*X)%imp.
Proof.
  reflexivity. Qed.

Example fold_aexp_ex2 :
  fold_constants_aexp (X -((0 * 6) + Y))%imp = (X - ( 0 + Y))%imp.
Proof. reflexivity. Qed.

Fixpoint fold_constants_bexp (b:bexp):bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else BFalse
    | (a1', a2') => BEq a1' a2'
    end
  | BLe a1 a2 =>
    match (fold_constants_aexp a1, fold_constants_aexp a2) with
    | (ANum n1, ANum n2) => if leb n1 n2 then BTrue else BFalse
    | (a1', a2') => BLe a1' a2'
    end
  | BNot b1 =>
    match (fold_constants_bexp b1) with
    | BTrue => BFalse
    | BFalse => BTrue
    | b1' => BNot b1
    end
  | BAnd b1 b2 =>
    match (fold_constants_bexp b1, fold_constants_bexp b2) with
    | (BTrue,BFalse) => BFalse
    | (BTrue,BTrue) =>BTrue
    | (BFalse, BTrue) => BFalse
    | (BFalse,BFalse) => BFalse
    | (b1', b2') => BAnd b1' b2'
    end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp (true && ~(false && true))%imp = true.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp ((X = Y) && (0 = (2 - ( 1 + 1))))%imp = (( X = Y) && true)%imp.
Proof. reflexivity. Qed.

Open Scope imp.

Fixpoint fold_constants_com (c:com) :com :=
  match c with
  | SKIP => SKIP
  | x ::= a => x ::= (fold_constants_aexp a)
                   | c1 ;; c2 => (fold_constants_com c1) ;; (fold_constants_com c2)
                   | TEST b THEN c1 ELSE c2 FI =>
                     match fold_constants_bexp b with
                     | BTrue => fold_constants_com c1
                     | BFalse => fold_constants_com c2
                     | b' => TEST b' THEN fold_constants_com c1 ELSE fold_constants_com c2 FI
                     end
                   | WHILE b DO c END =>
                     match fold_constants_bexp b with
                     | BTrue => WHILE BTrue DO SKIP END
                     | BFalse => SKIP
                     | b' => WHILE b' DO (fold_constants_com c) END
                     end
  end.

Close Scope imp.

Theorem fold_constants_aexp_sound:
  atrans_sound fold_constants_aexp.
Proof.
  unfold atrans_sound. intros a. unfold aequiv. intros.
  induction a;simpl;try reflexivity; destruct (fold_constants_aexp a1);destruct (fold_constants_aexp a2);rewrite IHa2; rewrite IHa1; reflexivity.
Qed.

Theorem fold_constants_bexp_sound:
  btrans_sound fold_constants_bexp.
Proof.
  unfold btrans_sound. intros. unfold bequiv. intros st.
  induction b.
  - reflexivity.
  - reflexivity.
  - simpl. destruct (fold_constants_aexp a1) eqn:He1;destruct (fold_constants_aexp a2) eqn:He2;rewrite (fold_constants_aexp_sound a1); rewrite He1; rewrite (fold_constants_aexp_sound a2); rewrite He2; simpl; try destruct (n =? n0);reflexivity.
  - simpl. destruct (fold_constants_aexp a1) eqn:He1;destruct (fold_constants_aexp a2) eqn:He2;rewrite (fold_constants_aexp_sound a1); rewrite He1; rewrite (fold_constants_aexp_sound a2); rewrite He2; simpl; try destruct (n <=? n0);reflexivity.
  - simpl. destruct (fold_constants_bexp b);rewrite IHb;try reflexivity;simpl;rewrite IHb;reflexivity.
  - simpl. destruct (fold_constants_bexp b1) eqn:He1;destruct (fold_constants_bexp b2) eqn:He2;rewrite IHb1; rewrite IHb2; reflexivity.
Qed.

Theorem fold_constants_com_sound:
  ctrans_sound fold_constants_com.
Proof.
  unfold ctrans_sound.
  intros c. induction c;simpl.
  - apply refl_cequiv.
  - apply CAss_congruence. apply fold_constants_aexp_sound.
  - destruct (fold_constants_com c1)  eqn:Hfc1;destruct (fold_constants_com c2) eqn:Hfc2;apply CSeq_congruence;assumption.
  - destruct (fold_constants_bexp b) eqn:Hb.
    + apply trans_cequiv with c1. apply TEST_true. rewrite <- Hb. apply fold_constants_bexp_sound. assumption.
    + apply trans_cequiv with c2. apply TEST_false. rewrite <- Hb. apply fold_constants_bexp_sound. assumption.
    + apply CIf_congruence. rewrite <- Hb. apply fold_constants_bexp_sound. assumption. assumption.
    + apply CIf_congruence. rewrite <- Hb. apply fold_constants_bexp_sound. assumption. assumption.
    + apply CIf_congruence. rewrite <- Hb. apply fold_constants_bexp_sound. assumption. assumption.
    + apply CIf_congruence. rewrite <- Hb. apply fold_constants_bexp_sound. assumption. assumption.
  - destruct (fold_constants_bexp b) eqn:Hb.
    + apply WHILE_true. simpl. rewrite <- Hb. apply fold_constants_bexp_sound.
    + apply WHILE_false. rewrite <- Hb. apply fold_constants_bexp_sound.
    + apply CWhile_congruence. rewrite <- Hb. apply fold_constants_bexp_sound. assumption.
    + apply CWhile_congruence. rewrite <- Hb. apply fold_constants_bexp_sound. assumption.
    + apply CWhile_congruence. rewrite <- Hb. apply fold_constants_bexp_sound. assumption.
    + apply CWhile_congruence. rewrite <- Hb. apply fold_constants_bexp_sound. assumption.
Qed.

Fixpoint optimize_0plus_aexp (a:aexp):aexp:=
  match a with
  | ANum n => ANum n
  | AId x => x
  | APlus (ANum 0) a1 => optimize_0plus_aexp a1
  | APlus e1 e2  => APlus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMinus e1 e2 => AMinus (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  | AMult e1 e2 => AMult (optimize_0plus_aexp e1) (optimize_0plus_aexp e2)
  end.

Fixpoint optimize_0plus_bexp (e:bexp) :bexp:=
  match e with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BLe a1 a2 => BLe (optimize_0plus_aexp a1) (optimize_0plus_aexp a2)
  | BNot b1 => BNot (optimize_0plus_bexp b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_bexp b1) (optimize_0plus_bexp b2)
  end.

Open Scope imp.
Fixpoint optimize_0plus_com (c:com):com :=
  match c with
  | SKIP => SKIP
  | x ::= a => x ::= (optimize_0plus_aexp a)
                   | c1 ;; c2 => (optimize_0plus_com c1) ;; (optimize_0plus_com c2)
                   | TEST b THEN c1 ELSE c2 FI => TEST (optimize_0plus_bexp b) THEN (optimize_0plus_com c1) ELSE (optimize_0plus_com c2) FI
                   | WHILE b DO c END =>
                     WHILE (optimize_0plus_bexp b) DO (optimize_0plus_com c) END
  end.
Close Scope imp.

Theorem optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  unfold atrans_sound. intros. unfold aequiv.
  intros. induction a;try reflexivity.
  - simpl. destruct a1 eqn:E.
    + destruct n;simpl.
      * assumption.
      * rewrite IHa2. reflexivity.
    + rewrite IHa2. reflexivity.
    + assert(tmpH1: aeval st (a3 + a4) = aeval st a3 + aeval st a4). reflexivity.
      assert(tmpH2: aeval st (optimize_0plus_aexp (a3 + a4) + optimize_0plus_aexp a2) = aeval st (optimize_0plus_aexp (a3 + a4)) + aeval st (optimize_0plus_aexp a2)). reflexivity.
      rewrite tmpH1. rewrite tmpH2. rewrite <- IHa1. rewrite <- IHa2. reflexivity.
    + assert(tmpH1: aeval st (a3 - a4) = aeval st a3 - aeval st a4). reflexivity.
      assert(tmpH2: aeval st (optimize_0plus_aexp (a3 - a4) + optimize_0plus_aexp a2) = aeval st (optimize_0plus_aexp (a3 - a4)) + aeval st (optimize_0plus_aexp a2)). reflexivity.
      rewrite tmpH1. rewrite tmpH2. rewrite <- IHa1. rewrite <- IHa2. reflexivity.
    + assert(tmpH1: aeval st (a3 * a4) = aeval st a3 * aeval st a4). reflexivity.
      assert(tmpH2: aeval st (optimize_0plus_aexp (a3 * a4) + optimize_0plus_aexp a2) = aeval st (optimize_0plus_aexp (a3 * a4)) + aeval st (optimize_0plus_aexp a2)). reflexivity.
      rewrite tmpH1. rewrite tmpH2. rewrite <- IHa1. rewrite <- IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
Qed.

Theorem optimize_0plus_bexp_sound :
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. unfold bequiv.
  intros. induction b;simpl;try reflexivity;try (rewrite (optimize_0plus_aexp_sound a1); rewrite (optimize_0plus_aexp_sound a2); reflexivity).
  - rewrite IHb. reflexivity.
  - simpl. rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

Theorem optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. unfold cequiv.
  induction c;simpl;try reflexivity.
  - apply CAss_congruence. apply optimize_0plus_aexp_sound.
  - apply CSeq_congruence;assumption.
  - apply CIf_congruence;try apply optimize_0plus_bexp_sound;assumption.
  - apply CWhile_congruence;try apply optimize_0plus_bexp_sound;assumption.
Qed.

Fixpoint subst_aexp (x:string) (u :aexp) (a:aexp):aexp:=
  match a with
  | ANum n => ANum n
  | AId x' => if eqb_string x x' then u else AId x'
  | APlus a1 a2 => APlus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMinus a1 a2=> AMinus (subst_aexp x u a1) (subst_aexp x u a2)
  | AMult a1 a2=> AMult (subst_aexp x u a1) (subst_aexp x u a2)
  end.

Definition subst_equiv_property := forall x1 x2 a1 a2,
    cequiv (x1 ::= a1;; x2 ::= a2) (x1 ::= a1 ;; x2 ::= subst_aexp x1 a1 a2).

Theorem subst_inequiv :
  ~subst_equiv_property.
Proof.
  unfold subst_equiv_property. unfold not. intros contra.
  remember (X ::= X + 1 ;; Y::=X)%imp as c1.
  remember (X ::= X+1 ;; Y ::= X+1)%imp as c2.
  assert (cequiv c1 c2) by (subst; apply contra).
  remember (Y !-> 1 ; X !-> 1) as st1.
  remember (Y !-> 2 ; X !-> 1) as st2.
  assert (H1 : empty_st =[ c1 ]=> st1);
    assert (H2 : empty_st =[ c2 ]=> st2);
    try(subst; apply E_Seq with (st' := (X !-> 1)); apply E_Ass ; reflexivity).
  apply H in H1.
  assert (Hcontra : st1 = st2) by (apply (ceval_deterministic c2 empty_st); assumption).
  assert (Hcontra' : st1 Y = st2 Y) by (rewrite Hcontra;reflexivity). subst.
  inversion Hcontra'. 
Qed.

Inductive var_not_used_in_aexp (x:string) :aexp -> Prop :=
| VNUNum : forall n, var_not_used_in_aexp x (ANum n)
| VNUId : forall y, x <> y -> var_not_used_in_aexp x (AId y)
| VNUPlus : forall a1 a2,
    var_not_used_in_aexp x a1 ->
    var_not_used_in_aexp x a2 ->
    var_not_used_in_aexp x (APlus a1 a2)
| VNUMinus : forall a1 a2,
    var_not_used_in_aexp x a1 ->
    var_not_used_in_aexp x a2 ->
    var_not_used_in_aexp x (AMinus a1 a2)
| VNUMult : forall a1 a2,
    var_not_used_in_aexp x a1 ->
    var_not_used_in_aexp x a2 ->
    var_not_used_in_aexp x (AMult a1 a2).

Lemma aeval_weakening : forall x st a ni,
    var_not_used_in_aexp x a ->
    aeval ( x !-> ni; st) a = aeval st a.
Proof.
  intros.
  induction H;simpl;try (rewrite IHvar_not_used_in_aexp1; rewrite IHvar_not_used_in_aexp2);try reflexivity.
  - apply t_update_neq. assumption.
Qed.

Theorem subst_aequiv :forall st x a1 a2,
    var_not_used_in_aexp x a1 ->
    aeval ( x !->  (aeval st a1); st) (subst_aexp x a1 a2) =
    aeval ( x!-> (aeval st a1);st) a2.
Proof.
  intros. induction a2;try reflexivity;simpl;try (rewrite IHa2_1; rewrite IHa2_2; reflexivity).
  - destruct (eqb_string x x0) eqn:E;try reflexivity.
    + apply eqb_string_true_iff in E. subst.
      assert(aeval (x0 !-> aeval st a1 ; st) a1 = aeval st a1) by ( apply aeval_weakening; assumption). rewrite H0. rewrite t_update_eq. reflexivity.
Qed.

Theorem better_subst_equiv:
  forall x1 x2 a1 a2 ,
    var_not_used_in_aexp x1 a1 -> cequiv (x1 ::= a1 ;; x2 ::= a2) (x1 ::= a1 ;; x2 ::= subst_aexp x1 a1 a2).
Proof.
  split;intros.
  - inversion H0;subst. apply E_Seq with st'0. assumption.
    inversion H3;inversion H6;subst. apply E_Ass. apply subst_aequiv. assumption.
  - inversion H0;subst. apply E_Seq with st'0. assumption.
    inversion H3;inversion H6;subst. apply E_Ass. symmetry. apply subst_aequiv. assumption.
Qed.

Theorem inequiv_exercise:
  ~cequiv (WHILE true DO SKIP END) SKIP.
Proof.
  unfold not,cequiv. intros.
  apply (loop_never_stops empty_st empty_st),H,E_Skip.
Qed.

Module HImp.
  Inductive com :Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CHavoc : string -> com.

  Notation "'SKIP'" := CSkip : imp_scope.
  Notation "X '::=' a" := (CAss X a) (at level 60) : imp_scope.
  Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80, right associativity) :imp_scope.
  Notation "'TEST' e1 'THEN' e2 'ELSE' e3 'FI'" :=
    (CIf e1 e2 e3) (at level 80, right associativity) :imp_scope.
  Notation "'HAVOC' l" := (CHavoc l) (at level 60) : imp_scope.

  
  
  Reserved Notation "st '=[' c ']=>' st'" (at level 40).
  Open Scope imp_scope.
  Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st, st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x, aeval st a1 = n -> st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' -> st' =[ c2 ]=> st'' -> st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true -> st =[ c1 ]=> st' -> st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false -> st =[ c2 ]=> st' -> st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false -> st =[ WHILE b DO c END ]=> st
  | E_WhileTrue: forall st st' st'' b c ,
      beval st b = true -> st =[ c ]=> st' -> st' =[ WHILE b DO c END ]=> st''
                                                                          -> st =[ WHILE b DO c END ]=> st''
  | E_Havoc : forall st x n, st =[ HAVOC x ]=> (x !-> n ; st)
  where "st =[ c ]=> st'" := (ceval c st st').
  Close Scope imp_scope.

  Definition cequiv (c1 c2 : com) : Prop := forall st st' : state,
      st =[ c1 ]=> st' <-> st =[ c2 ]=> st'.

  Definition pXY := (HAVOC X ;; HAVOC Y) %imp.
  Definition pYX := (HAVOC Y ;; HAVOC X)%imp.



  Theorem pXY_cequiv_PYX :
    cequiv pXY pYX \/ cequiv pXY pYX.
  Proof.
    unfold cequiv. left. intros. unfold pXY,pYX. split.
    - destruct (eqb_string X Y) eqn:E.
      + apply eqb_string_true_iff in E. intros. rewrite E. rewrite E in H. assumption.
      + intros. inversion H;subst. inversion H2;subst. inversion H5;subst.
      assert ( tmpH: forall n x, st =[(HAVOC x)%imp]=> ( x !-> n ; st)) by (intros;apply E_Havoc).
      apply E_Seq with (Y !-> n0 ; st).
      apply tmpH.
      assert (tmpH1 : (Y !-> n0; X !-> n; st ) = (X !-> n ; Y !-> n0;st)). apply t_update_permute. apply eqb_string_false_iff in E. assumption.
      rewrite tmpH1. apply E_Havoc.
    - destruct (eqb_string Y X) eqn:E.
      + apply eqb_string_true_iff in E. intros. rewrite E. rewrite E in H. assumption.
      + intros. inversion H;subst. inversion H2;subst. inversion H5;subst.
      assert ( tmpH: forall n x, st =[(HAVOC x)%imp]=> ( x !-> n ; st)) by (intros;apply E_Havoc).
      apply E_Seq with (X !-> n0 ; st). 
      apply tmpH.
      assert (tmpH1 : (X !-> n0; Y !-> n; st ) = (Y !-> n ; X !-> n0;st)). apply t_update_permute. apply eqb_string_false_iff in E. assumption.
      rewrite tmpH1. apply E_Havoc.
  Qed.

  Definition ptwice :=
    (HAVOC X ;; HAVOC Y)%imp.
  Definition pcopy :=
    (HAVOC X ;; Y ::= X)%imp.

  Theorem ptwice_cequiv_pcopy :
    cequiv ptwice pcopy \/ ~ cequiv ptwice pcopy.
  Proof.
    right. unfold cequiv, ptwice, pcopy,not. intros.
    assert(tmpH: empty_st =[ (HAVOC X)%imp]=> (X !-> 0 ;empty_st)) by apply E_Havoc.
    assert (tmpH1 : (X !-> 0) =[ (HAVOC Y)%imp ]=> (Y !-> 1 ; X !-> 0)) by apply E_Havoc.
    assert(tmpH2: empty_st =[ ptwice]=> (Y !-> 1; X !-> 0)). apply E_Seq with (X !->0).
    assumption. assumption.
    apply H in tmpH2. inversion tmpH2. subst. inversion H2;subst. inversion H5;subst. simpl in H6.
    assert(tmpH3: (Y !-> (X !-> n) X; X !-> n) X = n). reflexivity.
    assert(tmpH4: (Y !-> (X !-> n) X; X !-> n) Y = n). reflexivity.
    rewrite H6 in tmpH3. rewrite H6 in tmpH4. rewrite <- tmpH4 in tmpH3. inversion tmpH3.
  Qed.

  Definition p1 : com :=
    (WHILE ~(X = 0) DO
           HAVOC Y ;;
           X ::= X + 1
                       END)%imp.
  Definition p2 : com :=
    (WHILE ~(X = 0) DO SKIP END) %imp.

  Lemma p1_may_diverge : forall st st', st X <> 0 -> ~st =[ p1 ]=> st'.
  Proof.
    intros st st' H contra. unfold p1 in contra.
    remember (WHILE ~X =0 DO HAVOC Y ;; X ::= X+1 END)%imp as ldef eqn:E.
    induction contra;try discriminate.
    - inversion E;subst. simpl in H0. apply negb_false_iff in H0. apply eqb_eq in H0. auto.
    - inversion E;subst. inversion contra1;subst. inversion H3;subst. inversion H6;subst.
      apply IHcontra2.
      + simpl. assert(tmpH: (X !-> (Y !-> n; st) X + 1; Y !-> n; st) X = st X + 1). reflexivity. rewrite tmpH. induction (st X);simpl;auto.
      + reflexivity.
  Qed.

  Lemma p2_may_diverge : forall st st', st X <> 0 -> ~st =[ p2 ]=> st'.
  Proof.
    unfold p2. intros st st' H contra. remember (WHILE ~ X = 0 DO SKIP END)%imp as ldef eqn:E.
    induction contra;try (inversion E);subst.
    - simpl in H0. apply negb_false_iff in H0. apply eqb_eq in H0. apply H,H0.
    - inversion contra1;subst. apply IHcontra2;assumption.
  Qed.

  Theorem p1_p2_equiv: cequiv p1 p2.
  Proof.
    unfold cequiv. intros.
    destruct (st X) eqn:E.
    - unfold p1,p2. split;intros;try (inversion H;subst);try (apply E_WhileFalse;assumption);try (simpl in H2; apply negb_true_iff in H2; apply eqb_neq in H2; exfalso; apply H2,E).
    - assert (st X <>  0) by (rewrite E;auto).
      split;intros.
      + exfalso. apply (p1_may_diverge st st');assumption.
      + exfalso. apply (p2_may_diverge st st');assumption.
  Qed.

  Definition p3 : com :=
    (Z ::=1 ;;
            WHILE ~(X = 0) DO
            HAVOC X;; HAVOC Z  END)%imp.
  Definition p4 :com :=
    (X ::=0 ;; Z ::=1)%imp.

  Theorem p3_p4_inequiv : ~cequiv p3 p4.
  Proof.
    unfold cequiv. intros H.
    assert (tmpH:(X !-> 1) =[ (Z ::= 1)%imp]=> (Z !-> 1; X !-> 1)). apply E_Ass. reflexivity.
    assert (tmpH1: (Z !-> 1 ; X !->1) =[(WHILE ~X =0 DO HAVOC X ;; HAVOC Z END)%imp ]=> (Z !-> 2 ; X !-> 0 ; Z !-> 1; X !-> 1)). apply E_WhileTrue with (Z !-> 2; X !-> 0; Z !-> 1; X !-> 1). reflexivity. apply E_Seq with (X !-> 0; Z !-> 1; X !-> 1). apply E_Havoc. apply E_Havoc. apply E_WhileFalse. reflexivity.
    assert (tmpH2: (X !-> 1) =[ p3 ]=> (Z !-> 2; X !-> 0; Z !-> 1; X !-> 1)). apply E_Seq with (Z !-> 1; X !-> 1);assumption.
    apply H in tmpH2. inversion tmpH2;subst. inversion H2;subst. inversion H5;subst. simpl in H6.
    assert(tmpH3: (Z !-> 2; X !-> 0; X !-> 1) Z = (Z !-> 2; X !-> 0; Z !-> 1; X !-> 1) Z) by reflexivity.
    rewrite <- H6 in tmpH3. inversion tmpH3.
  Qed.

  Definition p5:com :=
    (WHILE ~(X = 1) DO HAVOC X END)%imp.
  Definition p6:com := (X ::=1)%imp.

  Theorem p5_terminate : forall st st', ((st X = 1) -> st =[ p5 ]=> st) /\ ((st X <>  1) ->st =[ p5]=> st' -> st' = (X !-> 1 ; st)).
  Proof.
    intros. split;intros.
    - apply E_WhileFalse. apply negb_false_iff. simpl. apply eqb_eq. assumption.
    - unfold p5 in H0. remember (WHILE ~ X = 1 DO HAVOC X END)%imp as ldef eqn:E1. 
      induction H0;inversion E1;subst.
      + apply negb_false_iff in H0. simpl in H0. apply eqb_eq in H0. rewrite H0 in H. contradiction.
      + clear E1 H0. inversion H0_;subst.
        destruct (n =? 1) eqn:E1.
        * apply eqb_eq in E1. subst. inversion H0_0;subst. reflexivity. simpl in H3. discriminate.
        * assert(tmpH: st''= (X !-> 1; X!-> n; st)). {
            apply IHceval2. rewrite t_update_eq.  apply eqb_neq in E1. assumption. reflexivity.
          }
          rewrite tmpH. apply t_update_shadow.
  Qed.
  
  Theorem p5_p6_equiv: cequiv p5 p6.
  Proof.
    unfold p5, p6,cequiv. intros.
    destruct (st X =? 1) eqn:E.
    - split;intros.
      + inversion H;subst.
        * assert (tmpH: st' = (X !-> st' X; st')) by  (symmetry; apply t_update_same).
          apply eqb_eq in E.
          assert(tmpH1: st' =[ p6]=> (X !-> 1 ; st')) by (apply E_Ass;reflexivity).
          rewrite E in tmpH. rewrite <- tmpH in tmpH1. assumption.
        * apply negb_true_iff in H2. simpl in H2. rewrite E in H2. discriminate.
      + apply eqb_eq in E. inversion H;subst. simpl. rewrite <- E.  rewrite t_update_same. apply E_WhileFalse. apply negb_false_iff. simpl. apply eqb_refl.
    - split;intros;pose proof (p5_terminate st st') as H1;destruct H1 as [H11 H12].
      + apply eqb_neq in E. apply H12 in E. rewrite E. apply E_Ass. reflexivity. assumption.
      + inversion H;subst.
        apply E_WhileTrue with (X !-> 1; st).
        * simpl. apply negb_true_iff. assumption.
        * simpl. apply E_Havoc.
        * apply E_WhileFalse. reflexivity.
  Qed.
End HImp.

Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
    l1 <> l2 -> var_not_used_in_aexp l1 a2 -> var_not_used_in_aexp l2 a1 ->
    cequiv (l1 ::= a1 ;; l2 ::= a2) (l2 ::=a2;; l1::=a1).
Proof.
  unfold cequiv. split;intros.
  - inversion H2;subst. inversion H5;subst. inversion H8;subst.
    apply E_Seq with (l2 !-> aeval st a2; st).
    apply E_Ass. reflexivity.
    assert(tmpH: aeval (l1 !-> aeval st a1 ;st) a2 = aeval st a2) by (apply (aeval_weakening l1 st a2 (aeval st a1));assumption).
    rewrite tmpH.
    assert(tmpH1: (l2 !-> aeval st a2; l1 !-> aeval st a1; st) = (l1 !-> aeval st a1; l2 !-> aeval st a2; st)) by ( apply t_update_permute;assumption).
    rewrite tmpH1. apply E_Ass. apply aeval_weakening. assumption.
  - inversion H2;subst. inversion H5;subst. inversion H8;subst.
    apply E_Seq with (l1 !-> aeval st a1; st).
    apply E_Ass. reflexivity.
    assert(tmpH: aeval(l2 !-> aeval st a2;st) a1 = aeval st a1) by ( apply  (aeval_weakening l2 st a1 (aeval st a2));assumption).
    rewrite tmpH.
    assert(tmpH1: (l1 !-> aeval st a1; l2 !-> aeval st a2; st) = (l2 !-> aeval st a2; l1 !-> aeval st a1; st)). (apply t_update_permute). intros E. symmetry in E. apply H,E.
    rewrite tmpH1. apply E_Ass. apply aeval_weakening. assumption.
Qed.

Definition capprox (c1 c2 : com) :Prop := forall (st st': state),
    st =[ c1 ]=> st' -> st =[c2]=> st'.

Definition c3 : com := SKIP.
Definition c4 : com := (X ::=1)%imp.

Theorem c3_c4_different : ~capprox c3 c4 /\ ~capprox c4 c3.
Proof.
  unfold capprox. unfold not. split;intros.
  - assert(tmpH: empty_st =[ SKIP]=> empty_st) by apply E_Skip.
    apply H in tmpH. inversion tmpH;subst. simpl in H3. rewrite <- H3 in H4.
    assert(tmpH1: (X !-> 1) X = empty_st X) by (rewrite H4;reflexivity).
    unfold empty_st in tmpH1.
    rewrite t_apply_empty in tmpH1.
    rewrite t_update_eq in tmpH1. inversion tmpH1.
  - assert(tmpH: empty_st =[ c4]=> (X !-> 1)) by (apply E_Ass;reflexivity).
    apply H in  tmpH. inversion tmpH;subst.
    assert(tmpH1: empty_st X = (X !-> 1) X) by (rewrite H0;reflexivity).
    unfold empty_st  in tmpH1. rewrite t_apply_empty in tmpH1.
    rewrite t_update_eq in tmpH1. inversion tmpH1.
Qed.

Definition cmin:com := (WHILE true DO SKIP END)%imp.
Theorem cmin_minimal : forall c, capprox cmin c.
Proof.
  unfold capprox. unfold cmin.
  intros. pose proof loop_never_stops as H1. exfalso. apply (H1 st st').
  assumption.
Qed.

Definition zprop (c:com) :Prop:= forall st, exists st', st =[c]=> st'.
Theorem zprop_preserving : forall c c',
    zprop c -> capprox c c' -> zprop c'.
Proof.
  unfold zprop.
  intros. destruct (H st) as [st' H1].
  exists st'. apply H0,H1.
Qed.

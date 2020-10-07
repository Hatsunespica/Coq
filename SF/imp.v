Set Warnings "-notatoin-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
Require Import maps.

Module AExp.
  Inductive aexp : Type :=
  | ANum (n :nat)
  | APlus (a1 a2 :aexp)
  | AMinus (a1 a2:aexp)
  | AMult (a1 a2 : aexp).

  Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 :aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 :bexp).

  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Fixpoint beval (b :bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
    | BLe a1 a2 => leb (aeval a1) (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
    end.

  Fixpoint optimize_0plus (a:aexp) : aexp:=
    match a with
    | ANum n => ANum n
    | APlus (ANum 0) e2 => optimize_0plus e2
    | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
    end.


  Theorem optimize_0plus_sound : forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros.
    induction a.
    - reflexivity.
    - simpl. destruct a1 eqn:E.
      + destruct n eqn:E'.
        * simpl. apply IHa2.
        * simpl. rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
      + simpl. simpl in IHa1. rewrite IHa1. rewrite IHa2. reflexivity.
    - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
    - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  Qed.

  Theorem silly1 :forall ae , aeval ae = aeval ae.
  Proof.
    try reflexivity. Qed.

  Theorem silly2 : forall (P:Prop) , P -> P.
  Proof.
    intros.
    try reflexivity.
    try apply H.
  Qed.

  Lemma foo : forall n, leb 0 n = true.
  Proof.
    intros.
    destruct n.
    - simpl. reflexivity.
    - simpl. reflexivity.
  Qed.

  Lemma foo' : forall n , leb 0 n = true.
  Proof.
    intros.
    destruct n;simpl;reflexivity.
  Qed.

  Theorem optimize_0plus_sound' : forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros.
    induction a; try(simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    - reflexivity.
    - destruct a1 eqn:E; try (simpl;simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
      + destruct n  eqn:E' ; simpl;  rewrite IHa2 ; reflexivity.
  Qed.

  Theorem optimize_0plus_sound'' : forall a,
      aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a.
    induction a; try (simpl; rewrite IHa1; rewrite IHa2;reflexivity);try reflexivity.
    -  destruct a1; try (simpl ; simpl in IHa1 ; rewrite IHa1 ;rewrite IHa2 ;reflexivity).
       + destruct n; simpl; rewrite IHa2; reflexivity.
  Qed.

  Theorem In10: In 10  [1;2;3;4;5;6;7;8;9;10].
  Proof.
    repeat (try (left;reflexivity); right).
  Qed.

  Fixpoint optimize_0plus_b (b : bexp) : bexp :=
    match b with
    | BTrue => BTrue
    | BFalse => BFalse
    | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
    | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
    | BNot b1 => BNot (optimize_0plus_b b1)
    | BAnd b1 b2 =>BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
    end.

  Theorem optimize_0plus_b_sound : forall b,
      beval (optimize_0plus_b b) = beval b.
  Proof.
    intros b.
    induction b; simpl;try(reflexivity);try(rewrite (optimize_0plus_sound a1);rewrite (optimize_0plus_sound a2);reflexivity);try(rewrite IHb;reflexivity).
    - rewrite IHb1. rewrite IHb2. reflexivity.
  Qed.

  Tactic Notation "simpl_and_try" tactic(c) :=
    simpl; try c.

  Example silly_presubrger_example : forall m n o p,
      m + n <= n + o /\ o + 3 = p + 3 -> m <= p.
  Proof.
    intros. omega.
  Qed.

  Module aevalR_first_try.
    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum n :
        aevalR (ANum n) n
    | E_APlus (e1 e2: aexp) (n1 n2 : nat) :
        aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
        aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
        aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMult e1 e2) ( n1 * n2).

    Notation " e '\\' n" := (aevalR e n)
                              (at level 50, left associativity)
                            :type_scope.
  End aevalR_first_try.

  Reserved Notation "e '\\' n" (at level 90, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n: nat) : (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat):
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 :aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat):
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1  * n2)
  where "e '\\' n" := (aevalR e n):type_scope.

  Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue  : bevalR BTrue true
  | E_BFalse : bevalR BFalse false
  | E_BEq (a1 a2 : aexp) (n1 n2: nat) : (a1 \\ n1) -> (a2 \\ n2) -> bevalR (BEq a1 a2) (beq_nat n1 n2)
  | E_BLe (a1 a2 :aexp) (n1 n2 :nat) : (a1 \\ n1) -> (a2 \\ n2) -> bevalR (BLe a1 a2) (leb n1 n2)
  | E_BNot (b1 : bexp) (b: bool) : (bevalR b1 b) -> bevalR (BNot b1) (negb b)
  | E_BAnd (b1 b2 :bexp) (b3 b4 : bool) : (bevalR b1 b3) -> (bevalR b2 b4) -> (bevalR (BAnd b1 b2) (andb b3 b4)).

  Theorem aeval_iff_aevalR : forall a n,
      (a \\ n) <-> aeval a = n.
  Proof.
    split.
    - intros H. induction H;simpl;subst;reflexivity.
    - generalize dependent n.
      induction a;simpl;intros;subst; constructor;try apply IHa1; try apply IHa2;reflexivity.
  Qed.

  Lemma beval_iff_bevalR : forall b bv,
      bevalR b bv <-> beval b = bv.
  Proof.
    split.
    - intros. induction H;simpl;try(apply aeval_iff_aevalR in H;apply aeval_iff_aevalR in H0);subst;reflexivity.
    - generalize dependent bv.
       induction b;intros;subst;simpl;constructor;try (apply aeval_iff_aevalR; reflexivity).
      + apply (IHb (beval b)). reflexivity.
      + apply (IHb1 (beval b1)). reflexivity.
      + apply (IHb2 (beval b2)). reflexivity.
  Qed.

End AExp.

Module aevalR_division.
  Inductive aexp:  Type :=
  | ANum (n :nat)
  | APlus (a1 a2 :aexp)
  | AMinus (a1 a2:aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

  Reserved Notation "e '\\' n" (at level 90, left associativity).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n: nat) : (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat):
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 :aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat):
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1  * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\n3
  where "e '\\' n" := (aevalR e n):type_scope.

End aevalR_division.

Module aevalR_extended.
  Reserved Notation "e '\\' n" (at level 90, left associativity).
  Inductive aexp: Type :=
  | AAny
  | ANum (n : nat)
  | APlus ( a1 a2 : aexp)
  | AMinus ( a1 a2 : aexp)
  | AMult (a1 a2: aexp).

  Inductive aevalR: aexp-> nat -> Prop:=
  | E_Any (n : nat) : AAny \\ n
  | E_ANum (n: nat) : (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat):
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 :aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat):
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1  * n2)
  where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.


Definition state := total_map nat.

Inductive aexp : Type :=
| ANum (n : nat)
| AId (x:string)
| APlus (a1 a2 :aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp :Type :=
| BTrue
| BFalse
| BEq (a1 a2 :aexp)
| BLe (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 :bexp).

Coercion AId : string >-> aexp.
Coercion ANum: nat >-> aexp.

Definition bool_to_bexp (b : bool ) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) :imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x <= y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity): imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) :imp_scope.
Notation " '~' b" := (BNot b) (at level 75, right associativity) :imp_scope.

Fixpoint aeval (st : state) (a:aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st  a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b: bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval  st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Inductive com :Type :=
| CSkip
| CAss (x : string) (a : aexp)
| CSeq ( c1 c2 : com)
| CIf ( b : bexp) (c1 c2 : com)
| CWhile (b: bexp) (c: com).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=CSkip : imp_scope.
Notation "x '::=' a" := (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity) :imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80 , right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

Definition fact_in_coq : com :=
  (Z ::= X;;
          Y ::= 1 ;;
                  WHILE ~(Z = 0) DO
                  Y ::= Y * Z ;;
                              Z ::= Z - 1
                                          END)%imp.

Definition plus2: com :=
  X ::= X +2.
Definition XtimesYinZ : com :=  Z ::= X*Y.
Definition subtract_slowly_body : com :=  Z ::= Z-1;;X::=X-1.
Definition subtract_slowly :com := (WHILE ~(X = 0) DO subtract_slowly_body END)%imp.
Definition subtract_3_from_5_slowly : com :=
  X ::=3;;Z::=5;;subtract_slowly.
Definition loop : com := WHILE true DO SKIP END.

Reserved Notation "st '=[' c ']=>' st'" (at level 40).
Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st,
    st =[ SKIP]=> st
| E_Ass : forall st a1 n x,
    aeval st a1  = n ->
    st =[ x ::= a1]=> (x !-> n; st)
| E_Seq : forall 
c1 c2 st st' st'',
    st =[ c1 ]=> st' -> st' =[ c2 ]=> st'' -> st =[ c1 ;; c2 ]=> st''
| E_IfTrue : forall st st' b c1 c2,
    beval st b = true -> st =[c1]=>st' -> st =[ TEST b THEN c1 ELSE c2 FI]=> st'
| E_IfFalse : forall st st' b c1 c2,
    beval st b = false ->
    st =[c2]=> st' -> st =[TEST b THEN c1 ELSE c2 FI]=> st'
| E_WhileFalse : forall b st c,
    beval st b = false ->
    st =[WHILE b DO c END]=> st
| E_WhileTrue : forall st st' st'' b c,
    beval st b = true ->
    st =[c]=> st' -> st'=[WHILE b DO c END]=> st'' -> st =[WHILE b DO c END]=> st''
where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example :
  empty_st =[
    X ::=2 ;;
           TEST X <= 1
                       THEN Y ::=3 ELSE Z ::= 4
                                                FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Ass. reflexivity.
Qed.

Example ceval_example2 :
  empty_st =[
    X ::= 0 ;; Y ::=1 ;; Z ::=2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Ass. reflexivity.
  - apply (E_Seq (Y ::= 1) _ (X !-> 0) (Y !-> 1; X !-> 0)).
    + apply E_Ass. reflexivity.
    + apply E_Ass. reflexivity.
Qed.

Definition pup_to_n : com :=
  (Y ::= 0 ;;
           WHILE ~(X = 0) DO
           Y ::= Y + X ;;
                       X ::= X - 1
                       END).

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0; Y!-> 3;X!->1;Y!->2;Y!->0;X!->2).
Proof.
  unfold pup_to_n.
  apply (E_Seq _ _ (X!->2) (Y!->0;X!->2)).
  - apply E_Ass. reflexivity.
  - apply (E_WhileTrue (Y!->0;X!->2) (X!->1;Y!->2;Y!->0;X!->2)).
    + reflexivity.
    + apply (E_Seq (Y::=Y+X) _ (Y!->0;X!->2) (Y!->2;Y!->0;X!->2)).
      * apply E_Ass. reflexivity.
      * apply E_Ass. reflexivity.
    + apply (E_WhileTrue (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2) (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2)).
      * reflexivity.
      * apply (E_Seq (Y::=Y+X) _ (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2) (Y!->3;X !-> 1; Y !-> 2; Y !-> 0; X !-> 2)).
        apply E_Ass. reflexivity. apply E_Ass. reflexivity.
      * apply E_WhileFalse. reflexivity.
Qed.


Theorem ceval_deterministic: forall c st st1 st2,
    st =[c]=> st1-> st=[c]=>st2 -> st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;intros;inversion E2;subst;try(reflexivity).
  - assert(tmpH: st' = st'0). apply IHE1_1. apply H1.
    subst. apply IHE1_2, H4.
  - apply (IHE1 st2), H6.
  - rewrite H in H5. discriminate.
  - rewrite H in H5. discriminate.
  - apply IHE1, H6.
  - rewrite H in H2. discriminate.
  - rewrite H in H4. discriminate.
  - apply IHE1_2. apply (IHE1_1 st'0) in H3. subst. apply H6.
Qed.

Theorem plus2_spec : forall st n st',
    st X = n -> st =[plus2]=> st' -> st' X = n +2.
Proof.
  intros. inversion H0. subst. reflexivity.
Qed.

Theorem XtimesYinZ_spec : forall st a b st',
    st X = a -> st Y = b -> st =[XtimesYinZ]=> st' -> st' Z = a * b.
Proof.
  intros.
  inversion H1. subst. reflexivity.
Qed.

Theorem loop_never_stops : forall st st',
    ~(st =[loop]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END)%imp as loopdef eqn:E.
  induction contra;try(inversion E).
  - rewrite H1 in H. inversion H.
  - subst. apply IHcontra2. reflexivity.
Qed.


Open Scope imp_scope.
Fixpoint no_whiles (c:com) : bool :=
  match c with
  | SKIP => true
  | _ ::= _ => true
        | c1 ;; c2 => andb (no_whiles c1) (no_whiles c2)
        | TEST _ THEN ct ELSE cf FI =>
          andb (no_whiles ct) (no_whiles cf)
        | WHILE _ DO _ END => false
  end.
Close Scope imp_scope.

Inductive no_whilesR: com -> Prop:=
| nwR_Skip : no_whilesR SKIP
| nwR_Seq (c1 c2 : com) : no_whilesR c1 -> no_whilesR c2 -> no_whilesR (c1 ;; c2)
| nwR_Ass (x: string) (a : aexp) : no_whilesR (x ::= a)
| nwR_If (b: bexp) (ct cf: com) : no_whilesR ct -> no_whilesR cf -> no_whilesR (TEST b THEN ct ELSE cf FI).

Theorem no_whiles_eqv:
  forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  - intros H.
    induction c;simpl in H;
      try(constructor;apply andb_prop in H; destruct H as [H1 H2]);
      try(apply (IHc1 H1));
      try(apply (IHc2 H2));discriminate.
  - intros H. induction H;simpl;
                try(rewrite IHno_whilesR1; rewrite IHno_whilesR2);
                try(reflexivity).
Qed.

Theorem no_whiles_terminating:
  forall c, no_whilesR c -> forall st, exists st', st =[c]=> st'.
Proof.
  intros c.
  induction c;intros.
  - exists st. constructor.
  - exists ( x !-> (aeval st a); st). constructor. reflexivity.
  - inversion H. subst.
    pose proof  (IHc1 H2 st) as H11. destruct H11 as [st1 H11].
    pose proof (IHc2 H3 st1) as H12. destruct H12 as [st2 H12].
    exists st2. apply (E_Seq c1 c2 st st1 st2). congruence. congruence.
  - inversion H. subst.
    pose proof  (IHc1 H2 st) as H11. destruct H11 as [st1 H11].
    pose proof (IHc2 H4 st) as H12. destruct H12 as [st2 H12].
    destruct (beval st b) eqn:E.
    + exists st1. apply E_IfTrue. congruence. congruence.
    + exists st2. apply E_IfFalse. congruence. congruence.
  - inversion H.
Qed.

Inductive sinstr : Type :=
| SPush (n:nat)
| SLoad (x:string)
| SPlus
| SMinus
| SMult.

Fixpoint s_excute (st:state) (stack : list nat) (prog :list sinstr) : list nat :=
  match prog with
  | [] => stack
  | sp :: tp => match sp with
                | SPush n => s_excute st (n :: stack) tp
                | SLoad x => s_excute st ((st x) :: stack) tp
                | SPlus => match stack with
                           | s1 :: s2 :: sk2 => s_excute st ((s2 + s1) :: sk2) tp
                           | _ => stack
                           end
                | SMinus => match stack with
                            | s1 :: s2 :: sk2 => s_excute st ((s2 - s1) :: sk2) tp
                            | _ => stack
                           end
                | SMult => match stack with
                           | s1 :: s2 :: sk2 => s_excute st ((s2 * s1) :: sk2) tp
                           | _ => stack
                           end
                end
  end.

Example s_excute1 :
  s_excute empty_st []
           [SPush 5; SPush 3; SPush 1;SMinus]
  = [2; 5].
Proof.
  reflexivity. Qed.

Example s_excute2 :
  s_excute (X !-> 3) [3;4] [SPush 4; SLoad X; SMult; SPlus] = [15;4].
Proof.
  reflexivity. Qed.

Fixpoint s_compile (e: aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId x => [SLoad x]
  | APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
  | AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++[SMinus]
  | AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
  end.

Example s_compile1 :
  s_compile (X - (2 * Y))%imp
  = [SLoad X;SPush 2; SLoad Y;SMult; SMinus].
Proof.
  reflexivity. Qed.


Theorem s_excute_process : forall (e : aexp) (st : state) (s1 : list nat) (other : list sinstr),
    s_excute st s1 (s_compile e ++ other) =
    s_excute st ((aeval st e) :: s1) other.
Proof.
  induction e;simpl;intros;try reflexivity.
  - assert(tmpH: ((s_compile e1 ++ s_compile e2 ++ [SPlus]) ++ other =
                  s_compile e1 ++ s_compile e2 ++ [SPlus] ++ other)).
    rewrite app_ass. rewrite app_ass. reflexivity.
    rewrite tmpH. clear tmpH.
    assert(tmpH: (s_excute st s1 (s_compile e1 ++ s_compile e2 ++ SPlus :: other) =
                   s_excute st (aeval st e1 :: s1) (s_compile e2 ++ SPlus :: other))).
    apply IHe1. simpl.
    rewrite tmpH. clear tmpH.
    assert(tmpH: s_excute st (aeval st e1 :: s1) (s_compile e2 ++ SPlus :: other) =
                 s_excute st (aeval st e2 :: aeval st e1 :: s1) (SPlus :: other)).
    apply IHe2. rewrite tmpH. reflexivity.
  - assert(tmpH: ((s_compile e1 ++ s_compile e2 ++ [SMinus]) ++ other =
                  s_compile e1 ++ s_compile e2 ++ [SMinus] ++ other)).
    rewrite app_ass. rewrite app_ass. reflexivity.
    rewrite tmpH. clear tmpH.
    assert(tmpH: (s_excute st s1 (s_compile e1 ++ s_compile e2 ++ SMinus :: other) =
                   s_excute st (aeval st e1 :: s1) (s_compile e2 ++ SMinus :: other))).
    apply IHe1. simpl.
    rewrite tmpH. clear tmpH.
    assert(tmpH: s_excute st (aeval st e1 :: s1) (s_compile e2 ++ SMinus :: other) =
                 s_excute st (aeval st e2 :: aeval st e1 :: s1) (SMinus :: other)).
    apply IHe2. rewrite tmpH. reflexivity.
  - assert(tmpH: ((s_compile e1 ++ s_compile e2 ++ [SMult]) ++ other =
                  s_compile e1 ++ s_compile e2 ++ [SMult] ++ other)).
    rewrite app_ass. rewrite app_ass. reflexivity.
    rewrite tmpH. clear tmpH.
    assert(tmpH: (s_excute st s1 (s_compile e1 ++ s_compile e2 ++ SMult :: other) =
                   s_excute st (aeval st e1 :: s1) (s_compile e2 ++ SMult :: other))).
    apply IHe1. simpl.
    rewrite tmpH. clear tmpH.
    assert(tmpH: s_excute st (aeval st e1 :: s1) (s_compile e2 ++ SMult :: other) =
                 s_excute st (aeval st e2 :: aeval st e1 :: s1) (SMult :: other)).
    apply IHe2. rewrite tmpH. reflexivity.
Qed.

Theorem s_compile_correct : forall (st: state) (e :aexp),
    s_excute st [] (s_compile e) = [aeval st e].
Proof.
  intros.
  assert(tmpH: s_compile e = s_compile e ++ []). rewrite app_nil_r. reflexivity.
  rewrite tmpH. clear tmpH.
  pose proof (s_excute_process e st [] [] ) as tmpH.
  rewrite tmpH. reflexivity.
Qed.


Fixpoint beval_sc (st : state) (b: bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval_sc st b1)
  | BAnd b1 b2 => if (beval_sc  st b1) then  (beval_sc st b2) else false
  end.

Theorem short_circuit: forall (st: state) (b:bexp),
    beval st b = beval_sc st b.
Proof.
  intros.
  induction b;simpl;try reflexivity.
Qed.

Module BreakImp.
  Inductive com:Type:=
  | CSkip
  | CBreak
  | CAss (x : string) (a : aexp)
  | CSeq ( c1 c2 : com)
  | CIf ( b : bexp) (c1 c2 : com)
  | CWhile (b: bexp) (c: com).

  
  Notation "'SKIP'" :=CSkip  .
  Notation "'BREAK'" := CBreak.
  Notation "x '::=' a" := (CAss x a) (at level 60)  .
  Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity).
  Notation "'WHILE' b 'DO' c 'END'" :=
    (CWhile b c) (at level 80 , right associativity).
  Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
    (CIf c1 c2 c3) (at level 80, right associativity).

  Inductive result : Type :=
  | SContinue
  | SBreak.
  
  Reserved Notation "st '=[' c ']=>' st' '/' s" (at level 40, st' at next level).
  
  Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st, st =[ CSkip ]=> st / SContinue
  | E_Break : forall st, st =[ CBreak ]=> st /SBreak
  | E_Ass: forall st x n a1, aeval st a1 = n -> st =[ x ::= a1 ]=> (x !-> n; st) / SContinue
  | E_Seq1Continue : forall c1 c2 st st' st'' r,
      st =[ c1 ]=> st' / SContinue
                   -> st' =[ c2 ]=> st'' / r -> st  =[ c1 ;; c2 ]=> st'' / r
  | E_Seq1Break: forall c1 c2 st st',
      st =[ c1 ]=> st' / SBreak -> st =[ c1 ;; c2 ]=> st' / SBreak
  | E_IfTrue : forall st st' b c1 c2 r,
    beval st b = true -> st =[c1]=>st'/ r -> st =[ TEST b THEN c1 ELSE c2 FI]=> st' / r
  | E_IfFalse : forall st st' b c1 c2 r,
    beval st b = false ->
    st =[c2]=> st' / r -> st =[TEST b THEN c1 ELSE c2 FI]=> st' / r
  | E_WhileFalse : forall b st c,
    beval st b = false -> 
    st =[WHILE b DO c END]=> st / SContinue
  | E_WhileTrueContinue: forall st st' st'' b c r,
      beval st b = true
      -> st =[c]=> st' / SContinue
                   -> st'=[WHILE b DO c END]=> st'' / r
                                               -> st =[WHILE b DO c END]=> st'' / r
  | E_WhileTrueBreak: forall st st'  b c ,
      beval st b = true
      -> st =[c]=> st' / SBreak -> st =[ WHILE b DO c END]=> st' /SContinue
  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

  Theorem break_ignore : forall c st st' s,
      st =[ BREAK ;; c]=> st' / s -> st = st'.
  Proof.
    intros. inversion H.
    - subst. inversion H2.
    - subst. inversion H5. subst. reflexivity.
  Qed.

  Theorem while_continue : forall b c st st' s,
      st =[ WHILE b DO c END ]=> st' / s -> s = SContinue.
  Proof.
    intros. remember (WHILE b DO c END) as cc.
    induction H
    ;try reflexivity
    ;try (simpl; apply (IHceval2 Heqcc))
    ;try inversion Heqcc.
  Qed.

  Theorem while_stops_on_break: forall b c st st',
      beval st b = true ->
      st =[ c ]=> st' / SBreak ->
                  st =[ WHILE b DO c END ]=> st' / SContinue.
  Proof.
    intros. constructor.
    apply H. apply H0.
  Qed.

  Theorem while_break_true : forall b c st st',
      st =[ WHILE b DO c END ]=> st' / SContinue ->
                                 beval st' b = true  ->
                                 exists st'', st'' =[ c ]=> st' / SBreak.
  Proof.
    intros. remember (WHILE b DO c END) as cc.
    induction H;inversion Heqcc;subst.
    - rewrite H0 in H. inversion H.
    - apply IHceval2. reflexivity. apply H0.
    - exists st. apply H1.
  Qed.

  Theorem ceval_deterministic : forall (c:com) st st1 st2 s1 s2,
      st =[ c ]=> st1 / s1 -> st =[ c ]=> st2 / s2 -> st1 = st2 /\ s1 = s2.
  Proof.
    intros. generalize dependent st2. generalize dependent s2.
    induction H;intros.
    - inversion H0. subst. split. reflexivity. reflexivity.
    - inversion H0. subst. split. reflexivity. reflexivity.
    - inversion H0. subst. split. reflexivity. reflexivity.
    - inversion H1;subst.
      + subst. apply IHceval1 in H4. destruct H4 as [H41 H42]. subst. apply IHceval2 in H8. apply H8.
      + subst. apply IHceval1 in H7. destruct H7 as [H71 H72]. discriminate H72.
    -  inversion H0;subst.
      + apply IHceval in H3. destruct H3 as [H33 H32]. discriminate.
      + apply IHceval in H6. apply H6.
    - inversion H1;subst.
      + apply IHceval in H9. apply H9.
      + rewrite H8 in H. discriminate.
    - inversion H1;subst.
      + rewrite H8 in H. discriminate.
      + apply IHceval in H9. apply H9.
    - inversion H0;subst.
      + split. reflexivity. reflexivity.
      + rewrite H3 in H. discriminate.
      + rewrite H3 in H. discriminate.
    - inversion H2;subst.
      + rewrite H8 in H. discriminate.
      + apply IHceval1 in H6. destruct H6 as [H61 H62]. subst. apply IHceval2 in H10. apply H10.
      + apply IHceval1 in H9. destruct H9 as [H91 H92]. discriminate.
    - inversion H1;subst.
      + rewrite H in H7;discriminate.
      + apply IHceval in H5. destruct H5 as [H51 H52];discriminate.
      + apply IHceval in H8. destruct H8 as [H81 H82]. split. apply H81. reflexivity.
  Qed.
End BreakImp.

  
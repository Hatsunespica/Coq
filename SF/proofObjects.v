Set Warnnings " -notation-overridden,-parsing".
Require Export indProp.

Theorem ev_4'' : even 4.
Proof.
  Show Proof.
  apply ev_ss.
  Show Proof.
  apply ev_ss.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : even 4 := ev_ss 2 (ev_ss 0 ev_0).

Theorem ev_8: even 8.
Proof.
  apply ev_ss, ev_ss, ev_4''.
Qed.

Definition ev_8' : even 8 := ev_ss 6 (ev_ss 4 ev_4''').

Theorem ev_plus4: forall n, even n -> even (4 + n).
Proof.
  intros.
  apply ev_ss, ev_ss, H.
Qed.

Definition ev_plus4' (n : nat) (H : even n) : even (4 + n) :=
  ev_ss (2+n) (ev_ss n H).

Definition addl: nat -> nat.
  intros n.
  Show Proof.
  apply S.
  Show Proof.
  apply n.
Defined.

Module Props.
  Module And.
    Inductive and (P Q:Prop) : Prop :=
    | conj : P -> Q -> and P Q.
  End And.

  Lemma and_comm : forall P Q:Prop, P /\ Q <-> Q /\ P.
  Proof.
    intros. split.
    - intros [HP HQ]. split. apply HQ. apply HP.
    - intros [HQ HP]. split. apply HP. apply HQ.
  Qed.

  Definition and_comm'_aux P Q (H: P /\ Q) : Q /\ P:=
    match H with
    | conj HP HQ => conj HQ HP
    end.

  Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
    conj (and_comm'_aux P Q) (and_comm'_aux Q P).

  Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
    fun (P Q R : Prop) => fun (H1: P /\ Q) => fun (H2: Q /\ R) =>
                                                match H1 with
                                                | conj P Q => match H2 with
                                                              | conj Q R => conj P R
                                                              end
                                                end.

  Module Or.
    Inductive or (P Q :Prop) :Prop :=
    | or_introl : P -> or P Q
    | or_intror : Q -> or P Q.
  End Or.

  Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
    fun (P Q:Prop) => fun (H1: P \/ Q) =>
                        match H1 with
                        | or_introl HP => or_intror HP
                        | or_intror HQ => or_introl HQ
                        end.

  Module Ex.
    Inductive ex{A:Type} (P :A -> Prop) :Prop:=
    | ex_intro : forall x:A , P x -> ex P.
  End Ex.

  Definition some_nat_is_even : exists n, even n :=
    ex_intro even 4 (ev_ss 2 (ev_ss 0 ev_0)).

  Definition ex_ev_Sn: ex (fun n => even (S n)) :=
    ex_intro (fun n => even (S n)) 1 (ev_ss 0 ev_0).

  Inductive True: Prop :=
  | I :True.
  Inductive False : Prop :=.
End Props.

Module MyEquality.
  Inductive eq{X:Type} : X -> X -> Prop:=
  | eq_refl : forall x, eq x x.
  Notation "x == y" := (eq x y)
                         (at level 70, no associativity)
                       : type_scope.

  Lemma four: 2 + 2 == 1 + 3.
  Proof.
    apply eq_refl.
  Qed.

  Definition fout' : 2 + 2 == 1 + 3 := eq_refl 4.

  Definition singleton : forall (X:Type) (x:X), [] ++ [x] == x :: [] :=
    fun (X:Type) (x:X) => eq_refl [x].

  Lemma equality__leibniz_equality : forall (X:Type) (x y :X),
      x == y -> forall P:X -> Prop, P x -> P y.
  Proof.
    intros. inversion H. subst x0. rewrite <- H2. congruence.
  Qed.

  Lemma leibniz_equality__equality : forall (X:Type) (x y :X),
      (forall P:X-> Prop, P x -> P y) -> x ==y.
  Proof.
    intros.
    assert(tmpH: x == x). apply (eq_refl x).
    apply (H (eq x) tmpH).
  Qed.
End MyEquality.


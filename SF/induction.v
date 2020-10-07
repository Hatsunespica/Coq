Require Export basics.

Theorem plus_n_O : forall n:nat, n = n + O.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem mult_O_r : forall n : nat,
    n * O = O.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    congruence.
Qed.

Theorem plus_n_Sm : forall n m: nat,
    S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
    n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - simpl.
    rewrite <- plus_n_Sm.
    rewrite <- IHn'.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p: nat,
    n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IHn'.
    reflexivity.
Qed.

Fixpoint double (n:nat):=
  match n with
  | 0 => 0
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [| n'].
  - reflexivity.
  - simpl.
    rewrite <- plus_n_Sm.
    rewrite <- IHn'.
    reflexivity.
Qed.

Lemma negb_negb: forall p : bool, negb (negb p) =p.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem evenb_S: forall n : nat,
    evenb (S n) = negb (evenb n).
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - rewrite IHn'.
    simpl.
    rewrite  negb_negb.
    reflexivity.
Qed.



    



    
    

  
    
      
      
      
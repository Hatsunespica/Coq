Inductive B:Type :=
|Bt
|Bf
|Bcom : B -> B -> B.

Inductive Br:B->B->Prop:=
|Brf (B1 :B): Br (Bcom Bf B1) B1
|Brt (B1 :B): Br (Bcom Bt B1) Bt.

Module NatPlayground.

  Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Definition minustwo ( n : nat ) : nat :=
  match n with
  | O => O
  | S O => O
  | S ( S n') => n'
  end.

Compute minustwo 3.

Fixpoint evenb ( n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb ( n : nat) : bool := negb ( evenb n).

Module NatPlayground2.

  Fixpoint plus ( n : nat)( m : nat ) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.

  Fixpoint mult ( n m : nat) : nat :=
    match n with
    |  O => O
    | S n' => plus m (mult n' m)
    end.

  Fixpoint minus ( n m : nat) : nat :=
    match n,m with
    | O , _  => O
    | S _ , O => n
    | S n' , S m' => minus n' m'
    end.

  End NatPlayground2.

  Fixpoint exp ( base power : nat) : nat :=
    match power with
    | O  => S O
    | S p => mult base (exp base p)
    end.

  Fixpoint factorial (n:nat) : nat :=
    match n with
    | O => 1
    | S n' => mult n (factorial n')
    end.

  Notation "x + y" := (plus x y)
                        (at level 50, left associativity)
                      : nat_scope.
  Notation "x - y" := (minus x y)
                        (at level 50, left associativity)
                      :nat_scope.
  Notation " x * y" :=(mult x y)
                        (at level 40, left associativity)
                      :nat_scope.

  Fixpoint beq_nat (n m : nat) :bool :=
    match n with
    | O => match m with
           | O => true
           | S m' => false
           end
    | S n' => match m with
              | O => false
              | S m' => beq_nat n' m'
              end
    end.

  Fixpoint leb (n m: nat) : bool :=
    match  n with
    | O => true
    | S n' => match m with
              | O => false
              | S m' => leb n' m'
              end
    end.

  Example test_leb1: (leb 2 2)  = true.
  Proof. simpl. reflexivity. Qed.
  Example test_leb2: (leb 1 4) = true.
  Proof. simpl. reflexivity. Qed.
  Example test_leb3: (leb 5 2) = false.
  Proof. simpl. reflexivity. Qed.

  Definition blt_nat (n m: nat) : bool :=
    match (leb n m) with
    | true =>(negb (beq_nat n m))
    | false => false
    end.

  Example test_blt_nat1: (blt_nat 2 2) =false.
  Proof. simpl. reflexivity. Qed.  

  Theorem plus_O_n : forall n : nat, O + n = n.
  Proof.
    intros n. simpl. reflexivity. Qed.

  Theorem puls_1_1 : forall n: nat, 1 + n = S n.
  Proof.
    intros n. reflexivity. Qed.

  Theorem mult_0_1 : forall n: nat, 0 * n = 0.
  Proof.
    intros n. reflexivity. Qed.

  Theorem plus_id_example : forall n m : nat,
      n = m -> n + n = m + m.
  Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity. Qed.

  Theorem plus_id_exercise: forall n m o: nat,
      n = m -> m = o -> n + m = m + o.
  Proof.
    intros n m o.
    intros H.
    rewrite -> H.
    intros H0.
    rewrite -> H0.           
    reflexivity. Qed.

  Theorem mult_O_plus : forall n m: nat,
      (O + n) * m = n * m.
  Proof.
    intros n m.
    rewrite -> plus_O_n.
    reflexivity. Qed.

  Theorem mult_S_1 : forall n m: nat,
      m = S n -> m * (1 + n) = m * m.
  Proof.
    intros n m.
    intros H.
    rewrite -> H.
    reflexivity. Qed.

  Theorem plus_1_neq_O : forall n : nat,
      beq_nat ( n + 1) 0 =false.
  Proof.
    intros n. destruct n as [| n'].
    - reflexivity.
    - reflexivity. Qed.

  Theorem andb_commutative : forall b c, andb b c = andb c b.
  Proof.
    intros b c. destruct b.
    - destruct c.
      + reflexivity.
      + reflexivity.
    - destruct c.
      + reflexivity.
      + reflexivity.
  Qed.

  Theorem andb_true_elim2 : forall b c:bool,
      andb b c = true -> c = true.
  Proof.
    intros [] [] H.
    - reflexivity.
      Admitted.

  
      
  
    

  Theorem zero__nbeq_plus_1 : forall n: nat,
      beq_nat 0 (n + 1)=false.
  Proof.
    intros [| n].
    - reflexivity.
    - reflexivity.
  Qed.
  
  (* Fixpoint tmp_rec ( n m : nat) : nat :=
    match n with
    | O => O
    | _ =>
      match m with
      | O => (tmp_rec (n + 1) (m + 1))
      | _ => (tmp_rec (minustwo n) O)
      end 
    end. *)
  Theorem identity_fn_applied_twice :
    forall ( f : bool -> bool),
      (forall (x : bool), f x = x) ->
      forall (b : bool), f ( f b) = b.
  Proof.
    intros f x b.
    rewrite -> x.
    rewrite -> x.
    reflexivity.
    Qed.
          
  Theorem negation_fn_applied_twice :
    forall (f :bool -> bool),
      (forall (x : bool), f x = negb x) ->
      forall (b : bool), f ( f b) = b.
  Proof.
    intros f x b.
    rewrite -> x.
    rewrite -> x.
    destruct b.
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem andb_eq_orb :
    forall ( b c :bool), (andb b c = orb b c) -> b =c.
  Proof.

    

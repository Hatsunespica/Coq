Require Export induction.
Module NatList.
  
  Inductive natprod : Type :=
  | pair : nat -> nat -> natprod.

  Definition fst (p :natprod) : nat :=
    match p with
    | pair x y => x
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair x y => y
    end.

  Notation "( x , y )" := (pair x y).

  Definition fst' ( p :natprod) : nat :=
    match p with
    | (x,y) =>x
    end.

  Definition snd' (p : natprod) : nat :=
    match p with
    | (x,y) => y
    end.

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (x,y)=>(y,x)
    end.

  Theorem surjective_pairing' : forall (n m : nat),
      (n,m) = (fst (n,m), snd (n,m)).
  Proof.
    reflexivity.
  Qed.

  Theorem snd_fst_is_swap : forall (p : natprod),
      (snd p, fst p) = swap_pair p.
  Proof.
    intros [n m].
    reflexivity.
  Qed.

  Theorem fst_swap_is_snd : forall (p: natprod),
      fst (swap_pair p) = snd p.
  Proof.
    intros [n m].
    reflexivity.
  Qed.

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Notation "x :: l" := (cons x l)
                         (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).


  Definition mylist3 := [1;2;3].
  Definition mylist2 := 1 :: 2 :: 3 :: nil.
  Definition mylist1 :=  1 :: (2 :: (3 :: nil)).

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | 0 => nil
    | S count' =>  n :: (repeat n count')
    end.

  Fixpoint length (l:natlist) : nat :=
    match l with
    | nil => 0
    |  h :: t => S (length t)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y)
                         (right associativity, at level 60).

  Definition hd (default:nat) (l:natlist) :nat  :=
    match l with
    | nil => default
    | h :: t => h
    end.

  Definition tl (l:natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

  Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t =>
      match h with
      | 0 => nonzeros t
      | _ => [h] ++  (nonzeros t)
      end
    end.

  Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t =>
      match (oddb h) with
      | true => h :: (oddmembers t)
      | false => oddmembers t
      end
    end.

  Fixpoint countoddmembers (l : natlist) : nat :=
    match l with
    | nil => 0
    | h :: t =>
      match (oddb h) with
      | true => S (countoddmembers t)
      | false => countoddmembers t
      end
    end.

  Fixpoint alternate ( l1 l2 : natlist)  : natlist :=
    match l1 with
    | nil => l2
    | h :: t =>
      match l2 with
      | nil => l1 
      | h' :: t' => h :: h' :: ( alternate t t')
      end
    end.

  Definition bag := natlist.
    
  Fixpoint count (v:nat) (s:bag) : nat :=
    match s with
    | nil => 0
    | h :: t =>
      match (beq_nat v h) with
      | true => S (count v t)
      | false => (count v t)
      end
    end.
  
  Definition sum : bag -> bag -> bag := alternate.
  
  Definition  add ( v:nat)(s:bag) : bag := v :: s .

  Definition member (v:nat) (s:bag) : bool := negb ( beq_nat 0 (count v s)).

  Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t =>
      match (beq_nat v h) with
      | true => t
      | false => remove_one v t
      end
    end.

  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
    | nil => nil
    | h :: t =>
      match (beq_nat h v) with
      | true => remove_all v t
      | false => h :: (remove_all v t)
      end
    end.

  Theorem beqT : forall n : nat, beq_nat n n = true.
  Proof.
    intros n.
    induction  n as  [| n' H'].
    - reflexivity.
    - simpl.
      congruence.
  Qed.
  
  Theorem bag_theorem : forall  n: natlist, forall m:nat,
        S (count m n) =  (count m (add m n)).
  Proof.
    intros m n.
    simpl.
    rewrite  beqT.
    reflexivity.
  Qed.

  Theorem app_assoc : forall l1 l2 l3 : natlist,
      (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3.
    induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl.
      rewrite <- IHl1'.
      reflexivity.
  Qed.

  Fixpoint rev (l:natlist) :natlist :=
    match l with
    | nil => []
    | h :: t =>  rev t ++ [h]
    end.

  Theorem app_length : forall l1 l2 : natlist,
      length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2.
    induction l1 as [| n l1' IHl1'].
    - reflexivity.
    - simpl.
      rewrite IHl1'.
      reflexivity.
  Qed.
  
  Theorem rev_length: forall l : natlist,
      length (rev l) = length l.
  Proof.
    intros l.
    induction l as [| n l' IHn'].
    - reflexivity.
    - simpl.
      rewrite -> app_length,plus_comm.
      rewrite IHn'.
      reflexivity.
  Qed.

  Theorem app_nil_r : forall l : natlist,
      l ++ [] = l.
  Proof.
    intros l.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl.
      rewrite IHl'.
      reflexivity.
  Qed.


  Theorem rev_app_distr : forall l1 l2: natlist,
      rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
    intros l1 l2.
    induction l1 as [| n l' IHl'].
    - simpl.
      rewrite -> app_nil_r.
      reflexivity.
    - simpl.
      rewrite IHl'.
      rewrite -> app_assoc.
      reflexivity.
  Qed.
  
  Theorem rev_involutive : forall l : natlist,
      rev (rev l) = l.
  Proof.
    intros l.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl.
      rewrite rev_app_distr.
      rewrite IHl'.
      reflexivity.
  Qed.

  Theorem app_assoc4  : forall l1 l2 l3 l4 : natlist,
      l1 ++ ( l2 ++ ( l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4.
    rewrite <- app_assoc.
    rewrite <- app_assoc.
    reflexivity.
  Qed.

  Theorem nonzerosT: forall l1 : natlist,forall n : nat,
        nonzeros(n :: l1) = (nonzeros [n]) ++ (nonzeros l1).
  Proof.
    intros l1 n.
    destruct n as [ | n'].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.
  
  Lemma nonzeros_app : forall l1 l2 :natlist,
      nonzeros ( l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2.
    induction l1 as [| n l IHl'].
    - reflexivity.
    - rewrite -> nonzerosT.
      rewrite -> app_assoc.
      rewrite <- IHl'.
      rewrite <- nonzerosT.
      reflexivity.
  Qed.


  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1 with
    | nil =>
      match l2 with
        | nil => true
        | _ => false
      end
    | h :: t =>
      match l2 with
      | nil => false
      | h2 :: t2 =>
        match beq_nat h h2 with
        | true => beq_natlist t t2
        | false => false
        end
      end
    end.
  
  Theorem beq_natlist_refl : forall l : natlist,
      true = beq_natlist l l.
  Proof.
    intros l.
    induction l as [| n l' IHl'].
    - reflexivity.
    - simpl.
      assert (H: forall k: nat, beq_nat k k =true).
      { intros k.
        induction k as [| k'].
        - reflexivity.
        - simpl.
          congruence.
      }
      rewrite -> H.
      congruence.
  Qed.

  Theorem count_member_nonzero : forall ( s : bag),
      leb 1 (count 1 (1 :: s)) =true.
  Proof.
    intros s.
    induction s as [| n l' IHl'].
    - reflexivity.
    - reflexivity.
  Qed.

  Theorem ble_n_Sn : forall n,
      leb n (S n) =true.
  Proof.
    intros n.
    induction n as [| n' IHn'].
    - reflexivity.
    - simpl.
      rewrite IHn'.
      reflexivity.
  Qed.
  
  Theorem remove_decreases_count: forall (s : bag),
      leb (count 0 (remove_one 0 s)) (count 0 s) = true.
  Proof.
    intros s.
    induction s as [| n l' IH'].
    - reflexivity.
    - destruct n as [| n'].
      + simpl.
        rewrite ble_n_Sn.
        reflexivity.
      + simpl.
        congruence.
  Qed.

  Theorem beq_nn: forall n,
      beq_nat n n =true.
  Proof.
    intros n.
    induction n as [| n'].
    - reflexivity.
    - simpl.
      congruence.
  Qed.

  Theorem bag_count_sum: forall n: nat, forall l : natlist,
        S(count n l) = count n (sum [n] l).
  Proof.
    intros n l.
    induction l as [| n' l' IH'].
    - simpl.
      rewrite beq_nn.
      reflexivity.
    - simpl.
      rewrite beq_nn.
      reflexivity.
  Qed.

  Theorem rev_app : forall (l1 l2:natlist),
      rev l1 = rev l2 -> rev (rev l1) = rev (rev l2).
  Proof.
    intros l1 l2 H.
    rewrite H.
    reflexivity.
  Qed.

  Theorem rev_injective:  forall ( l1 l2 :natlist),
      rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2 H.
    apply rev_app in H.
    rewrite rev_involutive in H.
    rewrite rev_involutive in H.
    congruence.
  Qed.
  
  Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

  Fixpoint nth_error (l:natlist) (n:nat) :natoption :=
    match l with
    | nil => None
    | a:: l' => match beq_nat n 0 with
                | true => Some a
                | false => nth_error l' (pred n)
                end
    end.


  Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
    match l with
    | nil => None
    | a :: l' => if beq_nat n 0 then Some a
                 else nth_error' l' (pred n)
    end.

  Definition option_elim ( d : nat) (o : natoption) : nat :=
    match o with 
    | Some n' => n'
    | None  => d
    end.

  Definition hd_error (l : natlist) : natoption :=
    match l with
    | nil => None
    | h :: t => Some h
    end.

  Theorem option_elim_hd : forall (l:natlist) (default:nat) ,
      hd default l = option_elim default (hd_error l).
  Proof.
    intros l default.
    destruct l as [| h  t].
    - reflexivity.
    - reflexivity.
  Qed.

  End NatList.


  Inductive id : Type :=
  | Id : nat -> id.

  Definition beq_id (x1 x2 : id) :=
    match x1, x2 with
    | Id n1, Id n2 => beq_nat n1 n2
    end.

  Theorem beq_nn : forall n:nat, beq_nat n n=true.
  Proof.
    intros n.
    induction n as [| n'].
    - reflexivity.
    - simpl.
      congruence.
  Qed.
  
  
  Theorem beq_id_refl : forall x, true = beq_id x x.
  Proof.
    intros x.
    destruct x as [n'].
    simpl.
    rewrite beq_nn.
    reflexivity.
  Qed.

  Module PartialMap.
    Export NatList.
    Inductive partial_map : Type :=
    | empty : partial_map
    | record : id -> nat -> partial_map -> partial_map.

    Definition update (d : partial_map) (x : id) (value : nat) : partial_map :=
      record x value d.

    Fixpoint find (x :id) (d : partial_map) : natoption :=
      match d with
      | empty => None
      | record y v d' => if beq_id x y
                         then Some v
                         else find x d'
      end.

    Theorem update_eq :
      forall (d : partial_map) (x: id) (v: nat),
        find x (update d x v) = Some v.
    Proof.
      intros d x v.
      simpl.
      rewrite <- beq_id_refl.
      reflexivity.
    Qed.

    Theorem update_neq:
      forall (d : partial_map) ( x y :id) (o : nat),
        beq_id x y = false -> find x (update d y o) = find x d.
    Proof.
      intros d x y o H.
      simpl.
      rewrite H.
      reflexivity.
    Qed.

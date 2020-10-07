Require Export basics.

Inductive boollist : Type :=
| bool_nil :boollist
| bool_cons : bool -> boollist -> boollist.

Inductive list (X: Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Fixpoint repeat (X: Type) (x : X) (count : nat) :list  X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Fixpoint repeat' X x  count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat' _ x count')
  end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Fixpoint repeat'' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat'' x count')
  end.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) :nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Notation "x :: y" := (cons x y)
                       (at level  60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y"  :=  (app x y)
                         (at level 60, right associativity).

Theorem app_nil_r : forall (X:Type), forall l:list X,
      l ++ [] = l.
Proof.
  intros x l.
  induction l as [| h t IHt].
  - reflexivity.
  - simpl.
    rewrite IHt.
    reflexivity.
Qed.

Theorem app_assoc : forall A (l m n: list A),
    l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [| h t IHl].
  - reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
    length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [| h t IHl].
  - reflexivity.
  - simpl.
    rewrite -> IHl.
    reflexivity.
Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X),
    rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [| h t IHl1].
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl.
    rewrite IHl1, app_assoc.
    reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
      rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite rev_app_distr, IH.
    reflexivity.
Qed.

Inductive prod (X Y: Type) : Type :=
| pair : X -> Y -> prod X Y.
Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | ( x , y) => x
  end.

Definition snd {X Y : Type} ( p : X * Y) : Y :=
  match p with
  | (x , y) => y
  end.

Fixpoint combine { X Y : Type} (lx : list X) (ly : list Y)
  : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x , y) :: (combine tx ty)
  end.

Fixpoint split {X Y: Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => (@nil X , @nil Y)
  | h :: t => ( (app [ (fst h) ] (fst (split t))) , (app [ (snd h) ] (snd (split t))))
  end.

Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X} _.
Arguments None {X}.


Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | [] =>None
  | a :: l' => if beq_nat n 0 then  Some a else nth_error l' (pred n)
  end.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | [] => None
  | h :: t => Some h
  end.

Fixpoint filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t) else filter test t
  end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) (leb 8 n)) l.

Definition partition {X:Type} (test : X -> bool) (l : list X) : list X * list X :=
  ( (filter test l) , (filter (fun x => negb (test x)) l)).

Fixpoint map {X Y : Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Theorem map_app_distr : forall (X Y : Type) (f : X -> Y)(l1 l2 :list X),
    map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros X Y f l1 l2.
  induction l1 as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
    map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction  l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite map_app_distr, IH.
    reflexivity.
Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l : list X) : (list Y) :=
  match l with
  | [] =>  []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Fixpoint fold {X Y:Type} (f: X -> Y -> Y)(l :list X)(b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Definition constfun {X:Type} (x: X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Definition fold_length {X: Type} (l :list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l : list X),
    fold_length l = length l.
Proof.
  intros X l.
  induction  l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite <- IH.
    reflexivity.
Qed.

Definition fold_map {X Y :Type} (f : X -> Y) (l : list X) : list Y :=
  (fold (fun a b => (f a) :: b) l []).

Definition prod_curry {X Y Z : Type}
           ( f : X * Y -> Z) (x : X)(y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z :Type}
           (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Theorem uncurry_curry : forall  (X Y Z : Type) (f : X -> Y -> Z) x y,
    prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  unfold prod_uncurry, prod_curry.
  reflexivity.
Qed.


Theorem pairT: forall (X Y : Type) (p : X * Y),
    (fst p, snd p) = p.
Proof.
  intros X Y p.
  destruct p as [h t].
  reflexivity.
Qed.


Theorem curry_uncurry: forall (X Y Z: Type) (f : (X * Y) -> Z) (p: X * Y),
    prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  unfold prod_uncurry, prod_curry.
  rewrite pairT.
  reflexivity.
Qed.

Module Church.
  Definition nat := forall X : Type, (X -> X) -> X -> X.

  Definition one : nat :=
    fun (X : Type) (f: X -> X) (x : X) => f x.

  Definition two : nat :=
    fun (X : Type) (f: X -> X) (x : X) => f (f x).

  Definition three : nat :=
    fun (X: Type) (f: X -> X) (x : X) => f ( f ( f x)).
  
  Definition zero : nat :=
    fun (X: Type) (f: X -> X) (x : X) => x.

  Definition succ (n : nat) : nat :=
    fun (X:Type) (f: X -> X) (x :X)=> f (n X f x).

  Definition plus (n m : nat) : nat :=
    fun (X:Type) (f: X -> X) (x : X) => (n X f (m X f x)).

  Definition mult ( n m : nat) : nat :=
    fun (X:Type) (f: X -> X) (x: X) => (n X (m X f) x).

  Definition exp (n m: nat) : nat :=
    fun (X:Type) (f: X -> X) (x: X) =>
      (m (X->X) (fun (y : X->X) => (fun (z: X) => (n X y z))) f) x.

  End Church.


  
    
 
    
  
    





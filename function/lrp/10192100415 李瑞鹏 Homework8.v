Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | 0,    0     =>  true
  | 0,    _     =>  false
  | _,    0     =>  false
  | S n', S m'  =>  eqb n' m'
  end.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Fixpoint even (n:nat) : bool :=
  match n with
  | 0        => true
  | S 0      => false
  | S (S n') => even n'
  end.
Definition odd (n : nat) : bool :=
  if even n then false else true.

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
Arguments nil {X}.
Arguments cons {X}.
Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Fixpoint filter { X : Type } (test : X -> bool) (l : list X) : list X :=
  match l with
  | []      =>  []
  | h :: t  =>
    if test h then h :: (filter test t)
    else filter test t
  end.
Fixpoint map { X Y : Type } (f : X -> Y) (l : list X) :=
  match l with
  | []      =>  []
  | h :: t  =>  (f h) :: (map f t)
  end.
Fixpoint fold { X Y : Type } (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | []      =>  b
  | h :: t  =>  f h (fold f t b)
  end.


(******************************************************************
 **************************** 作业题 1 *****************************
 ******************************************************************)
Fixpoint flat_map { X Y : Type } (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | []      =>  []
  | h :: t  =>  (f h) ++ (flat_map f t)
  end. 
Example test_flap_map1:
  flat_map (fun n => [n; n; n]) [1; 5; 4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(******************************************************************
 **************************** 作业题 2 *****************************
 ******************************************************************)
Definition changelist (L : list nat) : list nat :=
  map (fun n => if even n then n * 2 else n * 3) L.
Example test_changelist:
  changelist [1; 2; 3; 4; 5; 6] = [3; 4; 9; 8; 15; 12].
Proof. reflexivity. Qed.

(******************************************************************
 **************************** 作业题 3 *****************************
 ******************************************************************)
Definition add (a b : nat) : nat := a + b.
Definition sumPair (L : list nat) : nat * nat :=
  (fold add (filter odd L) 0,
   fold add (filter even L) 0).
Example test_sumPair:
  sumPair [1; 2; 3; 4; 5] = (9, 6).
Proof. reflexivity. Qed.

(******************************************************************
 **************************** 作业题 4 *****************************
 ******************************************************************)
(** 生成列表 [0; 1; 2; ...; n] *)
Fixpoint list_zero2n (n : nat) : list nat :=
  match n with
  | 0     =>  [0]
  | S n'  =>  (list_zero2n n') ++ [n]
  end.
(** 检查 a ∈ L *)
Fixpoint in_list (a : nat) (L : list nat) : bool :=
  match L with
  | []      =>  false
  | h :: t  =>
    if h =? a then true
    else in_list a t
  end.
(** A ∩ B *)
Definition inter (A : list nat) (B : list nat) : list nat :=
  filter (fun a => in_list a B) A.
(** 多集合交集 *)
Definition bigInter (L : list (list nat)) (n : nat) : list nat :=
  fold inter L (list_zero2n n).
Example test_bigInter:
  bigInter [[1; 3; 5]; [2; 3; 7; 6; 5]; [3; 9; 8; 5]] 10 = [3; 5].
Proof. reflexivity. Qed.
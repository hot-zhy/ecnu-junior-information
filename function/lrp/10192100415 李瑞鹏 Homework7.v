(***** 公共基础定义 *****)
Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | 0,    0     =>  true
  | 0,    _     =>  false
  | _,    0     =>  false
  | S n', S m'  =>  eqb n' m'
  end.
Fixpoint ltb (n m : nat) : bool :=
  match n, m with
  | 0,    0     =>  false
  | 0,    _     =>  true
  | _,    0     =>  false
  | S n', S m'  =>  ltb n' m'
  end.
Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Fixpoint even (n:nat) : bool :=
  match n with
  | 0        => true
  | S 0      => false
  | S (S n') => even n'
  end.



(***** 非泛型列表定义 *****)
Module NATLIST.
Inductive natprod : Type :=
  | pair (n1 n2 : nat).
Notation "( x , y )" := (pair x y).
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y) (right associativity, at level 60).
Inductive natoption : Type :=
  | Some (n : nat)
  | None.


(******************************************************************
 **************************** 作业题 1 *****************************
 ******************************************************************)
Fixpoint max (L : natlist) : natoption :=
  match L with
  | nil     =>  None
  | h :: t  =>
    match max t with
    | None    =>  Some h
    | Some n  =>  if n <? h then Some h else Some n
    end
  end.

(******************************************************************
 **************************** 作业题 2 *****************************
 ******************************************************************)
Fixpoint maxPair (L : natlist) : natprod :=
  match L with
  | nil     =>  (0, 0)
  | h :: t  =>
    match maxPair t with
    | (x, y)  =>
      if even h then
        if y <? h then (x, h) else (x, y)
      else
        if x <? h then (h, y) else (x, y)
    end
  end.
Example test_maxPair1: maxPair [1;2;5;4;8;10;3] = (5, 10).
Proof. reflexivity. Qed.
Example test_maxPair2: maxPair [2;4] = (0, 4).
Proof. reflexivity. Qed.
End NATLIST.

(***** 泛型列表定义 *****)
Module POLYLIST.
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
Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l.
  induction l as [| ln l' IHl'].
  - reflexivity.
  - simpl.
    rewrite IHl'.
    reflexivity.
Qed.

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l as [| ln l' IHl'].
  - reflexivity.
  - simpl.
    rewrite IHl'.
    reflexivity.
Qed.
    
(******************************************************************
 **************************** 作业题 3 *****************************
 ******************************************************************)
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof. 
  intros X l1 l2.
  induction l1 as [| n l1' IHl1'].
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl.
    rewrite IHl1'.
    rewrite app_assoc.
    reflexivity.
Qed.

(******************************************************************
 **************************** 作业题 4 *****************************
 ******************************************************************)
Theorem rev_involutive: forall X : Type , forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| n l' IHl'].
  - reflexivity.
  - simpl.
    rewrite rev_app_distr.
    rewrite IHl'.
    reflexivity.
Qed.
End POLYLIST.
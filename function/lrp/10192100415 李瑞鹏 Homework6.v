(***** 前置定义 *****)
Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | 0,    0     =>  true
  | 0,    _     =>  false
  | _,    0     =>  false
  | S n', S m'  =>  eqb n' m'
  end.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Definition bag := natlist.
Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
    match h =? v with
    | true => S(count v t)
    | false => count v t
    end
  end.

Fixpoint count' (v:nat)(s:bag):nat:=
  match s with
  |nil=>0
  |h::t=>
    match h=?v with
      |true=>S (count' v t)
      |false=> count' v t
      end 
  end.
(*******************)


(***** 作业 1 *****)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | nil,    _       =>  l2
  | _,      nil     =>  l1
  | h1::t1, h2::t2  =>  h1 :: (h2 :: (alternate t1 t2))
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.
(*****************)


(* zhi bao liu the first
 *)
(***** 作业 2 *****)
Fixpoint remove_repeat (l : natlist) : natlist :=
  match l with
  | nil   =>  nil
  | h::t  =>
    match count h t with
    | 0 =>  h :: (remove_repeat t)
    | _ =>  remove_repeat t
    end
  end.
Definition inter (l1 l2 : bag) : bag :=
  remove_repeat (l1 ++ l2).
(*****************)
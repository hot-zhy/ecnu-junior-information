(* Final Exam --- February 26, 2023  
You are allowed to search and use any property provided in the 
standard library of Coq. *)

Require Import Nat.
Require Import List.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. 
Qed.

Theorem mult_1_r : forall n:nat,
  n = n * 1.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. 
Qed.

(* 1. Prove the following fact about natural numbers by induction. *)
    
Lemma mul_2_r : forall  n : nat, 
  n * 2 = n + n.
Proof.
  induction n.
  - reflexivity.
  - simpl. apply f_equal. rewrite<- plus_n_Sm. apply f_equal. apply IHn.
Qed. 


(* 2. Define a function called cubic so that (cubic n) returns true 
iff n is a cubic number, i.e. n = n' * n' * n' for some n'. *)

Fixpoint find_cubic_num (n target:nat):nat:=
  if n*n*n =? target then n
  else
  match n with
  |0=>0
  |S n'=>find_cubic_num n' target
  end.

Definition cubic (n : nat) : bool :=
  match n with
  | 0 => true
  | S n' => if ((find_cubic_num n n) * (find_cubic_num n n)* (find_cubic_num n n) =? n) then true
            else false
  end.



Example cubic_test1 : cubic 8 = true.
Proof. reflexivity. Qed.

Example cubic_test2 : cubic 25 = false.
Proof. reflexivity. Qed.


(* 3. Let two sequences of numbers F1(n) and F2(n) be given as follows.
   F1(0) = 1
   F1(n) = 2 * F1(n-1)   for n > 0.

   F2(0) = F2(1) = 1
   F2(n+2) = F2(n) + F2(n+1)    for n >= 0.

Define the function Seq such that (Seq n) returns the sequence

[F1(0); F2(0); F1(1); F2(1); ... ; F1(n); F2(n)].
*)


Fixpoint get_F1 (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => 2 * (get_F1 n')
  end.

Fixpoint get_F2 (n : nat) : nat :=
  match n with
  | 0 => 1
  | 1 => 1
  | S n' => get_F2 n' + get_F2 (n' - 1)
  end.

Fixpoint Seq (n: nat) : list nat :=
  match n with
  | 0 => [1; 1]
  | S n' => Seq n' ++ [get_F1 n; get_F2 n]
  end.


Example Seq_test :  Seq 5 = [1; 1; 2; 1; 4; 2; 8; 3; 16; 5; 32; 8].
Proof. reflexivity. Qed.



(* 4. Let lt be the predicate such that (lt n m) holds iff n is strictly
less than m. Prove the following theorem about lt. *)

Inductive lt : nat -> nat -> Prop :=
 | lt1 : forall n, lt n (S n)
 | lt2 : forall n m, lt n m -> lt n (S m).

Theorem lt_add : forall n m p q, lt n m -> lt p q -> lt (n+p) (m+q).
Proof. 
  intros. destruct H0.
  - rewrite<- plus_n_Sm. apply lt2.  
(* 
Theorem auxility :forall p q m,lt p q->lt (p+m) (q+m).
Proof.
  intros. destruct H.
  + apply lt1.
  + apply   *)
(* 
 




(* 5. Write a function (transform):

      transform : list nat -> list (list nat )

   which transforms a list into a list of 3 sublists. The first sublist
   contains all the odd numbers in the original list; the second sublist contains 
   all the numbers divisible by 3 in the original list; the last sublist contains 
   all the other numbers in the original list. 
   The order of elements in the three sublists should be the same as their 
   order in the original list. 

   Hint: You may use the Coq function (filter).

*)

(* 判断是否能被3整除 *)
Fixpoint div3 (n:nat):bool:=
  match n with 
  |O=>true
  |S n'=>match (leb n' 1) with
        |true=>false
        |false=>div3(n'-2)
        end
  end.

Definition transform(l:list nat):list (list nat):=
  match l with
  |[]=>[[];[];[]]
  |h::t=>[filter (fun n=> odd n) l;filter (fun n=> (div3 n)) l; filter (fun n=>andb (negb (odd n)) (negb (div3 n))) l]
  end.


Example transform_test: 
transform [3;7;6;9;4;5;16;14;15] = [[3; 7; 9; 5; 15]; [3; 6; 9; 15]; [4; 16; 14]].
Proof. reflexivity. Qed.


(* 6. Prove the following fact about excluded middle. *)

Theorem de_morgan : 
   (forall P, P \/ ~P) -> (forall P Q, ~(~P \/ ~Q) -> P /\ Q).
Proof.
  intros H P Q HPQ.
  unfold not in HPQ.
  assert (P\/~P) as HP. {apply H. }
  assert (Q\/~Q) as HQ. {apply H. }
  destruct HP.
  - destruct HQ.
    + split. apply H0. apply H1.
    + destruct HPQ. right. apply H1.
  - destruct HPQ. left. apply H0.
Qed.



(* 7. Consider the following type btree about binary trees.
Define a function to give an inorder traversal of the tree and collect
all the odd numbers in a list. 
*)

Inductive btree : Set :=
 | leaf : nat -> btree 
 | node : nat -> btree -> btree -> btree.

(* 中序遍历 *)

Fixpoint inorder (t: btree) : list nat :=
  match t with 
  |leaf n => if odd n then [n] else []
  |node n l r => if odd n then inorder l ++ [n] ++ inorder r
                else inorder l ++ inorder r
  end.
Example bt_test : inorder (node 5 (node 1 (leaf 0) (node 3 (leaf 2) (leaf 4))) 
                                   (node 9 (node 7 (leaf 6) (leaf 8)) (leaf 10))) 
                   = [1; 3; 5; 7; 9].
Proof. reflexivity. Qed.



(* 8. The following definitions specify the abstract syntax of
    some arithmetic expressions and an evaluation function. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

(* Suppose we define a function that takes an arithmetic expression 
   and slightly simplifies it, changing every occurrence of [e + 0],
   [e - 0], or [1 * e] into [e], and [0 * e] into [0]. *)

Fixpoint optimize (a:aexp) : aexp :=
  match a with
  |ANum n => ANum n
  |APlus e1 (ANum 0) => optimize e1
  |APlus e1 e2 => APlus (optimize e1) (optimize e2)
  |AMinus e1 (ANum 0) => optimize e1 
  |AMinus e1 e2 => AMinus (optimize e1) (optimize e2)
  |AMult e1 (ANum 0) => ANum 0
  |AMult e1 (ANum 1) => optimize e1
  |AMult e1 e2 => AMult (optimize e1) (optimize e2)
  end.

(* Prove the following theorem that states the correctness of the 
optimization with respect to the evaluation of arithmetic expressions. *)


Theorem optimize_sound: forall a,
  aeval (optimize a) = aeval a.
  Proof. 
    intros a. induction a as [n | a1 IHa1 a2 IHa2| a1 IHa1 a2 IHa2| a1 IHa1 a2 IHa2].
  - simpl. reflexivity.
  - destruct a2.
     + destruct n. 
       * simpl. rewrite plus_comm. simpl. rewrite IHa1. reflexivity.
       * simpl. rewrite IHa1. reflexivity.
     + simpl in IHa2. simpl. rewrite IHa2. rewrite IHa1. reflexivity.
     + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
     + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
  - destruct a2.
     + simpl. destruct n.
       * rewrite PeanoNat.Nat.sub_0_r with (n := aeval a1). apply IHa1. 
       * simpl. rewrite IHa1. reflexivity.
     + simpl in IHa2. simpl. rewrite IHa2. rewrite IHa1. reflexivity.
     + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
     + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
  - destruct a2.
     + destruct n eqn:En. 
       * simpl. symmetry. apply mult_0_r.
       * destruct n0. simpl. rewrite <- mult_1_r. apply IHa1. simpl. rewrite IHa1. reflexivity.
     + simpl in IHa2. simpl. rewrite IHa2. rewrite IHa1. reflexivity.
     + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
     + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
 Qed.



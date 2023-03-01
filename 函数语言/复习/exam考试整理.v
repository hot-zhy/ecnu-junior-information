(* Final Exam (Paper A) --- January 4, 2021 *)
Require Import Nat.
Require Import List.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition admit {T: Type} : T.  Admitted.

(* 1. Prove the following fact about natural numbers. 
Hint: You may search and use some properties about the plus function 
in the standard library of Coq. *)

Lemma mul_3_r : forall n : nat, n * 3 = n + n + n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm.
    rewrite IHn'. simpl. reflexivity.
Qed.

(* 2. Complete the following definition so that (div2021 n) returns true 
iff n is divisible by 2021. 
Hint: You may find the leb function useful. *)
Print leb.

Fixpoint div2021 (n : nat ) : bool :=
  match n with
  |O => true
  |S n' => match (leb n' 2019) with
           |true => false
           |false => div2021 (n'-2020)
           end
  end.

Example div2021_test1: div2021 4042 = true.
Proof. reflexivity. Qed.

Example div2021_test2: div2021 2027 = false.
Proof. reflexivity. Qed.


(* 3. Define a function createList such that (createList n) returns 
a list of numbers in the form: [n;(n-1);...;2;1;2;...;(n-1);n], for any n > 0. *)

Fixpoint createList (n : nat) : list nat :=
  match n with
  |O => []
  |S O => [1]
  |S n' => [n] ++ (createList n') ++ [n]
  end.  

Example createList_test : createList 6 = [6;5;4;3;2;1;2;3;4;5;6].
Proof. reflexivity. Qed.



(* 4. Let oddn and evenn be the predicates that test whether a given number
is odd or even. Show that the sum of an odd number with an even number is odd. *)

Inductive oddn : nat -> Prop :=
 | odd1 : oddn 1
 | odd2 : forall n, oddn n -> oddn (S (S n)).

Inductive evenn : nat -> Prop :=
 | even1 : evenn 0
 | even2 : forall n, evenn n -> evenn (S (S n)).

Theorem odd_add : forall n m, oddn n -> evenn m -> oddn (n + m).
Proof.
  intros n m H1 H2.
  induction H1 as [| n' H1' IHn']. 
  -simpl. induction H2. apply odd1. apply odd2. apply IHevenn.
  -simpl. apply odd2. apply IHn'.
Qed. 

(* 5. Write a function (partition):

      partition : list nat -> list (list nat )

   which partitions a list into a list of 3 sublists. The first sublist
   contains all even numbers in the original list. The second sublist 
   contains all odd numbers divisible by 5 in the original list. The last 
   sublist contains all other elements. The order of elements in the
   three sublists should be the same as their order in the original list. 

   Hint: You may use the Coq function (filter).
*)

Fixpoint div5 (n : nat ) : bool :=
  match n with
  |O => true
  |S n' => match (leb n' 3) with
           |true => false
           |false => div5 (n'-4)
           end
  end.

Definition partition (l : list nat) : list (list nat) :=
  match l with
  |[] => [[];[];[]]
  |h :: t => [filter even l;filter div5 l;filter (fun n => andb (negb (even n) )(negb (div5 n)) ) l ]
  end.

Example partition_test: partition [1;2;3;9;4;5;6;15;8] = [[2;4;6;8]; [5;15]; [1;3;9]].
Proof. reflexivity. Qed.



(* 6. Prove the following fact about excluded middle. *)

Theorem excluded_middle : 
  (forall P Q : Prop, (P -> Q) -> (~P \/ Q)) -> (forall P, P \/ ~P).
Proof.
  intros. right. unfold not. unfold not in H. Admitted.
  



(* 7. Let a sequence of numbers F(n) be given as follows.
   F(0) = 0
   F(n) = F(n-1) + 2 * n   for n > 0.

Define the function Seq such that (Seq n) returns the sequence

[0; F(1); 2; F(3); 4; F(5); ... ; 2n; F(2n + 1)].
*)

Fixpoint F (n: nat) :  nat :=
  match n with
  |O => 0
  |S n' => F n' + 2*n
  end.

Fixpoint Seq (n: nat) : list nat :=
  match n with
  |0 => [0;F 1]
  |S n' => Seq n' ++ [2*n;F (2*n+1)]
  end.  

Example Seq_test :  Seq 5 = [0; 2; 2; 12; 4; 30; 6; 56; 8; 90; 10; 132].
Proof. reflexivity. Qed.



(* 8. Consider the following type:

Inductive btree : Set :=
 | leaf : nat -> btree 
 | node : nat -> btree -> btree -> btree.

Define a function taking as argument a tree t: btree and returning 
the sum of all numbers occurring in the tree. *)

Inductive btree : Set :=
 | leaf : nat -> btree 
 | node : nat -> btree -> btree -> btree.

Fixpoint sum (t: btree) : nat :=
  match t with
  |leaf n => n
  |node n x y => n + (sum x) + (sum y)
  end.  

Example bt_test : sum (node 5 (node 1 (leaf 0) (node 3 (leaf 2) (leaf 4))) 
                              (node 9 (node 7 (leaf 6) (leaf 8)) (leaf 10))) 
                  = 55.
Proof. reflexivity. Qed. 



(* 9. Write in Coq a function that rotates a list. Namely, the call to
(rotate l) returns a new list that is the same as l except that the last 
element of l instead appears as the first element of the new list. *)

Fixpoint rotate (l : list nat) : list nat :=
 match l with
 |[] => []
 |[h] => [h]
 | h :: t => rotate t ++ [h]
 end. 

Compute rotate [1;2;3;4;5].

Example rotate_test : rotate [1;2;3;4;5] = [5;1;2;3;4].
Proof.  Admitted.



(* 10. The following definitions specify the abstract syntax of
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
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

(* Suppose we define a function that takes an arithmetic expression 
   and slightly simplifies it, changing every occurrence of [e + 0]
   and [e - 0] into just [e], and [e * 1] into [e]. *)

Fixpoint optimize (a:aexp) : aexp :=
  match a with
  |ANum n => ANum n
  |APlus e1 (ANum 0) => optimize e1
  |APlus e1 e2 => APlus (optimize e1) (optimize e2)
  |AMinus e1 (ANum 0) => optimize e1 
  |AMinus e1 e2 => AMinus (optimize e1) (optimize e2)
  |AMult e1 (ANum 1) => optimize e1
  |AMult e1 e2 => AMult (optimize e1) (optimize e2)
  end.

(* Prove the following theorem that states the correctness of the 
optimization with respect to the evaluation of arithmetic expressions. *)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem minus_0 : forall n : nat,
   n = n - 0.
Proof.
  intro n. induction n as [|n' IHn'].
  -reflexivity.
  -simpl. reflexivity.
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

Theorem optimize_mult1_sound: forall a,
  aeval (optimize a) = aeval a.
Proof. 
  intros a. induction a.
  -reflexivity.
  -destruct a2 eqn:Ea1.
   + destruct n eqn:En.
    *simpl. rewrite plus_comm. simpl. apply IHa1.
    *simpl. rewrite IHa1. reflexivity.
   +simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
   +simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
   +simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
  -destruct a2 eqn:Ea2.
   + destruct n eqn:En.
    *simpl. rewrite <- minus_0. simpl. apply IHa1.
    *simpl. rewrite IHa1. reflexivity.
   +simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
   +simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
   +simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
  -destruct a2 eqn:Ea3.
   + destruct n eqn:En.
    *simpl. rewrite mult_0_r. rewrite mult_0_r. reflexivity.
    *destruct n0. { simpl. rewrite IHa1. rewrite <- mult_1_r. reflexivity. }
     {simpl.  rewrite IHa1. reflexivity. }
   +simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
   +simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
   +simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
Qed.
 

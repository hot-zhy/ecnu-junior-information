(* Final Exam (Paper A) --- January 4, 2021 *)
Require Import Nat.
Require Import List.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition admit {T: Type} : T.  Admitted.

(* 1. Prove the following fact about natural numbers. 
Hint: You may search and use some properties about the plus function 
in the standard library of Coq. *)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - rewrite <- plus_n_O.  reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Lemma mul_3_r : forall n : nat, n * 3 = n + n + n.
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn.
    rewrite (plus_comm (n + S n) (S n)). simpl.
    rewrite (plus_comm n (S n)). simpl.
    rewrite (plus_comm n (S(n + n))). simpl.
    reflexivity.
Qed.

(* 2. Complete the following definition so that (div2021 n) returns true 
iff n is divisible by 2021. 
Hint: You may find the leb function useful. *)

Fixpoint div2021 (n : nat ) : bool :=
  match n with
  | O => true
  | S n' => 
    match (leb n 2020) with
    | true => false
    | false => div2021 (n' -2020)
    end
  end.

Example div2021_test1: div2021 4042 = true.
Proof. reflexivity. Qed.

Example div2021_test2: div2021 2027 = false.
Proof. reflexivity. Qed.


(* 3. Define a function createList such that (createList n) returns 
a list of numbers in the form: [n;(n-1);...;2;1;2;...;(n-1);n], for any n > 0. *)

Fixpoint createList1 (n : nat) : list nat :=
  match n with
  | 0 => []
  | 1 => []
  | S n' => S n' :: (createList1 n')
  end.

Definition createList (n : nat) : list nat :=
  match n with
  | 0 => []
  | 1 => [1]
  | n => (createList1 n) ++ [1] ++ (rev (createList1 n))
  end.

Example createList_test : createList 6 = [6;5;4;3;2;1;2;3;4;5;6].
Proof. simpl. reflexivity. Qed.



(* 4. Let oddn and evenn be the predicates that test whether a given number
is odd or even. Show that the sum of an odd number with an even number is odd. *)

Inductive oddn : nat -> Prop :=
 | odd1 : oddn 1
 | odd2 : forall n, oddn n -> oddn (S (S n)).

Inductive evenn : nat -> Prop :=
 | even1 : evenn 0
 | even2 : forall n, evenn n -> evenn (S (S n)).


Theorem odd_add1: forall n, oddn n -> evenn ( S n ).
Proof.
  intros.
  induction H.
  - apply even2. apply even1.
  - apply even2. apply IHoddn.
Qed.

Theorem odd_add2: forall n, evenn n -> oddn ( S n ).
Proof.
  intros.
  induction H.
  - apply odd1.
  - apply odd2. apply IHevenn.
Qed.

Theorem odd_add3: forall n m, evenn n -> evenn m -> evenn (n + m).
Proof.
  intros.
  induction H.
  - apply H0.
  - simpl. apply even2. apply IHevenn.
Qed.

Theorem odd_add : forall n m, oddn n -> evenn m -> oddn (n + m).
Proof.
  intros.
  assert(H1: evenn (S n + m )).
  { apply (odd_add3 (S n) m). apply odd_add1. apply H. apply H0. }
  simpl in H1. inversion H1. apply odd_add2. apply H3.
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

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Fixpoint div5 (n : nat ) : bool :=
  match n with
  | O => true
  | S n' => 
    match (leb n 4) with
    | true => false
    | false => div5 (n' -4)
    end
  end.

Definition partition (l : list nat) : list (list nat) :=
  [filter evenb l;
   filter (fun n => andb (negb (evenb n)) (div5 n)) l;
   filter (fun n => andb (negb (evenb n)) (negb (div5 n))) l].

Example partition_test: partition [1;2;3;9;4;5;6;15;8] = [[2;4;6;8]; [5;15]; [1;3;9]].
Proof. reflexivity. Qed.

(* 6. Prove the following fact about excluded middle. *)

(*我们在 Logic.v 中了解到，(forall P, P \/ ~P) 是无法被 Coq 所证明的
而这道题目中，我们发现前提和结论是相互独立的。而且前提必为 True，所以我们必须要证明
结论是 True 的，这里我们引入一条公理来帮助证明*)

Axiom double_negation_elimination : forall P:Prop,
  ~~P -> P.

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros P H.
  apply H.
  right.
  intros.
  apply H.
  left.
  apply H0.
Qed.

Theorem excluded_middle:
(forall P Q:Prop,(P->Q)->(~P\/Q))->
(forall P,P\/~P).
Proof.
  intros.
  apply double_negation_elimination.
  apply excluded_middle_irrefutable.
Qed.
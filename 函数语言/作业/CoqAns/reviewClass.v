Require Import Nat.
Require Import List.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).



(* 1. Define a function createList such that (createList n) returns 
a list of n numbers from 1 to n. *)
Fixpoint createList (n:nat):list nat:=
  match n with
  |0=>nil
  |S n'=>(createList n')++[n]
  end.


Example test1 : createList 5 = [1;2;3;4;5].
(* FILL IN HERE *)
Proof. reflexivity. Qed.


(* 2. Complete the following definition so that (last n l) holds iff
 n is the last element of the list l. *)

Inductive last (n:nat):list nat->Prop:=
  |lbase:last n [n]
  |lstep :forall m l,last n l->last n (m::l).


Example test2 : last 5 [1;2;3;4;5].
Proof. (* FILL IN HERE *)
  apply lstep. apply lstep. apply lstep. apply lstep.
  apply lbase.
Qed.

Example test3 : forall n, ~ (last n [ ]).
Proof. (* FILL IN HERE *)
intros n H.  inversion H. Qed.


(* 3. Prove that the excluded middle axiom implies the double negation axiom. *)
Theorem double_negation : 
  (forall P, P \/ ~P) -> (forall P, ~~P <-> P).
Proof.  intros em P. split.
  - intro NN. assert (P\/~P) as H.
    {apply em. }
    inversion H as [H1|H2].
    + apply H1.
    + apply NN in H2. contradiction.
  -  intro. unfold not. intro. apply H0. apply H. Qed.
(* 任何能够被以下策略的组合解决的待证目标，都能用 auto 来解决：
intros
apply（默认使用局部上下文中的前提）。
使用 auto 一定是“安全”的，它不会失败，也不会改变当前证明的状态： auto 要么完全解决它，要么什么也不做。 *)
(* FILL IN HERE *)
Theorem double_negation' : 
  (forall P, P \/ ~P) -> (forall P, ~~P <-> P).
Proof. intros em P. split. 
  - intro NN. assert (P \/  ~P) as H.
    { apply em. }
    destruct H as [H1 | H2].
     + apply H1.
     + apply NN in H2. contradiction.
  - auto. 
Qed.


(* 4. Define the "less than or equal to" relation and show its transitivity. *)
Inductive le:nat->nat->Prop:=
  |le_n:forall n,le n n
  |le_S:forall m n ,le m n->le m (S n).


Example test5 : le 3 5.
Proof.  (* FILL IN HERE *)
apply le_S. apply le_S. apply le_n. Qed.


(* !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
Example test6 : ~ (le 2 1).
Proof. (* FILL IN HERE *)
intro H. inversion H. inversion H2. Qed. 

Example le_transitive : forall m n p,
  le m n -> le n p -> le m p.
Proof. 
  intros. induction H0.
  - apply H.
  - apply IHle in H. apply le_S. apply H. Qed.
Example le_transitive' : forall m n p,
  le m n -> le n p -> le m p.
Proof. 
  intros m n p Hmn Hnp. induction Hnp.
  - assumption. 
  - apply IHHnp in Hmn. apply le_S. assumption.
Qed.


(* 5. Consider the following function f. What does this function do? *)
Fixpoint f (l: list nat) : list nat :=
   match l with
   | nil => l
   | h :: t => f t ++ [h]
   end.

Lemma app_nil_r : forall l : list nat,
  l ++ [] = l.
Proof. intro l. induction l as [ | h t IHt].
 - reflexivity.
 - simpl. rewrite IHt; reflexivity.
Qed.
 

Lemma f_app : forall l1 l2 : list nat,
  f (l1 ++ l2) = (f l2) ++ (f l1).
Proof. intros l1 l2. induction l1 as [| h t IHt].
 - simpl. rewrite app_nil_r. reflexivity.
 - simpl. rewrite IHt. rewrite app_assoc. reflexivity.
Qed.

(* Show that function f has the following property. *)
Theorem double_f : forall l : list nat,
  f (f l) = l.
Proof. (* FILL IN HERE *)
 intro l. induction l.
 - reflexivity.
 - simpl. rewrite f_app. simpl. rewrite IHl. reflexivity.
Qed.


(* 6. Consider the following type:

Inductive btree : Set :=
 | leaf : btree 
 | node : nat->btree->btree->btree.

Define a function taking as argument a natural number n
and a tree t: btree and returning true iff t has (at least) 
an occurrence of n. 

Hint: You may use the function (eqb n m) which returns true iff the two natural
numbers n and m are equal.
*)

(* Inductive bt {X : Type} : Type :=
  | lf : bt
  | nd : X -> bt -> bt -> bt. *)

Inductive btree : Set :=
 | leaf : btree 
 | node : nat->btree->btree->btree.

Fixpoint occur (n:nat)(t:btree):bool:=
  match t with
  |leaf =>false
  |node nd t1 t2=>if eqb n nd
                  then true
                  else if occur n t1
                    then true
                    else occur n t2
  end.


Example test10 : occur 2 (node 1 leaf (node 3 (node 2 leaf leaf) leaf)) = true.
(* FILL IN HERE *) 
Proof. reflexivity. Qed.


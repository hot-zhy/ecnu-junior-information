(****************** Prerequisites *****************)
From Coq Require Import Setoids.Setoid.
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

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(**************************************************
 ******************* Question 1 *******************
 **************************************************)
Theorem dist_exists_or: forall (X : Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [x [HP | HQ]].
    + left. exists x. apply HP.
    + right. exists x. apply HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. apply HP.
    + exists x. right. apply HQ.
Qed.

(**************************************************
 ******************* Question 2 *******************
 **************************************************)
Inductive CE : nat -> nat -> Prop :=
  | CE_base: CE 0 2
  | CE_inductive (n m : nat) (H : CE n m): CE (S (S n)) (S (S m)).
Example test_CE: CE 4 6.
Proof.
  apply CE_inductive. apply CE_inductive. apply CE_base.
Qed.

(**************************************************
 ******************* Question 3 *******************
 **************************************************)
Lemma CE_inversion: forall (n m : nat),
  CE n m -> (n = 0 /\ m = 2) \/ (exists n' m', n = S (S n') /\ m = S (S m') /\ (CE n' m')).
Proof.
  intros n m H.
  destruct H as [| n' m' H'].
  - left. split.
    + reflexivity.
    + reflexivity.
  - right.
    exists n'. exists m'.
    split.
    + reflexivity.
    + split.
      * reflexivity.
      * apply H'.
Qed.

Theorem CE_SS: forall n m,
  CE (S (S n)) (S (S m)) -> CE n m.
Proof.
  intros n m H.
  apply CE_inversion in H.
  destruct H as [H | H].
  - destruct H as [H1 H2].
    discriminate H1.
  - destruct H as [n'].
    destruct H as [m'].
    destruct H as [Hn [Hm HCE]].
    injection Hn as Hn.
    injection Hm as Hm.
    rewrite Hn.
    rewrite Hm.
    apply HCE.
Qed.

(**************************************************
 ******************* Question 4 *******************
 **************************************************)
Theorem In_app_iff: forall A l l' (a : A),
  In a (l ++ l') <-> In a l \/ In a l'.
Proof.
  intros A l l'.
  induction l as [|a' l'' IH].
  - intros a.
    simpl.
    split.
    + intro H. right. apply H.
    + intros [H | H]. { destruct H. } { apply H. }
  - intros a.
    split.
    + simpl.
      intros [H | H].
      * left. left. apply H.
      * apply IH in H.
        rewrite <- or_assoc.
        right.
        apply H.
    + simpl.
      intros [[H1 | H2] | H3].
      * left. apply H1.
      * right. apply IH. left. apply H2.
      * right. apply IH. right. apply H3.
Qed.

(**************************************************
 ******************* Question 5 *******************
 **************************************************)
Fixpoint All { T : Type } (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => (P h) /\ (All P t)
  end.

Theorem All_In: forall T (P : T -> Prop) (l : list T),
  (forall x, In x l -> P x) <-> All P l.
Proof.
  intros T P l.
  induction l as [| x' l' IH ].
  - split.
    + intros _. apply I.
    + intros _ x H. destruct H.
  - simpl.
    split.
    + intro H.
      split.
      * apply H. left. reflexivity.
      * apply IH.
        intros x H'.
        assert (TEMP_OR: x' = x \/ In x l'). { right. apply H'. }
        apply H in TEMP_OR.
        apply TEMP_OR.
    + intros H x H'.
      destruct H as [H1 H2].
      destruct H' as [H' | H'].
      * rewrite H' in H1. apply H1.
      * rewrite <- IH in H2.
        apply H2 in H'.
        apply H'.
Qed.
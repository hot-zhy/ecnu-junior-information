(****************** Prerequisites *****************)
From Coq Require Import Setoids.Setoid.

(*** ev ***)
Inductive ev : nat -> Prop :=
  | ev_0                       : ev 0
  | ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(*** list ***)
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

(*** regexp ***)
Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Reserved Notation "s =~ re" (at level 80).
Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).

(**************************************************
 ******************* Question 1 *******************
 **************************************************)
Theorem ev_sum: forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em.
  induction En as [| n' En' IHEn'].
  - apply Em.
  - simpl. apply ev_SS. apply IHEn'.
Qed.

(**************************************************
 ******************* Question 2 *******************
 **************************************************)
Lemma le_trans: forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2.
  induction H2 as [| n' o' H'].
  - apply H1.
  - apply le_S. apply H'.
Qed.

(**************************************************
 ******************* Question 3 *******************
 **************************************************)
Example reg_exp_ex3: [0;1;0;1] =~ Star (App (Char 0) (Char 1)).
Proof.
  assert (tuple_01: [0; 1] =~ App (Char 0) (Char 1)).
  {
    apply (MApp [0]).
    + apply MChar.
    + apply MChar.
  }
  
  apply (MStarApp [0;1]).
  - apply tuple_01.
  - apply (MStarApp [0; 1]).
    + apply tuple_01.
    + apply MStar0.
Qed.

(**************************************************
 ******************* Question 4 *******************
 **************************************************)
Lemma MUnion': forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 -> s =~ Union re1 re2.
Proof.
  intros T s re1 re2.
  intros [H | H].
  - apply MUnionL. apply H.
  - apply MUnionR. apply H.
Qed.
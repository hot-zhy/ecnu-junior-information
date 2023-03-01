(*偶数判断*)
Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

(*奇数判断*)
Definition oddb (n:nat) : bool :=
  negb (evenb n).

(*比较函数*)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)

Check mult_n_Sm.
(* ===> forall n m : nat, n * m + n = n * S m *)

(*同时引进多个变量，多用于bool值*)
intros [] [].

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. 
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

(*加法交换律*)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  -simpl. reflexivity.
  -simpl. rewrite IHn'. reflexivity.
Qed.

(*replace*)
Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> plus_comm.
  replace (n+p) with (p + n).
  -rewrite -> plus_assoc. reflexivity.
  -rewrite -> plus_comm. reflexivity.
Qed.

(*关于list的一些符号*)
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
(*连接两个列表*)
Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

(*插入排序*)
Fixpoint insertion_sort (l:natlist) : natlist :=
  match l with
  |nil => nil
  |h :: t => insert h (insertion_sort t)
  end.

(*判断子集*)
Fixpoint subset (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => andb (member h s2) (subset t (remove_one h s2))
  end.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intro l. induction l as [|n l' IHl'].
  -simpl. reflexivity.
  -simpl. rewrite IHl'. reflexivity.
Qed.

(*拆分pail list*)
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  |nil => (nil , nil)
  |(x,y) :: t => ( x :: fst (split t) ,  y :: snd (split t))
  end.

(*过滤器*)
Fixpoint filter {X:Type} (test: X->bool) (l:list X) : (list X) :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.

(*匿名函数*)
Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => andb (evenb n) ( 7 <=? n)) l.

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(*等号两边交换*)
symmetry.

(*传递性*)
Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(*transitivity(重要)*)
Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2.   Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

(*功能同上*)
f_equal.

(*交集的交换律*)
Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.

(** Use [apply ... with ...] *)
Lemma in_not_nil_42_take2 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(*得到一个false，在结论中（false->p）*)
exfalso.

(*递归定义定理：被四整除*)
Inductive div4 : nat -> Prop := 
  |div4_0 : div4 0
  |div4_4S (n : nat) (H: div4 n) : div4 (S (S (S (S n)))).


Theorem le_plus_l : forall a b,
  a <= a + b.



(****************** Prerequisites *****************)
Set Warnings "-notation-overridden,-parsing".
Module ProofObjectPlayground.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.
Arguments conj [P] [Q].
Notation "P /\ Q" := (and P Q) : type_scope.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.
Arguments or_introl [P] [Q].
Arguments or_intror [P] [Q].
Notation "P \/ Q" := (or P Q) : type_scope.

Definition relation (X: Type) := X -> X -> Prop.
Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).
Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

(******************* conj_disj *******************)
Definition conj_disj: forall P Q R, (P /\ Q) \/ (P /\ R) -> P /\ (Q \/ R) :=
  fun (P Q R: Prop) (H: (P /\ Q) \/ (P /\ R)) =>
  match H with
  | or_introl HPQ =>
    match HPQ with
    | conj P Q => conj P (or_introl Q)
    end
  | or_intror HPR =>
    match HPR with
    | conj P R => conj P (or_intror R)
    end
  end.

(******************* plus_one_r' *******************)
Theorem plus_one_r': forall n : nat, n + 1 = S n.
Proof.
  apply nat_ind.
  - reflexivity.
  - intros n IH.
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(******************* lt_trans *******************)
Theorem lt_trans': transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [ | m' Hm'o].
  - apply le_S. assumption.
  - apply le_S. assumption.
Qed.

(******************* rsc_trans *******************)
Lemma rsc_trans:
  forall (X: Type) (R: relation X) (x y z: X),
    clos_refl_trans_1n R x y ->
    clos_refl_trans_1n R y z ->
    clos_refl_trans_1n R x z.
Proof.
  intros X R x y z HCxy HCyz.
  generalize dependent z.
  induction HCxy.
  - intros. assumption.
  - intros z0 Hzz0.
    apply IHHCxy in Hzz0.
    apply rt1n_trans with (y := y).
    + assumption.
    + assumption.
Qed.
End ProofObjectPlayground.
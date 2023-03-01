Theorem plus_n_Sm : forall n m : nat,
  S(n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.


Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  induction n as [| n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn'.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Theorem mul_n_Sm: forall n m : nat,
  n + n * m = n * S m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite <-IHn'.
    rewrite add_shuffle3.
    reflexivity.
Qed.

(* Prerequired theorem for mul_comm *)
Theorem mul_n_0 : forall n : nat,
  n * 0 = 0.
Proof.
  intro n.
  induction n as [|n' IHn'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  induction n as [|n' IHn'].
  - simpl.
    rewrite mul_n_0.
    reflexivity.
  - simpl.
    rewrite <- mul_n_Sm.
    rewrite IHn'.
    reflexivity.
Qed.
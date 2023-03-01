(**************************************************
 ******************* Question 1 *******************
 **************************************************)
Theorem or_commut: forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

(**************************************************
 ******************* Question 2 *******************
 **************************************************)
Theorem not_both_true_and_false: forall P : Prop,
  ~ (P /\ ~ P).
Proof.
  intro P.
  unfold not.
  intros [HP HNP].
  apply HNP in HP.
  apply HP.
Qed.

(**************************************************
 ******************* Question 3 *******************
 **************************************************)
Theorem or_distributes_over_and: forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R [HP | [HQ HR]].
  - split.
    + left. apply HP.
    + left. apply HP.
  - split.
    + right. apply HQ.
    + right. apply HR.
Qed.

(**************************************************
 ******************* Question 4 *******************
 **************************************************)
Theorem or_distributes_over_and': forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R [[HP | HQ] [HP' | HR]].
  - left. apply HP.
  - left. apply HP.
  - left. apply HP'.
  - right.
    split.
    + apply HQ.
    + apply HR.
Qed.
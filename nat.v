Set Mangle Names.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Notation "0" := O.
Notation "1" := (S O).

(* TODO: Something about setoids ???? See
   https://rocq-prover.org/doc/v8.12/refman/addendum/generalized-rewriting.html.
   This might also help with the other proofs. *)
Axiom Reflexive : forall (n : nat), n = n.
Axiom Symmetric : forall (a b : nat), a = b -> b = a.
Axiom Transitive : forall (a b c : nat), a = b -> b = c -> a = c.
Axiom Injection : forall (a b : nat), S a = S b -> a = b.
Axiom ConstructZero : forall (n : nat), S n <> 0.

Fixpoint add (a b : nat) : nat :=
  match a with
  | O => b
  | S c => S (add c b)
  end.

Notation "a + b" := (add a b) (at level 50, left associativity).

(* TODO: all these proofs are the same lol *)

Theorem add_assoc : forall (a b c : nat), (a + b) + c = a + (b + c).
Proof.
  intros a b c. induction a as [| a' IHa'].
  - reflexivity.
  - simpl. rewrite IHa'. reflexivity.
Qed.

Lemma add_0_l : forall (n : nat), 0 + n = n.
Proof. reflexivity. Qed.

Lemma add_0_r : forall (n : nat), n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma add_n_S_m : forall (n m : nat), n + S m = S (n + m).
Proof.
  intros n m. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_comm : forall (n m : nat), n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  - rewrite add_0_r. reflexivity.
  - rewrite add_n_S_m. simpl. rewrite IHn'. reflexivity.
Qed.

Theorem add_id_exist : exists (m : nat), forall (n : nat), m + n = n.
Proof. exists 0. reflexivity. Qed.

Theorem add_compat_eq : forall (a b c : nat), a + c = b + c -> a = b.
Proof.
  intros a b c H. induction c as [| c' IHc'].
  - rewrite <- add_0_r. symmetry.
    rewrite <- add_0_r. symmetry.
    assumption.
  - apply IHc'.
    rewrite add_n_S_m in H.
    rewrite add_n_S_m in H.
    inversion H. reflexivity.
Qed.

Theorem add_id_uniq : forall (n m : nat), m + n = n -> m = 0.
Proof.
  intros n m H.
  apply add_compat_eq with n.
  rewrite add_0_l. assumption.
Qed.

Fixpoint mul (a b : nat) : nat :=
  match a with
  | O => O
  | S c => add b (mul c b)
  end.

Notation "a * b" := (mul a b) (at level 40, left associativity).

Lemma mul_1_l : forall (n : nat), 1 * n = n.
Proof. apply add_0_r. Qed.

Lemma mul_1_r : forall (n : nat), n * 1 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem distr_l : forall (a b c : nat), a * (b + c) = (a * b) + (a * c).
Proof.
  intros a b c. induction a as [| a' IHa'].
  - reflexivity.
  - simpl. rewrite IHa'.
    rewrite add_assoc, add_assoc.
    enough (c + (a'*b + a'*c) = a'*b + (c + a'*c)) as H.
    + rewrite H. reflexivity.
    + rewrite add_comm, add_assoc.
      assert (a'*c + c = c + a'*c) as H by apply add_comm.
      rewrite H. reflexivity.
Qed.

Lemma mul_0_l : forall (n : nat), 0 * n = 0.
Proof. reflexivity. Qed.

Lemma mul_0_r : forall (n : nat), n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem mul_comm : forall (a b : nat), a * b = b * a.
Proof.
  intros a b. induction a as [| a' IHa'].
  - simpl. rewrite mul_0_r. reflexivity.
  - simpl. rewrite IHa'.
    enough (b * S a' = b * (a' + 1)) as H.
    + rewrite H, distr_l, mul_1_r, add_comm. reflexivity.
    + rewrite add_comm. simpl. reflexivity.
Qed.

Theorem distr_r : forall (a b c : nat), (a + b) * c = (a * c) + (b * c).
Proof.
  intros a b c.
  rewrite mul_comm.
  rewrite distr_l.
  rewrite mul_comm, add_comm.
  rewrite mul_comm, add_comm. reflexivity.
Qed.

Theorem mul_assoc : forall (a b c : nat), (a * b) * c = a * (b * c).
Proof.
  intros a b c. induction a as [| a' IHa'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHa', <- distr_r. reflexivity.
Qed.

Theorem mul_id_exist : exists (s : nat), forall (n : nat), s * n = n.
Proof. exists 1. apply mul_1_l. Qed.

Theorem mul_compat_eq : forall (a b c : nat), c <> 0 -> a * c = b * c -> a = b.
Proof.
  intros a b c H.
  induction c as [| c' IHc'].
  admit.
Admitted.

Theorem mul_id_uniq : forall (n m : nat), n <> 0 -> m <> 0 -> m * n = n -> m = 1.
Proof.
  intros n m Hn _ H.
  apply mul_compat_eq with n.
  - apply Hn.
  - rewrite mul_1_l. assumption.
Qed.

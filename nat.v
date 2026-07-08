Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Notation "0" := O.
Notation "1" := (S O).

(* TODO: Oh god
https://rocq-prover.org/doc/v8.13/refman/proof-engine/tactics.html#proof-maintenance
*)

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
  intros. induction a.
  - reflexivity.
  - simpl. rewrite IHa. reflexivity.
Qed.

Lemma add_0_l : forall (n : nat), 0 + n = n.
Proof. reflexivity. Qed.

Lemma add_0_r : forall (n : nat), n + 0 = n.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Lemma add_n_S_m : forall (n m : nat), n + S m = S (n + m).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_comm : forall (n m : nat), n + m = m + n.
Proof.
  intros. induction n.
  - rewrite add_0_r. reflexivity.
  - rewrite add_n_S_m. simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_id_exist : exists (m : nat), forall (n : nat), m + n = n.
Proof. exists 0. reflexivity. Qed.

Lemma h1 : forall (n m : nat), S n = S m <-> n = m.
Proof.
  intuition.
  + inversion H. reflexivity.
  + inversion H. reflexivity.
Qed.

Theorem add_compat_eq : forall (a b c : nat), a + c = b + c -> a = b.
Proof.
  intros. induction c.
  - rewrite <- add_0_r. symmetry.
    rewrite <- add_0_r. symmetry.
    assumption.
  - apply IHc.
    rewrite add_n_S_m in H.
    rewrite add_n_S_m in H.
    inversion H. reflexivity.
Qed.

Theorem add_id_uniq : forall (n m : nat), m + n = n -> m = 0.
Proof.
  intros.
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
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem distr_l : forall (a b c : nat), a * (b + c) = (a * b) + (a * c).
Proof.
  intros. induction a.
  - reflexivity.
  - simpl. rewrite IHa.
    rewrite add_assoc, add_assoc.
    enough (c + (a*b + a*c) = a*b + (c + a*c)).
    + rewrite H. reflexivity.
    + rewrite add_comm, add_assoc.
      assert (a*c + c = c + a*c) by apply add_comm.
      rewrite H. reflexivity.
Qed.

Lemma mul_0_l : forall (n : nat), 0 * n = 0.
Proof. reflexivity. Qed.

Lemma mul_0_r : forall (n : nat), n * 0 = 0.
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem mul_comm : forall (a b : nat), a * b = b * a.
Proof.
  intros. induction a.
  - simpl. rewrite mul_0_r. reflexivity.
  - simpl. rewrite IHa.
    enough (b * S a = b * (a + 1)).
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
  intros a b c.
  induction a.
  - simpl. reflexivity.
  - simpl. rewrite <- IHa. rewrite <- distr_r. reflexivity.
Qed.

Theorem mul_id_exist : exists (s : nat), forall (n : nat), s * n = n.
Proof. exists 1. apply mul_1_l. Qed.

Theorem mul_compat_eq : forall (a b c : nat), a * c = b * c -> a = b.
Proof.
  admit.
Admitted.

Theorem mul_id_uniq : forall (n s : nat), n <> 0 -> s <> 0 -> s * n = n -> s = 1.
Proof.
  intros.
  apply mul_compat_eq with n.
  rewrite mul_1_l. assumption.
Qed.

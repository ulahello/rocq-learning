Inductive nat : Set :=
  | Z : nat
  | S : nat -> nat.

Notation "0" := Z.
Notation "1" := (S Z).

Fixpoint add (a b : nat) : nat :=
  match a with
  | Z => b
  | S c => S (add c b)
  end
where "a + b" := (add a b).

(* TODO: all these proofs are the same lol *)

Theorem add_assoc : forall (a b c : nat), (a + b) + c = a + (b + c).
  intros a b c.
  induction a.
  - simpl. trivial.
  - simpl. rewrite IHa. trivial.
Qed.

(* TODO: this is a bad name *)
Lemma add_id_comm : forall (n : nat), n + 0 = n.
  intros n.
  induction n.
  - simpl. trivial.
  - simpl. rewrite IHn. trivial.
Qed.

Lemma add_succ_comm : forall (a b : nat), a + S b = S (a + b).
  intros a b.
  induction a.
  - simpl. trivial.
  - simpl. rewrite IHa. trivial.
Qed.

Theorem add_comm : forall (a b : nat), a + b = b + a.
  intros a b.
  induction a.
  - destruct b. trivial.
    simpl. rewrite add_id_comm. trivial.
  - simpl. rewrite IHa. rewrite add_succ_comm. trivial.
Qed.

Theorem add_id_exist : exists (z : nat), forall (n : nat), n + z = n.
  exists 0.
  apply add_id_comm.
Qed.

Theorem add_id_uniq : forall (n z : nat), n + z = n -> z = 0.
  intros n z.
  case z.
  - trivial.
  - intros n0.
    rewrite add_comm. simpl.
    (* TODO: Something about setoids ???? See
    https://rocq-prover.org/doc/v8.12/refman/addendum/generalized-rewriting.html.
    This might also help with the other proofs. *)
    admit.
Admitted.

Fixpoint mul (a b : nat) : nat :=
  match a with
  | Z => Z
  | S c => add b (mul c b)
  end
where "a * b" := (mul a b).

Lemma mul_id_comm : forall (n : nat), n * 1 = n.
  intros n.
  induction n.
  - simpl. trivial.
  - simpl. rewrite IHn. trivial.
Qed.

Theorem distr_l : forall (a b c : nat), a * (b + c) = (a * b) + (a * c).
  intros a b c.
  induction a.
  - simpl. trivial.
  - simpl. rewrite IHa.
    rewrite add_assoc, add_assoc.
    enough (c + (a*b + a*c) = a*b + (c + a*c)).
    + rewrite H. trivial.
    + rewrite add_comm, add_assoc.
      assert (a*c + c = c + a*c) by apply add_comm.
      rewrite H. trivial.
Qed.

Lemma mul_add_id_comm : forall (n : nat), n * 0 = 0.
  intros n.
  induction n.
  - simpl. trivial.
  - simpl. rewrite IHn. trivial.
Qed.

Theorem mul_comm : forall (a b : nat), a * b = b * a.
  intros a b.
  induction a.
  - simpl. rewrite mul_add_id_comm. trivial.
  - simpl. rewrite IHa.
    enough (b * S a = b * (a + 1)).
    + rewrite H, distr_l, mul_id_comm, add_comm. trivial.
    + rewrite add_comm. simpl. trivial.
Qed.

Theorem distr_r : forall (a b c : nat), (a + b) * c = (a * c) + (b * c).
  intros a b c.
  rewrite mul_comm.
  rewrite distr_l.
  rewrite mul_comm, add_comm.
  rewrite mul_comm, add_comm. trivial.
Qed.

Theorem mul_assoc : forall (a b c : nat), (a * b) * c = a * (b * c).
  intros a b c.
  induction a.
  - simpl. trivial.
  - simpl. rewrite <- IHa. rewrite <- distr_r. trivial.
Qed.

Theorem mul_id_exist : exists (s : nat), forall (n : nat), n * s = n.
  exists 1.
  apply mul_id_comm.
Qed.

Theorem mul_id_uniq : forall (n s : nat), s <> 0 /\ n * s = n -> s = 1.
  intros n s.
  admit.
Admitted.

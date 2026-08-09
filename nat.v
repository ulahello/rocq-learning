Set Mangle Names.

From Corelib Require Classes.RelationClasses.

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
  - simpl. rewrite add_n_S_m, IHn'. reflexivity.
Qed.

Theorem add_id_exist : exists (m : nat), forall (n : nat), m + n = n.
Proof. exists 0. reflexivity. Qed.

Theorem add_compat_eq : forall (a b c : nat), a + c = b + c <-> a = b.
Proof.
  intros a b c. split.
  - intros H. induction c as [| c' IHc'].
    + rewrite add_0_r, add_0_r in H. assumption.
    + apply IHc'.
      rewrite add_n_S_m, add_n_S_m in H.
      inversion H. reflexivity.
  - intros H. subst. reflexivity.
Qed.

Lemma S_compat_eq : forall (a b : nat), S a = S b <-> a = b.
Proof.
  (* TODO: golf *)
  intros a b.
  assert (S a = a + 1) as Ha by (rewrite add_comm; reflexivity).
  assert (S b = b + 1) as Hb by (rewrite add_comm; reflexivity).
  rewrite Ha, Hb.
  apply add_compat_eq.
Qed.

Theorem add_id_uniq : forall (n m : nat), m + n = n -> m = 0.
Proof.
  intros n m H.
  apply add_compat_eq with n.
  rewrite add_0_l. assumption.
Qed.

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

Fixpoint sub (a b : nat) : nat :=
  match b with
  | O => a
  | S c => sub (pred a) c
  end.

Notation "a - b" := (sub a b) (at level 50, left associativity).

Lemma sub_0_r : forall (n : nat), n - 0 = n.
Proof. reflexivity. Qed.

Lemma sub_0_l : forall (n : nat), 0 - n = 0.
Proof. intros n. induction n; trivial. Qed.

Lemma sub_annih : forall (n : nat), n - n = 0.
Proof. intros n. induction n; trivial. Qed.

Lemma sub_Sn_Sm : forall (n m : nat), S n - S m = n - m.
Proof.
  intros a. induction a as [| a' IHa'];
    intros b; induction b as [| b' IHb'];
    reflexivity.
Qed.

Lemma sub_nm_or_mn_0 : forall (n m : nat), n - m = 0 \/ m - n = 0.
Proof.
  intros a. induction a as [| a' IHa'].
  - intros b. rewrite sub_0_l. tauto.
  - intros [| b].
    + rewrite sub_0_l. tauto.
    + rewrite sub_Sn_Sm.
      apply IHa'.
Qed.

Lemma sub_nz_diff : forall (n m : nat), n - m <> 0 -> n <> m.
Proof.
  intros a. induction a as [| a' IHa'].
  - intros b. rewrite sub_0_l. contradiction.
  - intros [| b'].
    + rewrite sub_0_r. tauto.
    + rewrite sub_Sn_Sm.
      intros H.
      (* TODO: golf *)
      enough (a' <> b') as H'.
      * pose (S_compat_eq a' b') as E.
        intros C.
        apply H', E.
        assumption.
      * apply IHa'.
        assumption.
Qed.

Definition le (a b : nat) := a - b = 0.
Infix "<=" := le (at level 70).

Definition lt (a b : nat) := a <= b /\ a <> b.
Infix "<" := lt (at level 70).

Theorem le_refl : forall (n : nat), n <= n.
Proof. apply sub_annih. Qed.

Theorem lt_irrefl : forall (n : nat), ~(n < n).
Proof. unfold lt. tauto. Qed.

Lemma S_compat_le : forall (a b : nat), a <= b <-> S a <= S b.
Proof.
  intros a b.
  unfold le.
  rewrite sub_Sn_Sm.
  tauto.
Qed.

Theorem le_eq : forall (a b : nat), (a <= b /\ b <= a) <-> a = b.
Proof.
  intros a.
  induction a as [| a' IHa'].
  - intros b; split.
    + unfold le. rewrite sub_0_r.
      intros [_ H]. symmetry. assumption.
    + intros H. rewrite <- H.
      split; apply le_refl.
  - intros b. split.
    + destruct b as [| b'].
      * unfold le. intros [H _].
        rewrite sub_0_r in H.
        discriminate.
      * intros [L R].
        enough (a' = b') by (subst; reflexivity).
        enough (a' <= b' /\ b' <= a') by (apply IHa'; assumption).
        split; apply S_compat_le; assumption.
    + intros H. rewrite H.
      split; apply le_refl.
Qed.

Theorem le_neg : forall (a b : nat), ~(a <= b) <-> b < a.
Proof.
  intros a b.
  split; intros H.
  - unfold lt, le in *. split.
    + pose (sub_nm_or_mn_0 a b) as H'.
      destruct H'.
      * contradiction.
      * assumption.
    + symmetry. apply sub_nz_diff.
      assumption.
  - unfold lt, le in *.
    destruct a as [| a'].
    + tauto.
    + destruct H as [Hle Hne].
      destruct (S a' - b) eqn:gt.
      * assert (b = S a') by (apply le_eq; split; assumption).
        contradiction.
      * discriminate.
Qed.

Lemma le_nz_diff : forall (a b : nat), a - b <> 0 -> b < a.
Proof. apply le_neg. Qed.

Lemma le_succ_r : forall (a b : nat), a <= b -> a <= S b.
Proof.
  intros a. induction a as [| a' IHa'].
  - tauto.
  - intros [| b] H; try discriminate.
    apply IHa', S_compat_le.
    assumption.
Qed.

Lemma le_pred_l : forall (a b : nat), a <= b -> pred a <= b.
Proof.
  intros a. induction a as [| a' IHa'].
  - tauto.
  - intros [| b] H; try discriminate.
    apply IHa', S_compat_le.
    assumption.
Qed.

Theorem le_trans : forall (a b c : nat), a <= b -> b <= c -> a <= c.
  intros a.
  induction a as [| a' IHa'].
  - intros b c _ _. unfold le.
    rewrite sub_0_l.
    reflexivity.
  - intros [| b'] [| c'] L R; try discriminate.
    apply -> S_compat_le.
    apply (IHa' b' c'); apply S_compat_le; assumption.
Qed.

Theorem add_compat_le : forall (a b c : nat), a <= b <-> a + c <= b + c.
Proof.
  intros a b c. split; intros H.
  - induction c as [| c' IHc'].
    + do 2 rewrite add_0_r.
      assumption.
    + do 2 rewrite add_n_S_m.
      apply S_compat_le.
      assumption.
  - induction c as [| c' IHc'].
    + do 2 rewrite add_0_r in H.
      assumption.
    + do 2 rewrite add_n_S_m in H.
      apply S_compat_le in H.
      apply IHc'.
      assumption.
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

Lemma mul_0_l : forall (n : nat), 0 * n = 0.
Proof. reflexivity. Qed.

Lemma mul_0_r : forall (n : nat), n * 0 = 0.
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
    rewrite <- add_assoc, <- add_assoc. apply add_compat_eq.
    assert (c + a' * b = a' * b + c) as H by apply add_comm.
    rewrite add_assoc, add_assoc, H. reflexivity.
Qed.

Lemma mul_n_S_m : forall (n m : nat), n * S m = n + n * m.
Proof.
  intros n m.
  assert (S m = 1 + m) as H by reflexivity.
  rewrite H, distr_l, mul_1_r. reflexivity.
Qed.

Theorem mul_comm : forall (a b : nat), a * b = b * a.
Proof.
  intros a b. induction a as [| a' IHa'].
  - rewrite mul_0_r. reflexivity.
  - simpl. rewrite IHa', mul_n_S_m. reflexivity.
Qed.

Theorem distr_r : forall (a b c : nat), (a + b) * c = (a * c) + (b * c).
Proof.
  intros a b c.
  rewrite mul_comm, distr_l.
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

Theorem mul_compat_eq : forall (a b c : nat), c <> 0 -> a * c = b * c <-> a = b.
Proof.
  intros a b c Hc. split.
  - intros H. induction c as [| c' IHc'].
    + contradiction.
    + admit.
  - intros H. subst. reflexivity.
Admitted.

Theorem mul_id_uniq : forall (n m : nat), n <> 0 -> m <> 0 -> m * n = n -> m = 1.
Proof.
  intros n m Hn _ H.
  apply mul_compat_eq with n.
  - apply Hn.
  - rewrite mul_1_l. assumption.
Qed.

Set Mangle Names.

From Corelib Require Classes.RelationClasses.

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Notation "0" := O.
Notation "1" := (S O).

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

Lemma S_compat_eq : forall (a b : nat), S a = S b <-> a = b.
Proof.
  intros a b. split.
  - intros H. inversion H. reflexivity.
  - intros H. subst. reflexivity.
Qed.

Theorem add_compat_eq : forall (a b c : nat), a + c = b + c <-> a = b.
Proof.
  intros a b c. split.
  - intros H. induction c as [| c' IHc'].
    + do 2 rewrite add_0_r in H. assumption.
    + apply IHc'.
      rewrite add_n_S_m, add_n_S_m in H.
      apply S_compat_eq, H.
  - intros H. subst. reflexivity.
Qed.

Theorem add_id_uniq : forall (n m : nat), m + n = n -> m = 0.
Proof.
  intros n m H.
  apply add_compat_eq with n, H.
Qed.

Lemma add_eq_0 : forall (n m : nat), n <> 0 -> n + m <> 0.
Proof. intros [| n]; try tauto; discriminate. Qed.

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
  - intros b. rewrite sub_0_l. tauto.
  - intros [| b']; try tauto.
    rewrite sub_Sn_Sm.
    intros H C.
    apply -> S_compat_eq in C.
    apply (IHa' b' H), C.
Qed.

Definition le (a b : nat) := a - b = 0.
Infix "<=" := le (at level 70).

Definition lt (a b : nat) := a <= b /\ a <> b.
Infix "<" := lt (at level 70).

Theorem le_refl : forall (n : nat), n <= n.
Proof. apply sub_annih. Qed.

Theorem lt_irrefl : forall (n : nat), ~(n < n).
Proof. unfold lt. tauto. Qed.

Lemma le_0_l : forall (n : nat), 0 <= n.
Proof. apply sub_0_l. Qed.

Lemma le_0_r : forall (n : nat), n <= 0 -> n = 0.
Proof. tauto. Qed.

Lemma S_compat_le : forall (a b : nat), a <= b <-> S a <= S b.
Proof.
  intros a b.
  unfold le.
  rewrite sub_Sn_Sm.
  tauto.
Qed.

Theorem le_eq : forall (a b : nat), (a <= b /\ b <= a) -> a = b.
Proof.
  intros a.
  induction a as [| a' IHa'].
  - intros b. symmetry. tauto.
  - intros [| b']; try tauto.
    intros [L R].
    apply S_compat_eq, IHa'.
    split; assumption.
Qed.

Theorem le_neg : forall (a b : nat), ~(a <= b) <-> b < a.
Proof.
  intros a b. split.
  - intros H. split.
    + destruct (sub_nm_or_mn_0 a b); tauto.
    + symmetry. apply sub_nz_diff, H.
  - intros [Hle Hne].
    contradict Hne.
    apply le_eq. tauto.
Qed.

Lemma le_nz_diff : forall (a b : nat), a - b <> 0 -> b < a.
Proof. apply le_neg. Qed.

Lemma le_succ_r : forall (a b : nat), a <= b -> a <= S b.
Proof.
  intros a. induction a as [| a' IHa'].
  - tauto.
  - intros [| b] H; try discriminate.
    apply IHa', S_compat_le, H.
Qed.

Lemma le_pred_l : forall (a b : nat), a <= b -> pred a <= b.
Proof.
  intros [| a] b H; trivial.
  apply S_compat_le, le_succ_r, H.
Qed.

Theorem le_trans : forall (a b c : nat), a <= b -> b <= c -> a <= c.
  intros a.
  induction a as [| a' IHa'].
  - intros b c _ _. unfold le.
    rewrite sub_0_l.
    reflexivity.
  - intros [| b'] [| c'] L R; try discriminate.
    apply -> S_compat_le.
    apply (IHa' b' c'); assumption.
Qed.

Theorem add_compat_le : forall (a b c : nat), a <= b <-> a + c <= b + c.
Proof.
  intros a b c. split; intros H.
  - induction c as [| c' IHc'].
    + do 2 rewrite add_0_r.
      assumption.
    + do 2 rewrite add_n_S_m.
      apply S_compat_le, IHc'.
  - induction c as [| c' IHc'].
    + do 2 rewrite add_0_r in H.
      assumption.
    + do 2 rewrite add_n_S_m in H.
      apply IHc', H.
Qed.

Lemma add_compat_le_l : forall (a b c : nat), a <= b <-> c + a <= c + b.
Proof.
  intros a b c.
  replace (c + a) with (a + c) by apply add_comm.
  replace (c + b) with (b + c) by apply add_comm.
  apply add_compat_le.
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

Lemma mul_eq_0 : forall (n m : nat), n <> 0 -> m <> 0 -> n * m <> 0.
Proof.
  intros [| n] [| m]; try contradiction.
  discriminate.
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
  do 2 rewrite mul_comm, add_comm.
  reflexivity.
Qed.

Theorem mul_assoc : forall (a b c : nat), (a * b) * c = a * (b * c).
Proof.
  intros a b c. induction a as [| a' IHa']; simpl.
  - reflexivity.
  - rewrite <- IHa', <- distr_r. reflexivity.
Qed.

Theorem mul_id_exist : exists (s : nat), forall (n : nat), s * n = n.
Proof. exists 1. apply mul_1_l. Qed.

Theorem mul_compat_eq : forall (a b c : nat), c <> 0 -> a * c = b * c <-> a = b.
Proof.
  intros a. induction a as [| a' IHa'].
  - intros [| b] c Hc; try tauto.
    split; intros H.
    + contradict H. symmetry.
      apply add_eq_0, Hc.
    + discriminate.
  - intros [| b'] c Hc.
    + split; intros H.
      * contradict H.
        apply add_eq_0, Hc.
      * discriminate.
    + simpl. split; intros H.
      * apply S_compat_eq.
        apply -> IHa'.
        -- do 2 (rewrite add_comm in H; symmetry in H).
           apply add_compat_eq in H.
           apply H.
        -- exact Hc.
      * do 2 (rewrite add_comm; symmetry).
        apply add_compat_eq, IHa'.
        -- exact Hc.
        -- apply S_compat_eq, H.
Qed.

Theorem mul_id_uniq : forall (n m : nat), n <> 0 -> m <> 0 -> m * n = n -> m = 1.
Proof.
  intros n m Hn _ H.
  apply mul_compat_eq with n.
  - apply Hn.
  - rewrite mul_1_l. assumption.
Qed.

Theorem mul_compat_le : forall (a b c : nat), c <> 0 -> a <= b <-> a * c <= b * c.
Proof.
  intros a. induction a as [| a' IHa'].
  - intros b c Hc.
    split; intros H; apply le_0_l.
  - intros [| b'] c Hc.
    + split; intros H.
      * discriminate.
      * contradict H. apply add_eq_0, Hc.
    + split; intros H.
      * apply S_compat_le in H.
        apply add_compat_le_l, IHa'; assumption.
      * apply add_compat_le_l in H.
        apply -> S_compat_le.
        apply <- (IHa' b' c); assumption.
Qed.


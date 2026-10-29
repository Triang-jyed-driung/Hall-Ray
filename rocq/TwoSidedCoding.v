From Stdlib Require Import Reals Psatz Lia ZArith.
From HallRay Require Import SymbolicCoding StableCoding.
Open Scope R_scope.

Definition biword := Z -> bool.
Definition bi_shift (z : biword) : biword := fun k => z (k+1)%Z.
Definition bi_shift_by (j : nat) (z : biword) : biword := fun k => z (k+Z.of_nat j)%Z.
Definition future_of (z : biword) : future := fun k => z (Z.of_nat k).
Definition past_of (z : biword) : future := fun k => z (-1-Z.of_nat k)%Z.
Definition u_code (z : biword) := coded (future_of z).
Definition v_code (z : biword) := stable_coded (past_of z).

Lemma future_shift_matches : forall z k, shift (future_of z) k = future_of (bi_shift z) k.
Proof. intros z k; unfold shift, future_of, bi_shift; f_equal; lia. Qed.
Lemma future_shift_by_matches : forall z j k,
  shift_by j (future_of z) k = future_of (bi_shift_by j z) k.
Proof. intros z j k; unfold shift_by, future_of, bi_shift_by; f_equal; lia. Qed.
Lemma past_shift_tail_matches : forall z k, shift (past_of (bi_shift z)) k = past_of z k.
Proof. intros z k; unfold shift, past_of, bi_shift; f_equal; lia. Qed.

Theorem u_code_recursion : forall z,
  u_code z = branch (z 0%Z) (u_code (bi_shift z)).
Proof.
  intro z; unfold u_code. rewrite coded_recursion.
  assert (Hshift : coded (shift (future_of z)) = coded (future_of (bi_shift z)))
    by (apply coded_extensional; apply future_shift_matches).
  rewrite Hshift. reflexivity.
Qed.
Theorem v_code_recursion : forall z,
  v_code (bi_shift z) = psi_branch (z 0%Z) (v_code z).
Proof.
  intro z; unfold v_code. rewrite stable_coded_recursion.
  assert (Htail : stable_coded (shift (past_of (bi_shift z))) = stable_coded (past_of z))
    by (apply stable_coded_extensional; apply past_shift_tail_matches).
  rewrite Htail. reflexivity.
Qed.

Theorem u_code_inside : forall z, inside (u_code z).
Proof. intro z; apply coded_inside. Qed.
Theorem v_code_inside : forall z, stable_inside (v_code z).
Proof. intro z; apply stable_coded_inside. Qed.

Theorem u_code_common_future : forall n z z',
  (forall k, (k < n)%nat -> z (Z.of_nat k) = z' (Z.of_nat k)) ->
  close ((2/5)*(1/900)^n) (u_code z) (u_code z').
Proof. intros n z z' H; apply common_future_estimate; exact H. Qed.
Theorem v_code_common_past : forall n z z',
  (forall k, (k < n)%nat -> z (-1-Z.of_nat k)%Z = z' (-1-Z.of_nat k)%Z) ->
  close ((2/5)*(1/900)^n) (v_code z) (v_code z').
Proof. intros n z z' H; apply common_past_estimate; exact H. Qed.

Theorem u_code_extensional : forall z z',
  (forall k, z k = z' k) -> u_code z = u_code z'.
Proof. intros z z' H; apply coded_extensional; intro n; apply H. Qed.
Theorem v_code_extensional : forall z z',
  (forall k, z k = z' k) -> v_code z = v_code z'.
Proof. intros z z' H; apply stable_coded_extensional; intro n; apply H. Qed.

Lemma bi_shift_by_successor : forall n z k,
  bi_shift_by (S n) z k = bi_shift_by n (bi_shift z) k.
Proof. intros n z k; unfold bi_shift_by, bi_shift; f_equal; lia. Qed.

Definition splice_word (past future_symbols : future) : biword :=
  fun k => if Z_le_gt_dec 0 k then future_symbols (Z.to_nat k)
    else past (Z.to_nat (-1-k)).

Theorem splice_future : forall p f, u_code (splice_word p f) = coded f.
Proof.
  intros p f. apply coded_extensional. intro n. unfold future_of, splice_word.
  destruct (Z_le_gt_dec 0 (Z.of_nat n)); [rewrite Nat2Z.id; reflexivity|lia].
Qed.
Theorem splice_past : forall p f, v_code (splice_word p f) = stable_coded p.
Proof.
  intros p f. apply stable_coded_extensional. intro n. unfold past_of, splice_word.
  destruct (Z_le_gt_dec 0 (-1-Z.of_nat n)); [lia|].
  replace (-1-(-1-Z.of_nat n))%Z with (Z.of_nat n) by lia.
  rewrite Nat2Z.id; reflexivity.
Qed.

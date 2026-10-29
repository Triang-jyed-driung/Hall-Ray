From Stdlib Require Import Reals Psatz Lia Arith ZArith.
From HallRay Require Import MatrixAlgebra SymbolicCoding StableCoding SymbolicCocycle
  DefectLimit PeriodicReturns TwoSidedCoding LatticeReturns PeriodicWords.
Open Scope R_scope.

Definition constant_word : biword := fun _ => true.
Definition beginning_word (j : nat) : biword := fun k =>
  if Z.eqb (k+Z.of_nat j) (-1) then false else true.
Definition ending_word (r : nat) : biword := fun k =>
  if Z.eqb k (Z.of_nat r) then false else true.

Lemma integer_eqb_equivalent : forall a b c d,
  (a=b <-> c=d)%Z -> Z.eqb a b = Z.eqb c d.
Proof.
  intros a b c d Heq. destruct (Z.eqb a b) eqn:Hab.
  - apply Z.eqb_eq in Hab. symmetry; apply Z.eqb_eq; tauto.
  - apply Z.eqb_neq in Hab. symmetry; apply Z.eqb_neq; tauto.
Qed.

Lemma periodic_negative_window : forall n k,
  (-Z.of_nat (S n) <= k < Z.of_nat n)%Z ->
  periodic_word n k = (if Z.eqb k (-1) then false else true).
Proof.
  intros n k Hk. destruct (Z_le_gt_dec 0 k) as [Hpos|Hneg].
  - unfold periodic_word. rewrite Z.mod_small by lia.
    assert (Hn : Z.eqb k (Z.of_nat n) = false) by (apply Z.eqb_neq; lia).
    assert (Hm : Z.eqb k (-1) = false) by (apply Z.eqb_neq; lia).
    rewrite Hn,Hm; reflexivity.
  - rewrite <- (periodic_word_period n k). unfold periodic_word.
    rewrite Z.mod_small by lia.
    assert (Hb : Z.eqb (k+Z.of_nat (S n)) (Z.of_nat n) = Z.eqb k (-1)).
    { apply integer_eqb_equivalent; lia. }
    rewrite Hb; reflexivity.
Qed.

Lemma periodic_positive_window : forall n k,
  (0 <= k < 2*Z.of_nat (S n)-1)%Z ->
  periodic_word n k = (if Z.eqb k (Z.of_nat n) then false else true).
Proof.
  intros n k Hk. destruct (Z_lt_ge_dec k (Z.of_nat (S n))) as [Hsmall|Hlarge].
  - unfold periodic_word. rewrite Z.mod_small by lia; reflexivity.
  - replace k with ((k-Z.of_nat (S n))+Z.of_nat (S n))%Z at 1 by ring.
    rewrite periodic_word_period. unfold periodic_word.
    rewrite Z.mod_small by lia.
    assert (Ha : Z.eqb (k-Z.of_nat (S n)) (Z.of_nat n) = false) by (apply Z.eqb_neq; lia).
    assert (Hb : Z.eqb k (Z.of_nat n) = false) by (apply Z.eqb_neq; lia).
    rewrite Ha,Hb; reflexivity.
Qed.

Theorem periodic_beginning_codes : forall n j N,
  (j+N <= n)%nat ->
  close ((2/5)*(1/900)^N) (u_code (orbit_shift j (periodic_word n))) (u_code (beginning_word j)) /\
  close ((2/5)*(1/900)^N) (v_code (orbit_shift j (periodic_word n))) (v_code (beginning_word j)).
Proof.
  intros n j N HN. split.
  - apply u_code_common_future. intros k Hk.
    rewrite orbit_shift_by_matches. unfold bi_shift_by, beginning_word.
    apply periodic_negative_window. lia.
  - apply v_code_common_past. intros k Hk.
    rewrite orbit_shift_by_matches. unfold bi_shift_by, beginning_word.
    apply periodic_negative_window. lia.
Qed.

Theorem periodic_ending_codes : forall n j r N,
  (j+r=n)%nat -> (N <= j)%nat ->
  close ((2/5)*(1/900)^N) (u_code (orbit_shift j (periodic_word n))) (u_code (ending_word r)) /\
  close ((2/5)*(1/900)^N) (v_code (orbit_shift j (periodic_word n))) (v_code (ending_word r)).
Proof.
  intros n j r N Hjr HN. split.
  - apply u_code_common_future. intros k Hk.
    rewrite orbit_shift_by_matches. unfold bi_shift_by, ending_word.
    rewrite periodic_positive_window by lia.
    replace (Z.eqb (Z.of_nat k+Z.of_nat j) (Z.of_nat n)) with
      (Z.eqb (Z.of_nat k) (Z.of_nat r)) by (apply integer_eqb_equivalent; lia).
    reflexivity.
  - apply v_code_common_past. intros k Hk.
    rewrite orbit_shift_by_matches. unfold bi_shift_by, ending_word.
    rewrite periodic_positive_window by lia.
    replace (Z.eqb (-1-Z.of_nat k+Z.of_nat j) (Z.of_nat n)) with
      (Z.eqb (-1-Z.of_nat k) (Z.of_nat r)) by (apply integer_eqb_equivalent; lia).
    reflexivity.
Qed.

Theorem periodic_bulk_codes : forall n j N,
  (N <= j)%nat -> (j+N <= n)%nat ->
  close ((2/5)*(1/900)^N) (u_code (orbit_shift j (periodic_word n))) (u_code constant_word) /\
  close ((2/5)*(1/900)^N) (v_code (orbit_shift j (periodic_word n))) (v_code constant_word).
Proof.
  intros n j N Hj HN. split.
  - apply u_code_common_future. intros k Hk.
    rewrite orbit_shift_by_matches. unfold bi_shift_by, constant_word.
    rewrite periodic_positive_window by lia.
    assert (Hneq : Z.eqb (Z.of_nat k+Z.of_nat j) (Z.of_nat n) = false) by (apply Z.eqb_neq; lia).
    rewrite Hneq; reflexivity.
  - apply v_code_common_past. intros k Hk.
    rewrite orbit_shift_by_matches. unfold bi_shift_by, constant_word.
    rewrite periodic_positive_window by lia.
    assert (Hneq : Z.eqb (-1-Z.of_nat k+Z.of_nat j) (Z.of_nat n) = false) by (apply Z.eqb_neq; lia).
    rewrite Hneq; reflexivity.
Qed.

Lemma beginning_future : forall j k, future_of (beginning_word j) k = a_future k.
Proof.
  intros j k; unfold future_of, beginning_word, a_future.
  assert (H : Z.eqb (Z.of_nat k+Z.of_nat j) (-1) = false) by (apply Z.eqb_neq; lia).
  rewrite H; reflexivity.
Qed.
Lemma beginning_past : forall j k, past_of (beginning_word j) k = one_defect j k.
Proof.
  intros j k; unfold past_of, beginning_word, one_defect.
  replace (Z.eqb (-1-Z.of_nat k+Z.of_nat j) (-1)) with (Z.eqb (Z.of_nat k) (Z.of_nat j)) by
    (apply integer_eqb_equivalent; lia).
  rewrite natural_integer_eqb; reflexivity.
Qed.
Lemma ending_future : forall r k, future_of (ending_word r) k = one_defect r k.
Proof. intros r k; unfold future_of, ending_word, one_defect; rewrite natural_integer_eqb; reflexivity. Qed.
Lemma ending_past : forall r k, past_of (ending_word r) k = a_future k.
Proof.
  intros r k; unfold past_of, ending_word, a_future.
  assert (H : Z.eqb (-1-Z.of_nat k) (Z.of_nat r) = false) by (apply Z.eqb_neq; lia).
  rewrite H; reflexivity.
Qed.

Theorem beginning_code_formulas : forall j,
  u_code (beginning_word j) = coded a_future /\
  v_code (beginning_word j) = stable_coded (one_defect j).
Proof.
  intro j; split; [apply coded_extensional, beginning_future|apply stable_coded_extensional, beginning_past].
Qed.
Theorem ending_code_formulas : forall r,
  u_code (ending_word r) = coded (one_defect r) /\
  v_code (ending_word r) = stable_coded a_future.
Proof.
  intro r; split; [apply coded_extensional, ending_future|apply stable_coded_extensional, ending_past].
Qed.

Theorem beginning_fiber_products : forall j k,
  orbit_product k (beginning_word j) = matrix_power constant_return k.
Proof.
  intros j k. rewrite orbit_product_matches_future, <- constant_future_product.
  apply fiber_product_extensional, beginning_future.
Qed.
Theorem ending_suffix_product : forall r,
  orbit_product (S r) (ending_word r) = defect_product r.
Proof.
  intro r. rewrite orbit_product_matches_future.
  apply fiber_product_extensional, ending_future.
Qed.

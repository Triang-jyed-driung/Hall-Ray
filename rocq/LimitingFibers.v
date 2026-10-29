From Stdlib Require Import Reals Psatz Lia Arith ZArith.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  SymbolicCoding SymbolicCocycle ConcreteCocycle DefectLimit PeriodicReturns EllipticPowers
  EllipticConjugacy TwoSidedCoding LatticeReturns PeriodicWords LimitingWords.
Open Scope R_scope.

Theorem periodic_suffix_common_prefix : forall n j r N,
  (j+r=n)%nat -> (N <= n)%nat ->
  same_prefix (S r+N) (future_of (orbit_shift j (periodic_word n))) (one_defect r).
Proof.
  intros n j r N Hjr HN k Hk.
  unfold future_of. rewrite orbit_shift_by_matches. unfold bi_shift_by, one_defect.
  rewrite periodic_positive_window by lia.
  replace (Z.eqb (Z.of_nat k+Z.of_nat j) (Z.of_nat n)) with
    (Z.eqb (Z.of_nat k) (Z.of_nat r)) by (apply integer_eqb_equivalent; lia).
  rewrite natural_integer_eqb; reflexivity.
Qed.

Theorem periodic_suffix_error : forall n j r N,
  (j+r=n)%nat -> (N <= n)%nat ->
  opnorm (sub2 (orbit_product (S r) (orbit_shift j (periodic_word n))) (defect_product r)) <=
    opnorm (defect_product r)*(1/600)^N.
Proof.
  intros n j r N Hjr HN. rewrite orbit_product_matches_future.
  apply symbolic_relative_absolute_bound, periodic_suffix_common_prefix; assumption.
Qed.

Definition defect_product_bound := constant_power_bound*(opnorm defect_limit+1).

Theorem defect_products_bounded : forall r,
  opnorm (defect_product r) <= defect_product_bound.
Proof.
  intro r. pose proof (defect_limit_error_bound r) as Herror.
  pose proof (pow_incr (1/600) 1 r ltac:(lra)) as Hpow; rewrite pow1 in Hpow.
  pose proof (opnorm_nonnegative defect_limit) as HD.
  assert (Hseq : opnorm (defect_sequence r) <= opnorm defect_limit+1).
  { rewrite (matrix_difference_decomposition (defect_sequence r) defect_limit).
    pose proof (opnorm_subadditive (sub2 (defect_sequence r) defect_limit) defect_limit). lra. }
  rewrite defect_product_reconstruction. unfold defect_product_bound.
  eapply Rle_trans; [apply opnorm_submultiplicative|].
  apply Rmult_le_compat; auto using opnorm_nonnegative.
  apply constant_powers_uniformly_bounded.
Qed.

Theorem defect_suffixes_and_inverses_bounded : exists K, 0 < K /\ forall r,
  opnorm (defect_product r)+opnorm (adj2 (defect_product r)) <= K.
Proof.
  exists (3*defect_product_bound+1). split.
  - unfold defect_product_bound. pose proof constant_power_bound_nonnegative.
    pose proof (opnorm_nonnegative defect_limit). nra.
  - intro r. pose proof (defect_products_bounded r).
    pose proof (opnorm_adjugate_bound (defect_product r)). lra.
Qed.

Theorem periodic_suffixes_uniformly_bounded : forall n j r,
  (j+r=n)%nat ->
  opnorm (orbit_product (S r) (orbit_shift j (periodic_word n))) <= 2*defect_product_bound.
Proof.
  intros n j r Hjr. pose proof (periodic_suffix_error n j r 0 Hjr ltac:(lia)) as Herror.
  change (opnorm (sub2 (orbit_product (S r) (orbit_shift j (periodic_word n)))
    (defect_product r)) <= opnorm (defect_product r)*1) in Herror.
  rewrite Rmult_1_r in Herror.
  pose proof (defect_products_bounded r) as Hb.
  rewrite (matrix_difference_decomposition (orbit_product (S r) (orbit_shift j (periodic_word n))) (defect_product r)).
  pose proof (opnorm_subadditive
    (sub2 (orbit_product (S r) (orbit_shift j (periodic_word n))) (defect_product r)) (defect_product r)). lra.
Qed.

Theorem periodic_prefix_from_suffix : forall n j r,
  (j+r=n)%nat ->
  orbit_product j (periodic_word n) =
    mul2 (periodic_return n) (adj2 (orbit_product (S r) (orbit_shift j (periodic_word n)))).
Proof.
  intros n j r Hjr.
  rewrite <- periodic_word_return_product.
  replace (S n) with (j+S r)%nat by lia.
  rewrite orbit_product_add, mul2_assoc,
    (unimodular_right_inverse (orbit_product (S r) (orbit_shift j (periodic_word n)))).
  - rewrite mul2_id_right; reflexivity.
  - rewrite orbit_product_matches_future; apply factor_product_unimodular.
Qed.

Theorem periodic_prefix_rotation_error : forall n j,
  (j <= n)%nat ->
  opnorm (sub2 (orbit_product j (periodic_word n)) (matrix_power constant_return j)) <=
    constant_power_bound*(1/600)^(n-j).
Proof.
  intros n j Hj. rewrite orbit_product_matches_future.
  replace (fiber_product j (future_of (periodic_word n))) with (fiber_product j (periodic_future n)) by
    (apply fiber_product_extensional; intro k; symmetry; apply periodic_word_future).
  apply partial_period_rotation_bound; exact Hj.
Qed.

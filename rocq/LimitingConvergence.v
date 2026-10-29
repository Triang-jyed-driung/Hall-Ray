From Stdlib Require Import Reals Psatz Lia Arith FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  SymbolicCoding SymbolicCocycle DefectLimit PeriodicReturns EllipticConjugacy
  TwoSidedCoding LatticeReturns PeriodicWords LimitingWords LimitingFibers.
Open Scope R_scope.

Lemma indices_subtract_fixed : forall ns j,
  indices_tend_to_infinity ns -> indices_tend_to_infinity (fun k => (ns k-j)%nat).
Proof.
  intros ns j Hns N. destruct (Hns (N+j)%nat) as [I HI].
  exists I; intros i Hi; specialize (HI i Hi); lia.
Qed.

Lemma indices_minimum : forall ns ms,
  indices_tend_to_infinity ns -> indices_tend_to_infinity ms ->
  indices_tend_to_infinity (fun k => Nat.min (ns k) (ms k)).
Proof.
  intros ns ms Hn Hm N. destruct (Hn N) as [I HI]; destruct (Hm N) as [J HJ].
  exists (Nat.max I J). intros i Hi. specialize (HI i ltac:(lia)); specialize (HJ i ltac:(lia)); lia.
Qed.

Lemma geometric_indices_decay : forall r C ns,
  0 <= r < 1 -> 0 <= C -> indices_tend_to_infinity ns ->
  forall eps, 0 < eps -> exists I, forall i, (I <= i)%nat -> C*r^(ns i) < eps.
Proof.
  intros r C ns Hr HC Hns eps He.
  destruct (pow_lt_1_zero r ltac:(rewrite Rabs_right; lra) (eps/(C+1))
    ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
  destruct (Hns N) as [I HI]. exists I; intros i Hi.
  specialize (HN (ns i) (HI i Hi)).
  rewrite Rabs_right in HN by (apply Rle_ge, pow_le; lra).
  assert (Hsmall : C*(eps/(C+1)) < eps).
  { apply (Rmult_lt_reg_r (C+1)); [lra|].
    replace (C*(eps/(C+1))*(C+1)) with (C*eps) by (field; lra). nra. }
  assert (C*r^(ns i) <= C*(eps/(C+1))) by (apply Rmult_le_compat_l; lra). lra.
Qed.

Lemma close_eventually_converges : forall p q,
  (forall eps, 0 < eps -> exists I, forall i, (I <= i)%nat -> close eps (p i) q) ->
  point_converges p q.
Proof.
  intros p q H. split; intros eps He;
    destruct (H (eps/2) ltac:(lra)) as [I HI]; exists I;
    intros i Hi; specialize (HI i Hi); unfold close in HI; unfold Rdist; lra.
Qed.

Lemma geometric_point_limit : forall p q ns C r,
  indices_tend_to_infinity ns -> 0 <= C -> 0 <= r < 1 ->
  (exists I, forall i, (I <= i)%nat -> close (C*r^(ns i)) (p i) q) ->
  point_converges p q.
Proof.
  intros p q ns C r Hns HC Hr [I HI]. apply close_eventually_converges.
  intros eps He. destruct (geometric_indices_decay r C ns Hr HC Hns eps He) as [J HJ].
  exists (Nat.max I J); intros i Hi.
  specialize (HI i ltac:(lia)); specialize (HJ i ltac:(lia)). unfold close in *; split; lra.
Qed.

Theorem periodic_beginning_code_limits : forall ns j,
  indices_tend_to_infinity ns ->
  point_converges (fun k => u_code (orbit_shift j (periodic_word (ns k)))) (u_code (beginning_word j)) /\
  point_converges (fun k => v_code (orbit_shift j (periodic_word (ns k)))) (v_code (beginning_word j)).
Proof.
  intros ns j Hns. destruct (Hns j) as [I HI].
  assert (Hdecay := indices_subtract_fixed ns j Hns).
  split; apply (geometric_point_limit _ _ (fun k => (ns k-j)%nat) (2/5) (1/900));
    try exact Hdecay; try lra; exists I; intros i Hi;
    pose proof (periodic_beginning_codes (ns i) j (ns i-j) ltac:(specialize (HI i Hi); lia)); tauto.
Qed.

Theorem periodic_ending_code_limits : forall ns r,
  indices_tend_to_infinity ns ->
  point_converges (fun k => u_code (orbit_shift (ns k-r) (periodic_word (ns k)))) (u_code (ending_word r)) /\
  point_converges (fun k => v_code (orbit_shift (ns k-r) (periodic_word (ns k)))) (v_code (ending_word r)).
Proof.
  intros ns r Hns. destruct (Hns r) as [I HI].
  assert (Hdecay := indices_subtract_fixed ns r Hns).
  split; apply (geometric_point_limit _ _ (fun k => (ns k-r)%nat) (2/5) (1/900));
    try exact Hdecay; try lra; exists I; intros i Hi;
    pose proof (periodic_ending_codes (ns i) (ns i-r) r (ns i-r)
      ltac:(specialize (HI i Hi); lia) ltac:(lia)); tauto.
Qed.

Theorem periodic_bulk_code_limits : forall ns js,
  (forall i, (js i <= ns i)%nat) ->
  indices_tend_to_infinity js -> indices_tend_to_infinity (fun i => (ns i-js i)%nat) ->
  point_converges (fun k => u_code (orbit_shift (js k) (periodic_word (ns k)))) (u_code constant_word) /\
  point_converges (fun k => v_code (orbit_shift (js k) (periodic_word (ns k)))) (v_code constant_word).
Proof.
  intros ns js Hle Hj Hr.
  assert (Hdecay := indices_minimum js (fun i => (ns i-js i)%nat) Hj Hr).
  split; apply (geometric_point_limit _ _ (fun k => Nat.min (js k) (ns k-js k)) (2/5) (1/900));
    try exact Hdecay; try lra; exists 0%nat; intros i Hi;
    pose proof (periodic_bulk_codes (ns i) (js i) (Nat.min (js i) (ns i-js i))
      ltac:(lia) ltac:(specialize (Hle i); lia)); tauto.
Qed.

Lemma matrix_cv_from_vanishing_difference : forall U V L,
  matrix_cv V L ->
  (forall eps, 0 < eps -> exists I, forall i, (I <= i)%nat -> opnorm (sub2 (U i) (V i)) < eps) ->
  matrix_cv U L.
Proof.
  intros U V L HC Hd eps He.
  destruct (HC (eps/2) ltac:(lra)) as [I HI].
  destruct (Hd (eps/2) ltac:(lra)) as [J HJ].
  exists (Nat.max I J); intros i Hi.
  specialize (HI i ltac:(lia)); specialize (HJ i ltac:(lia)).
  pose proof (opnorm_difference_triangle (U i) (V i) L); lra.
Qed.

Theorem periodic_beginning_fiber_limits : forall ns j,
  indices_tend_to_infinity ns ->
  matrix_cv (fun k => orbit_product j (periodic_word (ns k))) (matrix_power constant_return j).
Proof.
  intros ns j Hns eps He.
  destruct (geometric_indices_decay (1/600) constant_power_bound (fun k => (ns k-j)%nat)
    ltac:(lra) constant_power_bound_nonnegative (indices_subtract_fixed ns j Hns) eps He) as [I HI].
  destruct (Hns j) as [J HJ]. exists (Nat.max I J); intros i Hi.
  pose proof (periodic_prefix_rotation_error (ns i) j (HJ i ltac:(lia))) as Hb.
  specialize (HI i ltac:(lia)); lra.
Qed.

Theorem periodic_ending_suffix_limits : forall ns r,
  indices_tend_to_infinity ns ->
  matrix_cv (fun k => orbit_product (S r) (orbit_shift (ns k-r) (periodic_word (ns k)))) (defect_product r).
Proof.
  intros ns r Hns eps He.
  destruct (geometric_indices_decay (1/600) (opnorm (defect_product r)) ns
    ltac:(lra) (opnorm_nonnegative _) Hns eps He) as [I HI].
  destruct (Hns r) as [J HJ]. exists (Nat.max I J); intros i Hi.
  pose proof (periodic_suffix_error (ns i) (ns i-r) r (ns i)
    ltac:(specialize (HJ i ltac:(lia)); lia) ltac:(lia)) as Hb.
  specialize (HI i ltac:(lia)); lra.
Qed.

Theorem periodic_bulk_fiber_limits : forall ns js S,
  (forall i, (js i <= ns i)%nat) ->
  indices_tend_to_infinity (fun i => (ns i-js i)%nat) ->
  matrix_cv (fun i => matrix_power constant_rotation (js i)) S ->
  matrix_cv (fun i => orbit_product (js i) (periodic_word (ns i)))
    (mul2 (mul2 constant_basis S) (adj2 constant_basis)).
Proof.
  intros ns js S Hle Hremaining HC.
  apply (matrix_cv_from_vanishing_difference _ (fun i => matrix_power constant_return (js i))).
  - assert (Hrec : (fun i => matrix_power constant_return (js i)) =
      (fun i => mul2 (mul2 constant_basis (matrix_power constant_rotation (js i))) (adj2 constant_basis))).
    { apply functional_extensionality; intro i; apply constant_power_reconstruction. }
    rewrite Hrec. apply matrix_cv_right_product, matrix_cv_left_product; exact HC.
  - intros eps He.
    destruct (geometric_indices_decay (1/600) constant_power_bound (fun i => (ns i-js i)%nat)
      ltac:(lra) constant_power_bound_nonnegative Hremaining eps He) as [I HI].
    exists I; intros i Hi. pose proof (periodic_prefix_rotation_error (ns i) (js i) (Hle i)).
    specialize (HI i Hi); lra.
Qed.

Definition phase_limit_original S :=
  mul2 (mul2 (mul2 constant_basis S) (adj2 constant_basis)) defect_limit.

Theorem periodic_returns_matrix_limit : forall ns S,
  indices_tend_to_infinity ns ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  matrix_cv (fun i => periodic_return (ns i)) (phase_limit_original S).
Proof.
  intros ns S Hns HS.
  apply (matrix_cv_from_vanishing_difference _
    (fun i => mul2 (mul2 (mul2 constant_basis (matrix_power constant_rotation (ns i)))
      (adj2 constant_basis)) defect_limit)).
  - apply matrix_cv_right_product, matrix_cv_right_product, matrix_cv_left_product; exact HS.
  - intros eps He. destruct (geometric_indices_decay (1/500) 2 ns ltac:(lra) ltac:(lra) Hns eps He)
      as [I HI]. exists I; intros i Hi.
    pose proof (periodic_return_asymptotic_bound (ns i)) as Hb.
    rewrite constant_power_reconstruction in Hb. specialize (HI i Hi); lra.
Qed.

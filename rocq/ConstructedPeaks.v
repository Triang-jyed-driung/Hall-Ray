From Stdlib Require Import Reals Psatz Lia Arith List ZArith.
From HallRay Require Import MatrixAlgebra EuclideanNorm MatrixLimits FiberProducts
  SymbolicCoding SymbolicCocycle DefectLimit PeriodicReturns PeriodicHeights WordPrefixes PrefixFibers
  NestedWords BlockConstruction ConstructedWords ConstructedCodes ConstructedFibers
  TwoSidedCoding LatticeReturns PeriodicWords ReturnBlocks.
Open Scope R_scope.

Lemma construction_code_error_scale : forall n,
  (2/5)*(1/900)^n <= (1/600)^n.
Proof.
  intro n; pose proof (pow_incr (1/900) (1/600) n ltac:(lra)).
  pose proof (pow_le (1/900) n ltac:(lra)); lra.
Qed.
Lemma close_enlarge : forall a b p q, a <= b -> close a p q -> close b p q.
Proof. intros a b p q Hab [Hx Hy]; split; lra. Qed.

Definition constructed_block_close nm states i eps :=
  Rabs (return_block_peak nm
    (orbit_shift (construction_start states i) (construction_word states))
    (orbit_product (construction_start states i) (construction_word states))
    (construction_repetitions states (S i)*S (construction_order states (S i))) -
    return_block_peak nm (periodic_word (construction_order states (S i)))
    (stage_fiber (construction_prefix states i) (construction_order states i))
    (construction_repetitions states (S i)*S (construction_order states (S i)))) <= eps.

Theorem constructed_block_comparison_radius : forall nm H delta K,
  0 < delta < 1 -> 1 <= K -> forall eps, 0 < eps ->
  exists eta, 0 < eta /\ forall tolerances states,
  states 0%nat=initial_block_state ->
  (forall i, state_index (states i)=i) ->
  (forall i, good_block_state delta tolerances (states i)) ->
  (forall i, block_step nm H delta K (states i) (states (S i))) ->
  forall i, (1/600)^(construction_order states i) < eta ->
    constructed_block_close nm states i eps.
Proof.
  intros nm H delta K Hd HK eps He.
  destruct (uniform_return_block_comparison nm (2*K+1) eps He) as [rho [Hr Hcompare]].
  set (eta := Rmin 1 rho/(6*K+1)).
  assert (Hden : 0 < 6*K+1) by lra.
  exists eta; split.
  { unfold eta; apply Rdiv_lt_0_compat; [apply Rmin_pos; lra|exact Hden]. }
  intros tolerances states Hinitial Hindices Hgood Hsteps i Hsmall.
  set (t := (1/600)^(construction_order states i)).
  assert (Ht : 0 <= t) by (unfold t; apply pow_le; lra).
  assert (Hscaled : (6*K+1)*t < Rmin 1 rho).
  { apply (Rmult_lt_reg_r (/ (6*K+1))); [apply Rinv_0_lt_compat; exact Hden|].
    field_simplify; unfold t,eta in *; nra. }
  assert (Hone : 6*K*t <= 1) by (pose proof (Rmin_l 1 rho); nra).
  assert (Hrho : 6*K*t <= rho) by (pose proof (Rmin_r 1 rho); nra).
  assert (Hcode : (2/5)*(1/900)^(construction_order states i) <= rho).
  { pose proof (construction_code_error_scale (construction_order states i)); pose proof (Rmin_r 1 rho); unfold t in *; nra. }
  unfold constructed_block_close; apply Hcompare.
  - apply orbit_product_unimodular.
  - apply stage_fiber_unimodular.
  - intros j Hj.
    destruct (construction_cumulative_fiber_bounds nm H delta K tolerances states
      Hindices Hgood Hsteps Hd HK i j ltac:(lia) Hone) as [HA HF].
    split; [exact HA|]. split; [exact HF|].
    destruct (construction_block_codes nm H delta K tolerances states Hinitial Hindices Hgood Hsteps i j Hj)
      as [Hu Hv].
    rewrite <-orbit_shift_add.
    split; [eapply close_enlarge; [exact Hcode|exact Hu]|].
    split; [eapply close_enlarge; [exact Hcode|exact Hv]|].
    eapply Rle_trans; [apply (construction_cumulative_fiber_error nm H delta K tolerances states
      Hindices Hgood Hsteps Hd HK i j ltac:(lia))|exact Hrho].
Qed.

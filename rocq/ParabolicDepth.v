From Stdlib Require Import Reals Psatz Lia FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices LatticeBasis
  FiberProducts EuclideanNorm MatrixLimits SymbolicCoding SymbolicCocycle DefectLimit
  EllipticConjugacy EllipticContinuity NormalizedFlow TwoSidedCoding LatticeReturns
  LimitingWords LimitingRepresentatives LimitingFamilies LatticeSystole SystoleContinuity SystoleCurves
  NormGeometry PaperTarget DaniCorrespondence DaniSystole Matrix3Limits
  CuspVectors BulkFlow.
Open Scope R_scope.

Definition degeneration_constant nm X := bulk_frame_scale*(bulk_contraction_bound nm X+1).
Lemma degeneration_constant_positive : forall nm X, 0 < degeneration_constant nm X.
Proof.
  intros nm X; unfold degeneration_constant. apply Rmult_lt_0_compat.
  - apply frame_normalizer_positive.
  - pose proof (bulk_contraction_bound_positive nm X); lra.
Qed.

Theorem limiting_peak_parabolic_scale_bound : forall nm X A HX HA Hell,
  0 < a21 A -> elliptic_scale A <= 1 ->
  /(degeneration_constant nm X*elliptic_scale A) <= limiting_peak nm X A HX HA Hell.
Proof.
  intros nm X A HX HA Hell Hc Hsmall.
  pose proof (elliptic_scale_positive A Hell Hc) as Hp.
  destruct (bulk_fiber_small_vector nm X A HA Hell Hc) as [E [R [HE [HRd [HRo Hvector]]]]].
  set (p := elliptic_scale A) in *.
  set (r := /sqrt p).
  assert (Hroot : 0 < sqrt p) by (apply sqrt_lt_R0; exact Hp).
  assert (Hr : 0 < r) by (apply Rinv_0_lt_compat; exact Hroot).
  assert (Hr1 : 1 <= r).
  { pose proof (pow2_sqrt p ltac:(lra)) as Hsq.
    assert (Hsqrt : sqrt p <= 1) by (pose proof (sqrt_pos p); nra).
    pose proof (Rinv_le_contravar (sqrt p) 1 Hroot Hsqrt).
    rewrite Rinv_1 in H; exact H. }
  assert (Ht : 0 <= ln r).
  { apply (logarithmic_scale_bound r 0 Hr). rewrite exp_0; exact Hr1. }
  set (L := mul3 (diagonal_flow (ln r)) (bulk_representative (mul2 X E) R 0)).
  pose proof (limiting_peak_bounds_bulk_flow nm X A HX HA Hell E R (ln r) HE HRd HRo Ht) as Hpeak.
  change (cusp_height nm L <= limiting_peak nm X A HX HA Hell) in Hpeak.
  assert (Hdet : det3 L = 1).
  { unfold L. rewrite mul3_determinant,diagonal_flow_unimodular,bulk_representative_unimodular;
      try exact HRd; [ring|rewrite det2_mul,HX,(elliptic_circle_unimodular A E HA Hell HE); ring]. }
  assert (Hsys : systole nm L <= degeneration_constant nm X*p).
  { unfold L,bulk_representative. rewrite diagonal_flow_zero,mul3_id_left.
    unfold diagonal_flow; rewrite exp_ln by exact Hr.
    eapply Rle_trans; [apply normalized_first_vector_systole_bound; exact Hr|].
    fold bulk_unstable bulk_stable bulk_frame_scale.
    unfold degeneration_constant.
    replace (bulk_frame_scale*(bulk_contraction_bound nm X+1)*p) with
      (bulk_frame_scale*((bulk_contraction_bound nm X+1)*p)) by ring.
    apply Rmult_le_compat_l; [apply Rlt_le,frame_normalizer_positive|].
    apply square_root_balancing_bound; try assumption.
    - split; assumption.
    - pose proof (bulk_contraction_bound_positive nm X); lra.
    - apply length2_nonnegative. }
  pose proof (systole_positive nm L Hdet) as Hpositive.
  pose proof (degeneration_constant_positive nm X) as HC.
  eapply Rle_trans; [|exact Hpeak]. unfold cusp_height.
  apply Rinv_le_contravar; assumption.
Qed.

Lemma elliptic_sine_sequence_at_boundary : forall U A,
  matrix_cv U A -> (trace2 A)^2 = 4 ->
  Un_cv (fun i => elliptic_sine (U i)) 0.
Proof.
  intros U A HU Htrace.
  pose proof (matrix_cv_trace U A HU) as Ht.
  assert (Hcos : Un_cv (fun i => elliptic_cosine (U i)) (elliptic_cosine A)).
  { unfold elliptic_cosine,Rdiv; scalar_cv_algebra. }
  assert (Hcos2 : (elliptic_cosine A)^2 = 1) by (unfold elliptic_cosine; nra).
  assert (Hsin : Un_cv (fun i => sqrt (1-elliptic_cosine (U i)^2)) (sqrt (1-elliptic_cosine A^2))).
  { apply scalar_cv_square_root; [|rewrite Hcos2; lra].
    replace (fun i => 1-elliptic_cosine (U i)^2) with
      (fun i => 1-elliptic_cosine (U i)*elliptic_cosine (U i)) by
      (apply functional_extensionality; intro i; simpl; ring).
    replace (1-elliptic_cosine A^2) with (1-elliptic_cosine A*elliptic_cosine A) by (simpl; ring).
    scalar_cv_algebra. }
  rewrite Hcos2 in Hsin. replace (1-1) with 0 in Hsin by ring.
  rewrite sqrt_0 in Hsin; exact Hsin.
Qed.

Theorem elliptic_scale_tends_to_zero_at_parabolic : forall U A,
  matrix_cv U A -> 0 < a21 A -> (trace2 A)^2 = 4 ->
  Un_cv (fun i => elliptic_scale (U i)) 0.
Proof.
  intros U A HU Hc Htrace.
  pose proof (elliptic_sine_sequence_at_boundary U A HU Htrace) as Hs.
  pose proof (proj1 (proj2 (proj2 (matrix_cv_coordinates U A HU)))) as H21.
  assert (Hinv := scalar_cv_inverse _ _ H21 ltac:(lra)).
  pose proof (CV_mult _ _ _ _ Hs Hinv) as Hratio.
  replace (0* /a21 A) with 0 in Hratio by ring.
  pose proof (scalar_cv_square_root _ _ Hratio ltac:(lra)) as Hroot.
  rewrite sqrt_0 in Hroot; exact Hroot.
Qed.

Theorem limiting_peaks_diverge_at_parabolic : forall nm X HX U A
  (HUdet : forall i, det2 (U i) = 1)
  (HUell : forall i, Rabs (trace2 (U i)) < 2),
  matrix_cv U A -> 0 < a21 A -> (trace2 A)^2 = 4 ->
  forall B, exists I, forall i, (I <= i)%nat ->
    B < limiting_peak nm X (U i) HX (HUdet i) (HUell i).
Proof.
  intros nm X HX U A HUdet HUell HU Hc Htrace B.
  pose proof (elliptic_scale_tends_to_zero_at_parabolic U A HU Hc Htrace) as Hscale.
  pose proof (proj1 (proj2 (proj2 (matrix_cv_coordinates U A HU)))) as H21.
  destruct (H21 (a21 A/2) ltac:(lra)) as [I HI].
  set (C := degeneration_constant nm X).
  assert (HC : 0 < C) by apply degeneration_constant_positive.
  set (e := Rmin 1 (/(C*(Rabs B+2)))).
  assert (He : 0 < e).
  { apply Rmin_pos; [lra|apply Rinv_0_lt_compat; pose proof (Rabs_pos B); nra]. }
  destruct (Hscale e He) as [J HJ]. exists (Nat.max I J); intros i Hi.
  specialize (HI i ltac:(lia)); unfold Rdist in HI; apply Rabs_def2 in HI.
  assert (Hci : 0 < a21 (U i)) by lra.
  pose proof (elliptic_scale_positive (U i) (HUell i) Hci) as Hp.
  specialize (HJ i ltac:(lia)); unfold Rdist in HJ; rewrite Rminus_0_r,Rabs_right in HJ by lra.
  assert (Hsmall : elliptic_scale (U i) <= 1) by (pose proof (Rmin_l 1 (/(C*(Rabs B+2)))) as Hmin; change (e <= 1) in Hmin; lra).
  pose proof (limiting_peak_parabolic_scale_bound nm X (U i) HX (HUdet i) (HUell i) Hci Hsmall) as Hbound.
  eapply Rlt_le_trans; [|exact Hbound]. fold C.
  assert (Heps : elliptic_scale (U i) < /(C*(Rabs B+2))).
  { pose proof (Rmin_r 1 (/(C*(Rabs B+2)))) as Hmin.
    change (e <= /(C*(Rabs B+2))) in Hmin; lra. }
  assert (Hprod : C*elliptic_scale (U i)*(Rabs B+2) < 1).
  { apply (Rmult_lt_compat_r (C*(Rabs B+2))) in Heps; [|pose proof (Rabs_pos B); nra].
    replace (/(C*(Rabs B+2))*(C*(Rabs B+2))) with 1 in Heps by (field; pose proof (Rabs_pos B); nra).
    nra. }
  apply (Rmult_lt_reg_r (C*elliptic_scale (U i))); [nra|].
  replace (/(C*elliptic_scale (U i))*(C*elliptic_scale (U i))) with 1 by (field; nra).
  pose proof (Rmult_le_compat_r (C*elliptic_scale (U i)) B (Rabs B) ltac:(nra) (Rle_abs B)) as Habs.
  assert (Hpositive : 0 < C*elliptic_scale (U i)) by nra. nra.
Qed.

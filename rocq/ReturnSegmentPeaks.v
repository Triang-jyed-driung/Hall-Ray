From Stdlib Require Import Reals Psatz Lia ClassicalDescription FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra ReturnIdentity ReturnBranches StableBranches
  FiberProducts EuclideanNorm MatrixLimits SymbolicCoding StableCoding TwoSidedCoding
  LatticeReturns LatticeBasis LatticeSystole SystoleCurves SystoleContinuity
  Matrix3Limits EllipticContinuity RoofLimits IntervalPeaks PaperTarget.
Open Scope R_scope.

Definition return_segment_peak nm z E :=
  match excluded_middle_informative (det2 E = 1) with
  | left HE => interval_peak nm (orbit_frame z E) (orbit_roof_time z)
      (orbit_frame_unimodular z E HE) (Rlt_le _ _ (Rlt_trans _ _ _ Rlt_0_1 (orbit_roof_time_gt_one z)))
  | right _ => 0
  end.

Lemma return_segment_peak_valid : forall nm z E HE Htime,
  return_segment_peak nm z E =
    interval_peak nm (orbit_frame z E) (orbit_roof_time z) (orbit_frame_unimodular z E HE) Htime.
Proof.
  intros nm z E HE Htime; unfold return_segment_peak.
  destruct (excluded_middle_informative (det2 E = 1)); [apply interval_peak_unique_proofs|contradiction].
Qed.
Theorem return_segment_peak_upper : forall nm z E t,
  det2 E = 1 -> 0 <= t <= orbit_roof_time z ->
  cusp_height nm (mul3 (diagonal_flow t) (orbit_frame z E)) <= return_segment_peak nm z E.
Proof.
  intros nm z E t HE Ht.
  assert (Htime : 0 <= orbit_roof_time z) by (pose proof (orbit_roof_time_gt_one z); lra).
  rewrite (return_segment_peak_valid nm z E HE Htime); apply interval_peak_upper; exact Ht.
Qed.
Theorem return_segment_peak_attained : forall nm z E,
  det2 E = 1 -> exists t, 0 <= t <= orbit_roof_time z /\
    return_segment_peak nm z E = cusp_height nm (mul3 (diagonal_flow t) (orbit_frame z E)).
Proof.
  intros nm z E HE.
  assert (Htime : 0 <= orbit_roof_time z) by (pose proof (orbit_roof_time_gt_one z); lra).
  rewrite (return_segment_peak_valid nm z E HE Htime); apply interval_peak_attained.
Qed.

Lemma code_abs_lower_bound : forall z, 1/102 <= Rabs (snd (u_code z)).
Proof.
  intro z; pose proof (u_code_inside (bi_shift z)) as HU.
  rewrite u_code_recursion; unfold branch; destruct (z 0%Z).
  - change (1/102 <= Rabs (1/da (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z))))).
    pose proof (da_bounds _ _ HU) as Hd.
    rewrite Rabs_right by (apply Rle_ge,Rlt_le,Rdiv_lt_0_compat; lra).
    unfold Rdiv; rewrite !Rmult_1_l.
    apply Rinv_le_contravar; lra.
  - change (1/102 <= Rabs (-1/db (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z))))).
    pose proof (db_bounds _ _ HU) as Hd.
    assert (Hpos : 0 < /db (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z)))) by
      (apply Rinv_0_lt_compat; lra).
    rewrite Rabs_left by (unfold Rdiv; nra).
    replace (-(-1/db (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z))))) with
      (/db (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z)))) by (field; lra).
    unfold Rdiv; rewrite Rmult_1_l.
    apply Rinv_le_contravar; lra.
Qed.

Lemma limit_code_second_nonzero : forall z a,
  point_converges (fun i => u_code (z i)) a -> snd a <> 0.
Proof.
  intros z a [_ Hcv] Ha.
  assert (Habs : Un_cv (fun i => Rabs (snd (u_code (z i)))) (Rabs (snd a))).
  { apply continuity_seq; [reg|exact Hcv]. }
  pose proof (scalar_limit_nonnegative (fun i => Rabs (snd (u_code (z i)))-1/102)
    (Rabs (snd a)-1/102) (CV_minus _ _ _ _ Habs (real_constant_cv (1/102)))
    ltac:(intro i; pose proof (code_abs_lower_bound (z i)); lra)) as H.
  rewrite Ha,Rabs_R0 in H; lra.
Qed.

Definition limiting_branch (a : point) := if Rlt_dec 0 (snd a) then true else false.
Lemma code_branch_converges_to_point : forall z a,
  point_converges (fun i => u_code (z i)) a -> snd a <> 0 ->
  exists N, forall i, (N <= i)%nat -> z i 0%Z = limiting_branch a.
Proof.
  intros z a [_ Hcv] Ha. unfold limiting_branch.
  destruct (Rlt_dec 0 (snd a)) as [Hpos|Hneg].
  - destruct (Hcv (snd a/2) ltac:(lra)) as [N HN]. exists N; intros i Hi.
    specialize (HN i Hi); unfold Rdist in HN; apply Rabs_def2 in HN.
    destruct (z i 0%Z) eqn:Hz; [reflexivity|].
    pose proof (proj2 (unstable_code_branch_sign (z i)) Hz); lra.
  - destruct (Hcv (-snd a/2) ltac:(lra)) as [N HN]. exists N; intros i Hi.
    specialize (HN i Hi); unfold Rdist in HN; apply Rabs_def2 in HN.
    destruct (z i 0%Z) eqn:Hz; [|reflexivity].
    pose proof (proj1 (unstable_code_branch_sign (z i)) Hz); lra.
Qed.

Definition point_roof_limit a b := ln (current_roof_scale (limiting_branch a) a b).
Theorem roof_limit_to_code_points : forall z a b,
  point_converges (fun i => u_code (z i)) a ->
  point_converges (fun i => v_code (z i)) b -> stable_inside b -> snd a <> 0 ->
  Un_cv (fun i => orbit_roof_time (z i)) (point_roof_limit a b).
Proof.
  intros z a b Hu Hv Hb Ha.
  destruct (code_branch_converges_to_point z a Hu Ha) as [N HN].
  assert (Hscale : Un_cv (fun i => orbit_roof_scale (z i)) (current_roof_scale (limiting_branch a) a b)).
  { eapply scalar_cv_eventual_agreement; [exact (current_roof_scale_sequence_limit (limiting_branch a)
      (fun i => u_code (z i)) (fun i => v_code (z i)) a b Hu Hv Hb Ha)|].
    exists N; intros i Hi; rewrite orbit_roof_from_current_codes,HN by exact Hi; reflexivity. }
  unfold orbit_roof_time,point_roof_limit; apply continuity_seq; [|exact Hscale].
  apply positive_log_continuous,NormalizedFlow.positive_cube_root_positive.
Qed.

Theorem return_segment_peak_sequence_limit : forall nm z E A h
  (HE : forall i, det2 (E i) = 1) (HA : det3 A = 1) (Hh : 0 <= h),
  matrix3_cv (fun i => orbit_frame (z i) (E i)) A ->
  Un_cv (fun i => orbit_roof_time (z i)) h ->
  Un_cv (fun i => return_segment_peak nm (z i) (E i)) (interval_peak nm A h HA Hh).
Proof.
  intros nm z E A h HE HA Hh Hframe Hroof.
  assert (Htimes : forall i, 0 <= orbit_roof_time (z i)) by
    (intro i; pose proof (orbit_roof_time_gt_one (z i)); lra).
  assert (Hsame : (fun i => return_segment_peak nm (z i) (E i)) =
    (fun i => interval_peak nm (orbit_frame (z i) (E i)) (orbit_roof_time (z i))
      (orbit_frame_unimodular (z i) (E i) (HE i)) (Htimes i))).
  { apply functional_extensionality; intro i; apply return_segment_peak_valid. }
  rewrite Hsame; apply interval_peaks_sequence_limit; assumption.
Qed.

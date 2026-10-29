From Stdlib Require Import Reals Psatz Lia Arith Classical ClassicalChoice.
From HallRay Require Import MatrixAlgebra ReturnIdentity FiberProducts EuclideanNorm MatrixLimits
  SymbolicCoding StableCoding TwoSidedCoding LatticeReturns
  PeriodicReturns LimitingConvergence CompactMatrices Matrix3Limits ChartCompactness
  NormalizedFlow RoofLimits IntervalPeaks ReturnSegmentPeaks
  PaperTarget SystoleCurves.
Open Scope R_scope.

Lemma scalar_cv_transfer_difference : forall u v l,
  Un_cv u l ->
  (forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Rabs (u n-v n) < eps) -> Un_cv v l.
Proof.
  intros u v l Hu Hd eps He.
  destruct (Hu (eps/2) ltac:(lra)) as [I HI]; destruct (Hd (eps/2) ltac:(lra)) as [J HJ].
  exists (Nat.max I J); intros n Hn; specialize (HI n ltac:(lia)); specialize (HJ n ltac:(lia)).
  unfold Rdist in *; apply Rabs_def2 in HI,HJ; apply Rabs_def1; lra.
Qed.
Lemma point_cv_transfer_geometric : forall u v a ns,
  point_converges u a -> indices_tend_to_infinity ns ->
  (forall i, close ((1/2)^(ns i)) (u i) (v i)) -> point_converges v a.
Proof.
  intros u v a ns [Hu1 Hu2] Hns Hclose.
  assert (Hdecay : forall eps, 0 < eps -> exists I, forall i, (I <= i)%nat -> (1/2)^(ns i) < eps).
  { intros eps He; destruct (geometric_indices_decay (1/2) 1 ns ltac:(lra) ltac:(lra) Hns eps He)
      as [I HI]; exists I; intros i Hi; specialize (HI i Hi); lra. }
  split.
  - apply (scalar_cv_transfer_difference (fun i => fst (u i))); [exact Hu1|].
    intros eps He; destruct (Hdecay eps He) as [I HI]; exists I; intros i Hi.
    specialize (HI i Hi); specialize (Hclose i); unfold close in Hclose; lra.
  - apply (scalar_cv_transfer_difference (fun i => snd (u i))); [exact Hu2|].
    intros eps He; destruct (Hdecay eps He) as [I HI]; exists I; intros i Hi.
    specialize (HI i Hi); specialize (Hclose i); unfold close in Hclose; lra.
Qed.

Record segment_pair := SegmentPair {
  left_word : biword; right_word : biword; left_fiber : mat2; right_fiber : mat2
}.
Definition segment_pair_good nm M eps rho p :=
  det2 (left_fiber p) = 1 /\ det2 (right_fiber p) = 1 /\
  opnorm (left_fiber p) <= M /\ opnorm (right_fiber p) <= M /\
  close rho (u_code (left_word p)) (u_code (right_word p)) /\
  close rho (v_code (left_word p)) (v_code (right_word p)) /\
  opnorm (sub2 (left_fiber p) (right_fiber p)) <= rho /\
  eps <= Rabs (return_segment_peak nm (left_word p) (left_fiber p)-
    return_segment_peak nm (right_word p) (right_fiber p)).

Theorem return_segment_peaks_uniform_continuity : forall nm M eps,
  0 < eps -> exists rho, 0 < rho /\ forall z w Q V,
    det2 Q = 1 -> det2 V = 1 -> opnorm Q <= M -> opnorm V <= M ->
    close rho (u_code z) (u_code w) -> close rho (v_code z) (v_code w) ->
    opnorm (sub2 Q V) <= rho ->
    Rabs (return_segment_peak nm z Q-return_segment_peak nm w V) < eps.
Proof.
  intros nm M eps He; apply NNPP; intro Hno.
  assert (Hchoose : forall i, exists p, segment_pair_good nm M eps ((1/2)^i) p).
  { intro i; apply NNPP; intro Hnone; apply Hno; exists ((1/2)^i); split; [apply pow_lt; lra|].
    intros z w Q V HQ HV HMQ HMV Hu Hv HQV.
    destruct (Rlt_dec (Rabs (return_segment_peak nm z Q-return_segment_peak nm w V)) eps) as [Hyes|Hbad]; auto.
    exfalso; apply Hnone; exists (SegmentPair z w Q V); unfold segment_pair_good; simpl.
    repeat first [assumption|split]; lra. }
  destruct (@choice nat segment_pair _ Hchoose) as [p Hp].
  set (z := fun i => left_word (p i)); set (w := fun i => right_word (p i)).
  set (Q := fun i => left_fiber (p i)); set (V := fun i => right_fiber (p i)).
  assert (HQ : forall i, det2 (Q i) = 1) by (intro i; exact (proj1 (Hp i))).
  assert (HV : forall i, det2 (V i) = 1) by (intro i; exact (proj1 (proj2 (Hp i)))).
  assert (HMQ : forall i, opnorm (Q i) <= M) by (intro i; exact (proj1 (proj2 (proj2 (Hp i))))).
  destruct (bounded_chart_parameters_subsequence
    (fun i => u_code (z i)) (fun i => v_code (z i)) Q (fun _ => 0) M 0
    (fun i => u_code_inside (z i)) (fun i => v_code_inside (z i)) HQ HMQ
    ltac:(intro i; change (Rabs 0 <= 0); rewrite Rabs_R0; lra))
    as [ns [a [b [F [t [Hns [Ha [Hb [HF [Hu [Hv [HQcv Hzero]]]]]]]]]]]].
  assert (Huw : point_converges (fun i => u_code (w (ns i))) a).
  { apply (point_cv_transfer_geometric (fun i => u_code (z (ns i))) _ a ns Hu Hns).
    intro i; exact (proj1 (proj2 (proj2 (proj2 (proj2 (Hp (ns i))))))). }
  assert (Hvw : point_converges (fun i => v_code (w (ns i))) b).
  { apply (point_cv_transfer_geometric (fun i => v_code (z (ns i))) _ b ns Hv Hns).
    intro i; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (Hp (ns i)))))))). }
  assert (HVcv : matrix_cv (fun i => V (ns i)) F).
  { apply (matrix_cv_from_vanishing_difference _ (fun i => Q (ns i)) F HQcv).
    intros e Hpos; destruct (geometric_indices_decay (1/2) 1 ns ltac:(lra) ltac:(lra) Hns e Hpos) as [I HI].
    exists I; intros i Hi; specialize (HI i Hi).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (Hp (ns i))))))))) as Hdiff.
    change (opnorm (sub2 (Q (ns i)) (V (ns i))) <= (1/2)^(ns i)) in Hdiff.
    rewrite opnorm_difference_symmetric; lra. }
  assert (Hanonzero : snd a <> 0) by (apply (limit_code_second_nonzero (fun i => z (ns i)) a Hu)).
  assert (Hroofz := roof_limit_to_code_points (fun i => z (ns i)) a b Hu Hv Hb Hanonzero).
  assert (Hroofw := roof_limit_to_code_points (fun i => w (ns i)) a b Huw Hvw Hb Hanonzero).
  set (A := normalized_frame (fst a) (snd a) (fst b) (snd b) F).
  set (h := point_roof_limit a b).
  assert (HA : det3 A = 1) by (apply normalized_frame_unimodular; assumption).
  assert (Hh : 0 <= h).
  { apply (scalar_limit_nonnegative _ _ Hroofz); intro i; pose proof (orbit_roof_time_gt_one (z (ns i))); lra. }
  assert (Hframez : matrix3_cv (fun i => orbit_frame (z (ns i)) (Q (ns i))) A).
  { apply normalized_frame_sequence_limit; try assumption.
    pose proof (chart_weight_bounds _ _ _ _ Ha Hb); lra. }
  assert (Hframew : matrix3_cv (fun i => orbit_frame (w (ns i)) (V (ns i))) A).
  { apply normalized_frame_sequence_limit; try assumption.
    pose proof (chart_weight_bounds _ _ _ _ Ha Hb); lra. }
  pose proof (return_segment_peak_sequence_limit nm (fun i => z (ns i)) (fun i => Q (ns i)) A h
    (fun i => HQ (ns i)) HA Hh Hframez Hroofz) as Hzpeak.
  pose proof (return_segment_peak_sequence_limit nm (fun i => w (ns i)) (fun i => V (ns i)) A h
    (fun i => HV (ns i)) HA Hh Hframew Hroofw) as Hwpeak.
  destruct (Hzpeak (eps/2) ltac:(lra)) as [I HI]; destruct (Hwpeak (eps/2) ltac:(lra)) as [J HJ].
  set (i := Nat.max I J). specialize (HI i ltac:(unfold i; lia)); specialize (HJ i ltac:(unfold i; lia)).
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (Hp (ns i))))))))) as Hbad.
  change (eps <= Rabs (return_segment_peak nm (z (ns i)) (Q (ns i))-
    return_segment_peak nm (w (ns i)) (V (ns i)))) in Hbad.
  unfold Rdist in HI,HJ; apply Rabs_def2 in HI,HJ.
  assert (Hsmall : Rabs (return_segment_peak nm (z (ns i)) (Q (ns i))-
    return_segment_peak nm (w (ns i)) (V (ns i))) < eps) by (apply Rabs_def1; lra).
  lra.
Qed.

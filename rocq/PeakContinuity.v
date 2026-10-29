From Stdlib Require Import Reals Psatz Lia Arith ClassicalChoice.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits DefectLimit PeriodicReturns
  EllipticConjugacy EllipticContinuity RotationDensity LimitingConvergence CompactMatrices
  LimitingFamilies PeriodicHeights PeakConvergence PaperTarget SystoleCurves.
Open Scope R_scope.

Lemma periodic_peak_unique_proofs : forall nm n X HX HX' Hell Hell',
  periodic_peak nm n X HX Hell = periodic_peak nm n X HX' Hell'.
Proof.
  intros nm n X HX HX' Hell Hell'.
  destruct (periodic_peak_lub nm n X HX Hell) as [Hb Hleast].
  destruct (periodic_peak_lub nm n X HX' Hell') as [Hb' Hleast'].
  apply Rle_antisym; [apply Hleast|apply Hleast']; assumption.
Qed.
Lemma limiting_peak_unique_proofs : forall nm X A HX HX' HA HA' Hell Hell',
  limiting_peak nm X A HX HA Hell = limiting_peak nm X A HX' HA' Hell'.
Proof.
  intros nm X A HX HX' HA HA' Hell Hell'.
  destruct (limiting_peak_lub nm X A HX HA Hell) as [Hb Hleast].
  destruct (limiting_peak_lub nm X A HX' HA' Hell') as [Hb' Hleast'].
  apply Rle_antisym; [apply Hleast|apply Hleast']; assumption.
Qed.

Lemma matrix_limit_eventually_elliptic : forall U A,
  matrix_cv U A -> Rabs (trace2 A) < 2 ->
  exists I, forall i, (I <= i)%nat -> Rabs (trace2 (U i)) < 2.
Proof.
  intros U A HU HA. pose proof (matrix_cv_trace U A HU) as Htrace.
  destruct (Htrace ((2-Rabs (trace2 A))/2) ltac:(lra)) as [I HI].
  exists I; intros i Hi. specialize (HI i Hi); unfold Rdist in HI.
  pose proof (Rabs_triang (trace2 (U i)-trace2 A) (trace2 A)) as H.
  replace (trace2 (U i)-trace2 A+trace2 A) with (trace2 (U i)) in H by ring. lra.
Qed.
Lemma cofinal_offset : forall I, indices_tend_to_infinity (fun i => (i+I)%nat).
Proof. intros I N; exists N; intros i Hi; lia. Qed.

Theorem periodic_peak_approximation_at_phase : forall nm X S HX HA Hphase,
  det2 S = 1 -> orthogonal2 S -> forall eps N, 0 < eps ->
  exists n, (N <= n)%nat /\ Rabs (trace2 (periodic_return n)) < 2 /\
    opnorm (sub2 (matrix_power constant_rotation n) S) < eps /\
    forall Hn, Rabs (periodic_peak nm n X HX Hn-
      limiting_peak nm X (phase_limit_original S) HX HA Hphase) < eps.
Proof.
  intros nm X S HX HA Hphase HSd HSo eps N He.
  destruct (constant_rotation_dense_subsequence S HSd HSo) as [ns [Hns HS]].
  destruct (matrix_limit_eventually_elliptic _ _ (periodic_returns_matrix_limit ns S Hns HS) Hphase)
    as [I HI].
  set (ms := fun i => ns (i+I)%nat).
  assert (Hms : indices_tend_to_infinity ms) by exact (cofinal_composition ns _ Hns (cofinal_offset I)).
  assert (Hrotation : matrix_cv (fun i => matrix_power constant_rotation (ms i)) S)
    by exact (matrix_cv_subsequence _ _ _ HS (cofinal_offset I)).
  assert (Hell : forall i, Rabs (trace2 (periodic_return (ms i))) < 2)
    by (intro i; apply HI; lia).
  pose proof (periodic_peaks_converge nm ms (fun _ => X) X S (fun _ => HX) Hell HX HA Hphase
    Hms (matrix_cv_constant X) Hrotation) as Hpeaks.
  destruct (Hrotation eps He) as [J HJ]. destruct (Hpeaks eps He) as [K HK].
  destruct (Hms N) as [M HM]. set (i := Nat.max J (Nat.max K M)).
  exists (ms i); split; [apply HM; unfold i; lia|]. split; [apply Hell|].
  split; [apply HJ; unfold i; lia|]. intros Hn.
  rewrite (periodic_peak_unique_proofs nm (ms i) X HX HX Hn (Hell i)).
  exact (HK i ltac:(unfold i; lia)).
Qed.

Theorem limiting_peaks_joint_sequence_limit : forall nm X Y R S
  (HX : forall i, det2 (X i) = 1) (HY : det2 Y = 1)
  (HA : forall i, det2 (phase_limit_original (R i)) = 1)
  (Hell : forall i, Rabs (trace2 (phase_limit_original (R i))) < 2)
  (HAlimit : det2 (phase_limit_original S) = 1)
  (Helllimit : Rabs (trace2 (phase_limit_original S)) < 2),
  (forall i, det2 (R i) = 1) -> (forall i, orthogonal2 (R i)) ->
  matrix_cv X Y -> matrix_cv R S ->
  Un_cv (fun i => limiting_peak nm (X i) (phase_limit_original (R i)) (HX i) (HA i) (Hell i))
    (limiting_peak nm Y (phase_limit_original S) HY HAlimit Helllimit).
Proof.
  intros nm X Y R S HX HY HA Hell HAlimit Helllimit HRd HRo HXY HRS.
  assert (Hchoose : forall i, exists n, (i <= n)%nat /\
    Rabs (trace2 (periodic_return n)) < 2 /\
    opnorm (sub2 (matrix_power constant_rotation n) (R i)) < (1/2)^i /\
    forall Hn, Rabs (periodic_peak nm n (X i) (HX i) Hn-
      limiting_peak nm (X i) (phase_limit_original (R i)) (HX i) (HA i) (Hell i)) < (1/2)^i).
  { intro i. apply periodic_peak_approximation_at_phase; try assumption;
      [apply HRd|apply HRo|apply pow_lt; lra]. }
  destruct (@choice nat nat _ Hchoose) as [ns Hns].
  assert (Hindices : indices_tend_to_infinity ns).
  { intros N; exists N; intros i Hi; specialize (Hns i); lia. }
  set (Hperiodic := fun i => proj1 (proj2 (Hns i))).
  assert (Hrotation : matrix_cv (fun i => matrix_power constant_rotation (ns i)) S).
  { apply (matrix_cv_from_vanishing_difference _ R S HRS).
    intros eps He.
    destruct (pow_lt_1_zero (1/2) ltac:(rewrite Rabs_right; lra) eps He) as [N HN].
    exists N; intros i Hi. specialize (HN i Hi).
    rewrite Rabs_right in HN by (apply Rle_ge,pow_le; lra).
    pose proof (proj1 (proj2 (proj2 (Hns i)))); lra. }
  pose proof (periodic_peaks_converge nm ns X Y S HX Hperiodic HY HAlimit Helllimit
    Hindices HXY Hrotation) as Hpeak.
  intros eps He. destruct (Hpeak (eps/2) ltac:(lra)) as [I HI].
  destruct (pow_lt_1_zero (1/2) ltac:(rewrite Rabs_right; lra) (eps/2) ltac:(lra)) as [J HJ].
  exists (Nat.max I J); intros i Hi.
  specialize (HI i ltac:(lia)); specialize (HJ i ltac:(lia)).
  rewrite Rabs_right in HJ by (apply Rle_ge,pow_le; lra).
  pose proof (proj2 (proj2 (proj2 (Hns i))) (Hperiodic i)) as Hnear.
  unfold Rdist in *; apply Rabs_def2 in HI,Hnear. apply Rabs_def1; lra.
Qed.

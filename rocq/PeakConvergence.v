From Stdlib Require Import Reals Psatz Lia Arith Classical.
From HallRay Require Import MatrixAlgebra EuclideanNorm MatrixLimits DefectLimit PeriodicReturns
  LimitingConvergence CompactMatrices PositionalSubsequences EllipticConjugacy EllipticContinuity
  LimitingFamilies PeriodicHeights CirclePeaks LowerApproximations PeakUpperLimits
  PaperTarget SystoleCurves.
Open Scope R_scope.

Theorem limiting_peak_near : forall nm X A HX HA Hell eps,
  0 < eps -> exists L, limiting_representative X A L /\
    limiting_peak nm X A HX HA Hell-eps < cusp_height nm L.
Proof.
  intros nm X A HX HA Hell eps He.
  destruct (classic (exists L, limiting_representative X A L /\
    limiting_peak nm X A HX HA Hell-eps < cusp_height nm L)) as [Hyes|Hno]; auto.
  destruct (limiting_peak_lub nm X A HX HA Hell) as [_ Hleast].
  assert (Hb : is_upper_bound (limiting_height_values nm X A) (limiting_peak nm X A HX HA Hell-eps)).
  { intros y [L [HL Hy]]; subst y.
    destruct (Rle_dec (cusp_height nm L) (limiting_peak nm X A HX HA Hell-eps)) as [Hyes|Hbad]; auto.
    exfalso; apply Hno; exists L; split; [exact HL|lra]. }
  specialize (Hleast _ Hb); lra.
Qed.

Theorem periodic_peaks_lower_limit : forall nm ns X Y S
  (HX : forall i, det2 (X i) = 1)
  (Hell : forall i, Rabs (trace2 (periodic_return (ns i))) < 2)
  (HY : det2 Y = 1) (HA : det2 (phase_limit_original S) = 1)
  (Hphase : Rabs (trace2 (phase_limit_original S)) < 2),
  indices_tend_to_infinity ns -> matrix_cv X Y ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  forall eps, 0 < eps -> exists I, forall i, (I <= i)%nat ->
    limiting_peak nm Y (phase_limit_original S) HY HA Hphase-eps <
      periodic_peak nm (ns i) (X i) (HX i) (Hell i).
Proof.
  intros nm ns X Y S HX Hell HY HA Hphase Hns HXY HS eps He.
  set (D := limiting_peak nm Y (phase_limit_original S) HY HA Hphase).
  apply NNPP; intro Hno.
  assert (Hbad : arbitrarily_late (fun i => periodic_peak nm (ns i) (X i) (HX i) (Hell i) <= D-eps)).
  { intro I. apply NNPP; intro Hnone. apply Hno; exists I; intros i Hi.
    destruct (Rlt_dec (D-eps) (periodic_peak nm (ns i) (X i) (HX i) (Hell i))) as [Hyes|Hbad]; auto.
    exfalso; apply Hnone; exists i; split; [exact Hi|lra]. }
  destruct (arbitrarily_late_subsequence _ Hbad) as [ss [Hss Hbadss]].
  destruct (limiting_peak_near nm Y (phase_limit_original S) HY HA Hphase (eps/2) ltac:(lra))
    as [L [HL Hnear]].
  change (D-eps/2 < cusp_height nm L) in Hnear.
  destruct (limiting_model_height_lower_approximation nm
    (fun i => ns (ss i)) (fun i => X (ss i)) Y S (fun i => HX (ss i)) (fun i => Hell (ss i))
    HY HA Hphase (cofinal_composition ns ss Hns Hss) (matrix_cv_subsequence X Y ss HXY Hss)
    (matrix_cv_subsequence _ _ ss HS Hss) L HL) as [ks [h [Hks [Hb Hcv]]]].
  assert (Hlimit : cusp_height nm L <= D-eps).
  { apply (scalar_limit_upper_bound h _ _ Hcv); intro i.
    specialize (Hb i); specialize (Hbadss (ks i)); lra. }
  lra.
Qed.

Theorem periodic_peaks_converge : forall nm ns X Y S
  (HX : forall i, det2 (X i) = 1)
  (Hell : forall i, Rabs (trace2 (periodic_return (ns i))) < 2)
  (HY : det2 Y = 1) (HA : det2 (phase_limit_original S) = 1)
  (Hphase : Rabs (trace2 (phase_limit_original S)) < 2),
  indices_tend_to_infinity ns -> matrix_cv X Y ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  Un_cv (fun i => periodic_peak nm (ns i) (X i) (HX i) (Hell i))
    (limiting_peak nm Y (phase_limit_original S) HY HA Hphase).
Proof.
  intros nm ns X Y S HX Hell HY HA Hphase Hns HXY HS eps He.
  destruct (periodic_peaks_upper_limit nm ns X Y S HX Hell HY HA Hphase Hns HXY HS eps He)
    as [I HI].
  destruct (periodic_peaks_lower_limit nm ns X Y S HX Hell HY HA Hphase Hns HXY HS eps He)
    as [J HJ].
  exists (Nat.max I J); intros i Hi. specialize (HI i ltac:(lia)); specialize (HJ i ltac:(lia)).
  unfold Rdist; apply Rabs_def1; lra.
Qed.

From Stdlib Require Import Reals Psatz Lia Arith Classical ClassicalChoice.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices FiberProducts
  EuclideanNorm MatrixLimits LatticeBasis LatticeReturns LatticeSystole SystoleCurves
  PeriodicReturns Matrix3Limits ChartCompactness CompactMatrices RoofLimits CirclePeaks LowerApproximations
  PositionalSubsequences PaperTarget.
Open Scope R_scope.

Lemma flowing_basis_unimodular : forall A t,
  det3 A = 1 -> det3 (mul3 (diagonal_flow t) A) = 1.
Proof. intros A t HA; rewrite mul3_determinant,diagonal_flow_unimodular,HA; ring. Qed.

Definition interval_height_values nm A h y := exists t,
  0 <= t <= h /\ y = cusp_height nm (mul3 (diagonal_flow t) A).

Lemma interval_height_nonempty : forall nm A h,
  0 <= h -> exists y, interval_height_values nm A h y.
Proof.
  intros nm A h Hh. exists (cusp_height nm (mul3 (diagonal_flow 0) A)); exists 0; split; [lra|reflexivity].
Qed.
Lemma interval_height_maximum : forall nm A h,
  det3 A = 1 -> 0 <= h -> exists t, 0 <= t <= h /\ forall s, 0 <= s <= h ->
    cusp_height nm (mul3 (diagonal_flow s) A) <= cusp_height nm (mul3 (diagonal_flow t) A).
Proof.
  intros nm A h HA Hh.
  destruct (compact_curve_height_maximum nm (scaled_flow_curve A) 0 h Hh
    (scaled_flow_curve_continuous A) ltac:(intro t; apply flowing_basis_unimodular; exact HA))
    as [t [Ht Hb]]. exists t; auto.
Qed.
Lemma interval_height_bounded : forall nm A h,
  det3 A = 1 -> 0 <= h -> bound (interval_height_values nm A h).
Proof.
  intros nm A h HA Hh. destruct (interval_height_maximum nm A h HA Hh) as [t [Ht Hb]].
  exists (cusp_height nm (mul3 (diagonal_flow t) A)); intros y [s [Hs Hy]]; subst y; apply Hb; exact Hs.
Qed.

Definition interval_peak nm A h (HA : det3 A = 1) (Hh : 0 <= h) :=
  proj1_sig (completeness (interval_height_values nm A h)
    (interval_height_bounded nm A h HA Hh) (interval_height_nonempty nm A h Hh)).
Lemma interval_peak_lub : forall nm A h HA Hh,
  is_lub (interval_height_values nm A h) (interval_peak nm A h HA Hh).
Proof. intros; apply (proj2_sig (completeness _ _ _)). Qed.
Theorem interval_peak_upper : forall nm A h HA Hh t,
  0 <= t <= h -> cusp_height nm (mul3 (diagonal_flow t) A) <= interval_peak nm A h HA Hh.
Proof.
  intros nm A h HA Hh t Ht. destruct (interval_peak_lub nm A h HA Hh) as [Hb _].
  apply Hb; exists t; auto.
Qed.
Theorem interval_peak_attained : forall nm A h HA Hh,
  exists t, 0 <= t <= h /\ interval_peak nm A h HA Hh = cusp_height nm (mul3 (diagonal_flow t) A).
Proof.
  intros nm A h HA Hh. destruct (interval_height_maximum nm A h HA Hh) as [t [Ht Hb]].
  exists t; split; [exact Ht|]; apply Rle_antisym.
  - destruct (interval_peak_lub nm A h HA Hh) as [_ Hleast]. apply Hleast.
    intros y [s [Hs Hy]]; subst y; apply Hb; exact Hs.
  - apply interval_peak_upper; exact Ht.
Qed.
Lemma interval_peak_unique_proofs : forall nm A h HA HA' Hh Hh',
  interval_peak nm A h HA Hh = interval_peak nm A h HA' Hh'.
Proof.
  intros nm A h HA HA' Hh Hh'.
  destruct (interval_peak_lub nm A h HA Hh) as [Hb Hleast].
  destruct (interval_peak_lub nm A h HA' Hh') as [Hb' Hleast'].
  apply Rle_antisym; [apply Hleast|apply Hleast']; assumption.
Qed.

Lemma finite_scalar_abs_bound : forall u N,
  exists C, 0 <= C /\ forall n, (n < N)%nat -> Rabs (u n) <= C.
Proof.
  intros u N; induction N as [|N [C [HC Hb]]].
  - exists 0; split; [lra|intros; lia].
  - exists (C+Rabs (u N)); split; [pose proof (Rabs_pos (u N)); lra|].
    intros n Hn; destruct (Nat.eq_dec n N); [subst n; lra|specialize (Hb n ltac:(lia)); pose proof (Rabs_pos (u N)); lra].
Qed.
Lemma convergent_scalar_abs_bounded : forall u l,
  Un_cv u l -> exists C, 0 < C /\ forall n, Rabs (u n) <= C.
Proof.
  intros u l Hu; destruct (Hu 1 ltac:(lra)) as [N HN].
  destruct (finite_scalar_abs_bound u N) as [C [HC Hb]].
  exists (C+Rabs l+1); split; [pose proof (Rabs_pos l); lra|]. intros n.
  destruct (lt_dec n N) as [Hsmall|Hlarge].
  - specialize (Hb n Hsmall); pose proof (Rabs_pos l); lra.
  - specialize (HN n ltac:(lia)); unfold Rdist in HN.
    pose proof (Rabs_triang_inv (u n) l); lra.
Qed.
Lemma interval_times_closed_limit : forall hs h ts t,
  Un_cv hs h -> Un_cv ts t -> (forall i, 0 <= ts i <= hs i) -> 0 <= t <= h.
Proof.
  intros hs h ts t Hh Ht Hrange; split.
  - apply (scalar_limit_nonnegative ts t Ht); intro i; exact (proj1 (Hrange i)).
  - pose proof (scalar_limit_nonnegative (fun i => hs i-ts i) (h-t)
      (CV_minus _ _ _ _ Hh Ht) ltac:(intro i; specialize (Hrange i); lra)); lra.
Qed.
Lemma clipped_interval_times_limit : forall hs h t,
  Un_cv hs h -> (forall i, 0 <= hs i) -> 0 <= t <= h ->
  Un_cv (fun i => Rmin t (hs i)) t /\ forall i, 0 <= Rmin t (hs i) <= hs i.
Proof.
  intros hs h t Hh Hpos Ht; split.
  - intros eps He; destruct (Hh eps He) as [N HN]; exists N; intros i Hi.
    specialize (HN i Hi); unfold Rdist in *.
    pose proof (minimum_constant_lipschitz t (hs i) h) as H.
    rewrite (Rmin_left t h) in H by lra; lra.
  - intro i; split; [apply Rmin_glb; [lra|apply Hpos]|apply Rmin_r].
Qed.

Theorem interval_peaks_sequence_limit : forall nm U A hs h
  (HU : forall i, det3 (U i) = 1) (HA : det3 A = 1)
  (Hhs : forall i, 0 <= hs i) (Hh : 0 <= h),
  matrix3_cv U A -> Un_cv hs h ->
  Un_cv (fun i => interval_peak nm (U i) (hs i) (HU i) (Hhs i)) (interval_peak nm A h HA Hh).
Proof.
  intros nm U A hs h HU HA Hhs Hh Hcv Hhcv.
  set (P := interval_peak nm A h HA Hh).
  assert (Hupper : forall eps, 0 < eps -> exists I, forall i, (I <= i)%nat ->
    interval_peak nm (U i) (hs i) (HU i) (Hhs i) < P+eps).
  { intros eps He; apply NNPP; intro Hno.
    assert (Hbad : arbitrarily_late (fun i => P+eps <= interval_peak nm (U i) (hs i) (HU i) (Hhs i))).
    { intro I; apply NNPP; intro Hnone; apply Hno; exists I; intros i Hi.
      destruct (Rlt_dec (interval_peak nm (U i) (hs i) (HU i) (Hhs i)) (P+eps)); auto.
      exfalso; apply Hnone; exists i; split; [exact Hi|lra]. }
    destruct (arbitrarily_late_subsequence _ Hbad) as [ss [Hss Hbadss]].
    destruct (@choice nat R (fun i t => 0 <= t <= hs i /\
      interval_peak nm (U i) (hs i) (HU i) (Hhs i) = cusp_height nm (mul3 (diagonal_flow t) (U i)))
      (fun i => interval_peak_attained nm (U i) (hs i) (HU i) (Hhs i))) as [ts Hts].
    destruct (convergent_scalar_abs_bounded hs h Hhcv) as [C [HC Hb]].
    destruct (bounded_real_subsequence (fun i => ts (ss i)) C
      ltac:(intro i; pose proof (proj1 (Hts (ss i))) as Hti; pose proof (Hb (ss i));
        rewrite Rabs_right by lra; pose proof (Rle_abs (hs (ss i))); lra))
      as [rs [t [Hrs Ht]]].
    set (ks := fun i => ss (rs i)).
    assert (Hks : indices_tend_to_infinity ks) by exact (cofinal_composition ss rs Hss Hrs).
    assert (Hclosed : 0 <= t <= h).
    { apply (interval_times_closed_limit (fun i => hs (ks i)) h (fun i => ts (ks i)) t
        (scalar_cv_subsequence hs h ks Hhcv Hks) Ht); intro i; exact (proj1 (Hts (ks i))). }
    assert (Hmat : matrix3_cv (fun i => mul3 (diagonal_flow (ts (ks i))) (U (ks i))) (mul3 (diagonal_flow t) A)).
    { apply matrix3_cv_product; [apply diagonal_flow_sequence_limit; exact Ht|exact (matrix3_cv_subsequence U A ks Hcv Hks)]. }
    pose proof (cusp_height_sequence_limit nm _ _ (flowing_basis_unimodular A t HA) Hmat) as Hheight.
    assert (Hlow : P+eps <= cusp_height nm (mul3 (diagonal_flow t) A)).
    { pose proof (CV_minus _ _ _ _ Hheight (real_constant_cv (P+eps))) as Hdiff.
      assert (Hnonnegative : forall i,
        0 <= cusp_height nm (mul3 (diagonal_flow (ts (ks i))) (U (ks i)))-(P+eps)).
      { intro i; pose proof (Hbadss (rs i)) as Hbadi.
        change (P+eps <= interval_peak nm (U (ks i)) (hs (ks i)) (HU (ks i)) (Hhs (ks i))) in Hbadi.
        rewrite (proj2 (Hts (ks i))) in Hbadi; lra. }
      pose proof (scalar_limit_nonnegative _ _ Hdiff Hnonnegative); lra. }
    pose proof (interval_peak_upper nm A h HA Hh t Hclosed); fold P in H; lra. }
  assert (Hlower : forall eps, 0 < eps -> exists I, forall i, (I <= i)%nat ->
    P-eps < interval_peak nm (U i) (hs i) (HU i) (Hhs i)).
  { intros eps He.
    destruct (interval_peak_attained nm A h HA Hh) as [t [Ht Hvalue]].
    destruct (clipped_interval_times_limit hs h t Hhcv Hhs Ht) as [Htime Htimes].
    assert (Hmat : matrix3_cv (fun i => mul3 (diagonal_flow (Rmin t (hs i))) (U i)) (mul3 (diagonal_flow t) A)).
    { apply matrix3_cv_product; [apply diagonal_flow_sequence_limit; exact Htime|exact Hcv]. }
    pose proof (cusp_height_sequence_limit nm _ _ (flowing_basis_unimodular A t HA) Hmat) as Hheight.
    rewrite <- Hvalue in Hheight; fold P in Hheight.
    destruct (Hheight eps He) as [I HI]; exists I; intros i Hi; specialize (HI i Hi).
    pose proof (interval_peak_upper nm (U i) (hs i) (HU i) (Hhs i) (Rmin t (hs i)) (Htimes i)).
    unfold Rdist in HI; apply Rabs_def2 in HI; lra. }
  intros eps He; destruct (Hupper eps He) as [I HI]; destruct (Hlower eps He) as [J HJ].
  exists (Nat.max I J); intros i Hi; specialize (HI i ltac:(lia)); specialize (HJ i ltac:(lia)).
  unfold Rdist; apply Rabs_def1; lra.
Qed.

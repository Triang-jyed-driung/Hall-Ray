From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices FiberProducts
  EuclideanNorm MatrixLimits SymbolicCoding SymbolicCocycle TwoSidedCoding LatticeReturns
  LatticeBasis LatticeOrbit LatticeSystole SystoleContinuity SystoleCurves
  IntervalPeaks ReturnSegmentPeaks UniformSegmentComparison StableForgetting PeriodicWords PeriodicReturns
  PeriodicHeights DefectLimit PaperTarget.
Open Scope R_scope.

Fixpoint finite_maximum (f : nat -> R) (N : nat) :=
  match N with O => 0 | S n => Rmax (finite_maximum f n) (f n) end.

Lemma finite_maximum_member : forall f N j,
  (j < N)%nat -> f j <= finite_maximum f N.
Proof.
  intros f N; induction N as [|N IH]; intros j Hj; [lia|]. cbn [finite_maximum].
  destruct (Nat.eq_dec j N) as [Hsame|Hdiff].
  - subst j; apply Rmax_r.
  - eapply Rle_trans; [apply IH; lia|apply Rmax_l].
Qed.
Lemma finite_maximum_attained : forall f N,
  (0 < N)%nat -> (forall j, (j < N)%nat -> 0 < f j) ->
  exists j, (j < N)%nat /\ finite_maximum f N = f j.
Proof.
  intros f N; induction N as [|N IH]; intros HN Hpos; [lia|].
  destruct N as [|N].
  - exists 0%nat; split; [lia|]. cbn [finite_maximum]. rewrite Rmax_right; [reflexivity|specialize (Hpos 0%nat ltac:(lia)); lra].
  - destruct (IH ltac:(lia) ltac:(intros j Hj; apply Hpos; lia)) as [j [Hj Hvalue]].
    change (exists j, (j < S (S N))%nat /\ Rmax (finite_maximum f (S N)) (f (S N)) = f j).
    destruct (Rle_dec (finite_maximum f (S N)) (f (S N))) as [Hle|Hle].
    + exists (S N); split; [lia|rewrite Rmax_right; auto].
    + exists j; split; [lia|rewrite Rmax_left by lra; exact Hvalue].
Qed.
Lemma maximum_comparison : forall a b c d eps,
  Rabs (a-c) <= eps -> Rabs (b-d) <= eps ->
  Rabs (Rmax a b-Rmax c d) <= eps.
Proof.
  intros a b c d eps H1 H2.
  apply absolute_difference_sandwich in H1,H2.
  pose proof (Rmax_l a b); pose proof (Rmax_r a b); pose proof (Rmax_l c d); pose proof (Rmax_r c d).
  assert (Hupper : Rmax a b <= Rmax c d+eps) by (apply Rmax_lub; lra).
  assert (Hlower : Rmax c d <= Rmax a b+eps) by (apply Rmax_lub; lra).
  apply Rabs_le; split; lra.
Qed.
Lemma finite_maximum_comparison : forall f g N eps,
  0 <= eps -> (forall j, (j < N)%nat -> Rabs (f j-g j) <= eps) ->
  Rabs (finite_maximum f N-finite_maximum g N) <= eps.
Proof.
  intros f g N; induction N as [|N IH]; intros eps He Hb.
  - cbn [finite_maximum]; replace (0-0) with 0 by ring; rewrite Rabs_R0; exact He.
  - cbn [finite_maximum]; apply maximum_comparison.
    + apply IH; [exact He|intros; apply Hb; lia].
    + apply Hb; lia.
Qed.

Lemma orbit_product_unimodular : forall n z, det2 (orbit_product n z) = 1.
Proof. intros n z; rewrite orbit_product_matches_future; apply factor_product_unimodular. Qed.
Lemma orbit_times_monotone : forall z n m, (n <= m)%nat -> orbit_time n z <= orbit_time m z.
Proof.
  intros z n m Hnm; induction Hnm; [lra|pose proof (orbit_time_increasing m z); lra].
Qed.

Theorem orbit_height_segment_identity : forall nm z E n r,
  det2 E = 1 ->
  lattice_height_orbit nm (orbit_frame z E) (orbit_time n z+r) =
    cusp_height nm (mul3 (diagonal_flow r) (orbit_frame (orbit_shift n z) (mul2 E (orbit_product n z)))).
Proof.
  intros nm z E n r HE. unfold lattice_height_orbit,cusp_height; f_equal.
  apply systole_same_lattice.
  - apply flowing_basis_unimodular,orbit_frame_unimodular; exact HE.
  - apply flowing_basis_unimodular,orbit_frame_unimodular.
    rewrite det2_mul,HE,orbit_product_unimodular; ring.
  - apply orbit_lattice_return.
Qed.

Lemma return_segment_peak_positive : forall nm z E,
  det2 E = 1 -> 0 < return_segment_peak nm z E.
Proof.
  intros nm z E HE.
  pose proof (return_segment_peak_upper nm z E 0 HE ltac:(pose proof (orbit_roof_time_gt_one z); lra)) as Hb.
  assert (Hpos : 0 < cusp_height nm (mul3 (diagonal_flow 0) (orbit_frame z E))).
  { unfold cusp_height; apply Rinv_0_lt_compat,systole_positive,flowing_basis_unimodular,orbit_frame_unimodular; exact HE. }
  lra.
Qed.
Definition return_block_peak nm z E N := finite_maximum
  (fun j => return_segment_peak nm (orbit_shift j z) (mul2 E (orbit_product j z))) N.

Lemma finite_return_time_cover : forall z N t,
  (0 < N)%nat -> 0 <= t <= orbit_time N z ->
  exists j, (j < N)%nat /\ orbit_time j z <= t <= orbit_time (S j) z.
Proof.
  intros z N; induction N as [|N IH]; intros t HN Ht; [lia|].
  destruct (Rle_dec (orbit_time N z) t) as [Hle|Hle].
  - exists N; split; [lia|lra].
  - destruct N as [|N]; [simpl in Hle; lra|].
    destruct (IH t ltac:(lia) ltac:(lra)) as [j [Hj Hjtime]]. exists j; split; [lia|exact Hjtime].
Qed.

Theorem return_block_peak_upper : forall nm z E N t,
  det2 E = 1 -> (0 < N)%nat -> 0 <= t <= orbit_time N z ->
  lattice_height_orbit nm (orbit_frame z E) t <= return_block_peak nm z E N.
Proof.
  intros nm z E N t HE HN Ht.
  destruct (finite_return_time_cover z N t HN Ht) as [j [Hj Htime]].
  replace t with (orbit_time j z+(t-orbit_time j z)) by ring.
  rewrite orbit_height_segment_identity by exact HE. unfold return_block_peak.
  eapply Rle_trans; [apply return_segment_peak_upper|exact (finite_maximum_member
    (fun k => return_segment_peak nm (orbit_shift k z) (mul2 E (orbit_product k z))) N j Hj)].
  - rewrite det2_mul,HE,orbit_product_unimodular; ring.
  - rewrite orbit_time_successor in Htime; lra.
Qed.
Theorem return_block_peak_attained : forall nm z E N,
  det2 E = 1 -> (0 < N)%nat -> exists t, 0 <= t <= orbit_time N z /\
    return_block_peak nm z E N = lattice_height_orbit nm (orbit_frame z E) t.
Proof.
  intros nm z E N HE HN.
  destruct (finite_maximum_attained
    (fun j => return_segment_peak nm (orbit_shift j z) (mul2 E (orbit_product j z))) N HN
    ltac:(intros j Hj; apply return_segment_peak_positive; rewrite det2_mul,HE,orbit_product_unimodular; ring))
    as [j [Hj Hvalue]].
  assert (HF : det2 (mul2 E (orbit_product j z)) = 1) by (rewrite det2_mul,HE,orbit_product_unimodular; ring).
  destruct (return_segment_peak_attained nm (orbit_shift j z) _ HF) as [r [Hr Hpeak]].
  exists (orbit_time j z+r); split.
  - pose proof (orbit_time_lower_bound j z); pose proof (pos_INR j).
    pose proof (orbit_times_monotone z (S j) N ltac:(lia)) as Htime.
    rewrite orbit_time_successor in Htime; lra.
  - unfold return_block_peak; rewrite Hvalue,Hpeak,orbit_height_segment_identity by exact HE; reflexivity.
Qed.

Theorem periodic_block_peak_returns : forall nm n E HE Hell L,
  (0 < L)%nat -> periodic_block_peak nm n E HE Hell L =
    return_block_peak nm (periodic_word n) E (L*S n).
Proof.
  intros nm n E HE Hell L HL.
  assert (Htime : orbit_time (L*S n) (periodic_word n) = INR L*periodic_word_time n).
  { apply cyclic_word_times; apply periodic_word_return_shift. }
  apply Rle_antisym.
  - destruct (periodic_block_peak_lub nm n E HE Hell L) as [_ Hleast]; apply Hleast.
    intros y [t [Ht Hy]]; subst y. apply return_block_peak_upper; [exact HE|nia|rewrite Htime; exact Ht].
  - destruct (return_block_peak_attained nm (periodic_word n) E (L*S n) HE ltac:(nia)) as [t [Ht Hvalue]].
    rewrite Hvalue; apply periodic_block_value_bound; rewrite <- Htime; exact Ht.
Qed.

Theorem uniform_return_block_comparison : forall nm M eps,
  0 < eps -> exists rho, 0 < rho /\ forall z w E F N,
    det2 E = 1 -> det2 F = 1 ->
    (forall j, (j < N)%nat ->
      opnorm (mul2 E (orbit_product j z)) <= M /\ opnorm (mul2 F (orbit_product j w)) <= M /\
      close rho (u_code (orbit_shift j z)) (u_code (orbit_shift j w)) /\
      close rho (v_code (orbit_shift j z)) (v_code (orbit_shift j w)) /\
      opnorm (sub2 (mul2 E (orbit_product j z)) (mul2 F (orbit_product j w))) <= rho) ->
    Rabs (return_block_peak nm z E N-return_block_peak nm w F N) <= eps.
Proof.
  intros nm M eps He.
  destruct (return_segment_peaks_uniform_continuity nm M eps He) as [rho [Hr Hb]].
  exists rho; split; [exact Hr|]. intros z w E F N HE HF Hclose.
  unfold return_block_peak. apply finite_maximum_comparison; [lra|]. intros j Hj.
  destruct (Hclose j Hj) as [HQ [HV [Hu [Hv Hdiff]]]].
  apply Rlt_le,Hb; try assumption; rewrite det2_mul,orbit_product_unimodular; [rewrite HE|rewrite HF]; ring.
Qed.

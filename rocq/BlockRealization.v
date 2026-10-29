From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices FiberProducts
  EuclideanNorm MatrixLimits SymbolicCoding SymbolicCocycle TwoSidedCoding LatticeReturns
  ReturnBlocks ReturnSegmentPeaks IntervalPeaks Concatenation StableForgetting
  AdjustedPeriodicPeaks DaniCorrespondence PaperTarget ApproximationRealization.
Open Scope R_scope.

Lemma increasing_natural_lower : forall s : nat -> nat,
  (forall i, (s i < s (S i))%nat) -> forall i, (i <= s i)%nat.
Proof. intros s Hs i; induction i; [lia|specialize (Hs i); lia]. Qed.

Theorem block_controls_realize_height : forall nm z s H e,
  (forall i, (s i < s (S i))%nat) -> tends_to_zero e ->
  (forall i, Rabs (return_block_peak nm (orbit_shift (s i) z) (orbit_product (s i) z)
    (s (S i)-s i)-H) <= e i) ->
  has_limsup (lattice_height_orbit nm (orbit_frame z id2)) H.
Proof.
  intros nm z s H e Hs He Hblocks.
  set (T := fun i => orbit_time (s i) z).
  assert (HTincreasing : forall i, T i < T (S i)).
  { intro i; unfold T. pose proof (orbit_time_increasing (s i) z) as Hstep.
    pose proof (orbit_times_monotone z (S (s i)) (s (S i)) ltac:(specialize (Hs i); lia)); lra. }
  assert (HTcofinal : forall R, exists i, R < T i).
  { intro R; destruct (natural_cast_cofinal R) as [i Hi]; exists i.
    pose proof (le_INR i (s i) (increasing_natural_lower s Hs i)).
    pose proof (orbit_time_lower_bound (s i) z). unfold T; lra. }
  assert (Htime : forall i,
    T (S i) = T i+orbit_time (s (S i)-s i) (orbit_shift (s i) z)).
  { intro i; unfold T. replace (s (S i)) with (s i+(s (S i)-s i))%nat at 1 by (specialize (Hs i); lia).
    rewrite PeriodicWords.orbit_time_add; reflexivity. }
  apply (@block_maxima_limsup T HTincreasing HTcofinal
    (lattice_height_orbit nm (orbit_frame z id2)) H e He).
  - intros i t Ht.
    assert (Hlocal : 0 <= t-T i <= orbit_time (s (S i)-s i) (orbit_shift (s i) z)) by
      (specialize (Htime i); lra).
    pose proof (return_block_peak_upper nm (orbit_shift (s i) z) (orbit_product (s i) z)
      (s (S i)-s i) (t-T i) (orbit_product_unimodular _ _)
      ltac:(specialize (Hs i); lia) Hlocal) as Hb.
    assert (Hheight : lattice_height_orbit nm (orbit_frame z id2) t =
      lattice_height_orbit nm (orbit_frame (orbit_shift (s i) z) (orbit_product (s i) z)) (t-T i)).
    { replace t with (orbit_time (s i) z+(t-T i)) at 1 by (unfold T; ring).
      rewrite orbit_height_segment_identity by apply identity_unimodular.
      rewrite mul2_id_left; reflexivity. }
    rewrite Hheight. eapply Rle_trans; [exact Hb|].
    specialize (Hblocks i); apply SystoleContinuity.absolute_difference_sandwich in Hblocks; lra.
  - intro i.
    destruct (return_block_peak_attained nm (orbit_shift (s i) z) (orbit_product (s i) z)
      (s (S i)-s i) (orbit_product_unimodular _ _)
      ltac:(specialize (Hs i); lia)) as [r [Hr Hpeak]].
    exists (T i+r); split; [specialize (Htime i); lra|].
    unfold T. rewrite orbit_height_segment_identity by apply identity_unimodular.
    rewrite mul2_id_left.
    change (H-e i <= lattice_height_orbit nm
      (orbit_frame (orbit_shift (s i) z) (orbit_product (s i) z)) r).
    rewrite <- Hpeak. specialize (Hblocks i); apply SystoleContinuity.absolute_difference_sandwich in Hblocks; lra.
Qed.

Theorem block_controls_realize_approximation : forall nm z s rho e,
  0 < rho -> (forall i, (s i < s (S i))%nat) -> tends_to_zero e ->
  (forall i, Rabs (return_block_peak nm (orbit_shift (s i) z) (orbit_product (s i) z)
    (s (S i)-s i)-height_for_constant rho) <= e i) ->
  ~ rational_vector (u_code z) /\ has_approximation_constant nm (u_code z) rho.
Proof.
  intros nm z s rho e Hr Hs He Hblocks.
  apply symbolic_height_realizes_constant; [exact Hr|].
  exact (block_controls_realize_height nm z s (height_for_constant rho) e Hs He Hblocks).
Qed.

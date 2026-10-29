From Stdlib Require Import Reals Psatz Lia Arith ClassicalChoice FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices FiberProducts
  EuclideanNorm MatrixLimits SymbolicCoding SymbolicCocycle DefectLimit PeriodicReturns
  EllipticConjugacy EllipticContinuity RotationDensity ReturnInfiniteOrder
  TwoSidedCoding LatticeReturns PeriodicWords LimitingWords LimitingFibers LimitingConvergence
  LimitingRepresentatives PositionalLimits Matrix3Limits CompactMatrices RoofLimits
  LimitingFamilies PeriodicHeights CirclePeaks PaperTarget SystoleCurves.
Open Scope R_scope.

Lemma matrix3_cv_eventual_agreement : forall U V L,
  matrix3_cv V L -> (exists N, forall n, (N <= n)%nat -> U n = V n) -> matrix3_cv U L.
Proof.
  intros U V L HV [N Hsame] eps He. destruct (HV eps He) as [I HI].
  exists (Nat.max N I); intros n Hn; rewrite Hsame by lia; apply HI; lia.
Qed.

Lemma minimum_constant_lipschitz : forall c a b,
  Rabs (Rmin c a-Rmin c b) <= Rabs (a-b).
Proof.
  intros c a b. pose proof (Rle_abs (a-b)); pose proof (Rle_abs (b-a)).
  rewrite (Rabs_minus_sym b a) in *.
  destruct (Rle_dec c a), (Rle_dec c b);
    repeat first [rewrite Rmin_left by lra|rewrite Rmin_right by lra];
    apply Rabs_le; split; lra.
Qed.

Theorem clipped_return_times_limit : forall z w t,
  point_converges (fun i => u_code (z i)) (u_code w) ->
  point_converges (fun i => v_code (z i)) (v_code w) ->
  0 <= t <= orbit_roof_time w ->
  Un_cv (fun i => Rmin t (orbit_roof_time (z i))) t /\
    forall i, 0 <= Rmin t (orbit_roof_time (z i)) <= orbit_roof_time (z i).
Proof.
  intros z w t Hu Hv Ht. pose proof (orbit_roof_sequence_limit z w Hu Hv) as Hroof.
  split.
  - intros eps He. destruct (Hroof eps He) as [N HN]. exists N; intros i Hi.
    specialize (HN i Hi); unfold Rdist in *.
    pose proof (minimum_constant_lipschitz t (orbit_roof_time (z i)) (orbit_roof_time w)) as H.
    rewrite (Rmin_left t (orbit_roof_time w)) in H by lra. lra.
  - intro i; split; [apply Rmin_glb; [lra|pose proof (orbit_roof_time_gt_one (z i)); lra]|apply Rmin_r].
Qed.

Lemma bulk_positions_choice : forall ns js,
  indices_tend_to_infinity ns -> exists ks,
  indices_tend_to_infinity ks /\ forall i, (js i+i <= ns (ks i))%nat.
Proof.
  intros ns js Hns.
  assert (Hchoose : forall i, exists k, (i <= k)%nat /\ (js i+i <= ns k)%nat).
  { intro i; destruct (Hns (js i+i)%nat) as [N HN].
    exists (Nat.max i N); split; [lia|apply HN; lia]. }
  destruct (@choice nat nat (fun i k => (i <= k)%nat /\ (js i+i <= ns k)%nat) Hchoose)
    as [ks Hks]. exists ks; split.
  - intros N; exists N; intros i Hi; specialize (Hks i); lia.
  - intro i; exact (proj2 (Hks i)).
Qed.

Theorem limiting_model_matrix_lower_approximation : forall nm ns X Y S
  (HX : forall i, det2 (X i) = 1)
  (Hell : forall i, Rabs (trace2 (periodic_return (ns i))) < 2),
  indices_tend_to_infinity ns -> matrix_cv X Y ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  det2 (phase_limit_original S) = 1 -> Rabs (trace2 (phase_limit_original S)) < 2 ->
  forall L, limiting_representative Y (phase_limit_original S) L ->
  exists ks U, indices_tend_to_infinity ks /\
    (forall i, cusp_height nm (U i) <= periodic_peak nm (ns (ks i)) (X (ks i)) (HX (ks i)) (Hell (ks i))) /\
    matrix3_cv U L.
Proof.
  intros nm ns X Y S HX Hell Hns HXY HS HA Hphase L HL.
  pose proof (periodic_returns_matrix_limit ns S Hns HS) as HP.
  destruct HL as [E j t HE Ht|E r t HE Ht|E R t HE HRd HRo Ht].
  - destruct (elliptic_circles_lower_limit _ _ E HP HA Hphase HE) as [C [HC Hcv]].
    destruct (periodic_beginning_code_limits ns j Hns) as [Hu Hv].
    destruct (clipped_return_times_limit _ _ t Hu Hv Ht) as [Htime Htimes].
    exists (fun i => i), (fun i => periodic_lifted_representative (ns i) j
      (mul2 (X i) (C i)) (Rmin t (orbit_roof_time (orbit_shift j (periodic_word (ns i)))))).
    split; [intros N; exists N; auto|]. split.
    + intro i; apply periodic_peak_bounds_circle; [apply HC|exact (proj1 (Htimes i))].
    + apply beginning_representative_limit; [exact Hns|apply matrix_cv_product; assumption|exact Htime].
  - assert (Hinverse : in_elliptic_circle (phase_limit_original S) (mul2 E (adj2 (phase_limit_original S)))).
    { apply elliptic_circle_product; try assumption. apply elliptic_circle_inverse; try assumption.
      apply elliptic_return_in_circle; assumption. }
    destruct (elliptic_circles_lower_limit _ _ _ HP HA Hphase Hinverse) as [C [HC Hcv]].
    destruct (periodic_ending_code_limits ns r Hns) as [Hu Hv].
    destruct (clipped_return_times_limit _ _ t Hu Hv Ht) as [Htime Htimes].
    set (U := fun i => periodic_lifted_representative (ns i) (ns i-r) (mul2 (X i) (C i))
      (Rmin t (orbit_roof_time (orbit_shift (ns i-r) (periodic_word (ns i)))))).
    exists (fun i => i), U; split; [intros N; exists N; auto|]. split.
    + intro i; apply periodic_peak_bounds_circle; [apply HC|exact (proj1 (Htimes i))].
    + assert (Hcoefficient : matrix_cv (fun i => mul2 (X i) (mul2 (C i) (periodic_return (ns i)))) (mul2 Y E)).
      { pose proof (matrix_cv_product C (fun i => periodic_return (ns i))
          (mul2 E (adj2 (phase_limit_original S))) (phase_limit_original S) Hcv HP) as HCP.
        rewrite mul2_assoc,(adjugate_left_identity _ HA),mul2_id_right in HCP.
        apply matrix_cv_product; assumption. }
      pose proof (ending_representative_limit ns r
        (fun i => mul2 (X i) (mul2 (C i) (periodic_return (ns i)))) (mul2 Y E)
        (fun i => Rmin t (orbit_roof_time (orbit_shift (ns i-r) (periodic_word (ns i))))) t
        Hns Hcoefficient Htime) as Hmodel.
      eapply matrix3_cv_eventual_agreement; [exact Hmodel|].
      destruct (Hns r) as [N HN]. exists N; intros i Hi.
      unfold U, periodic_lifted_representative.
      rewrite (periodic_prefix_from_suffix (ns i) (ns i-r) r ltac:(specialize (HN i Hi); lia)).
      repeat rewrite mul2_assoc; reflexivity.
  - destruct (constant_rotation_dense_subsequence R HRd HRo) as [js [Hjs Hrotation]].
    destruct (bulk_positions_choice ns js Hns) as [ks [Hks Hroom]].
    assert (Hlengths := cofinal_composition ns ks Hns Hks).
    assert (Hphasecv := matrix_cv_subsequence _ _ ks HS Hks).
    assert (HPsub := periodic_returns_matrix_limit (fun i => ns (ks i)) S Hlengths Hphasecv).
    destruct (elliptic_circles_lower_limit _ _ E HPsub HA Hphase HE) as [C [HC Hcv]].
    assert (Hpositions : forall i, (js i <= ns (ks i))%nat) by (intro i; specialize (Hroom i); lia).
    assert (Hremaining : indices_tend_to_infinity (fun i => (ns (ks i)-js i)%nat)).
    { intros N; exists N; intros i Hi; specialize (Hroom i); lia. }
    destruct (periodic_bulk_code_limits (fun i => ns (ks i)) js Hpositions Hjs Hremaining) as [Hu Hv].
    destruct (clipped_return_times_limit _ _ t Hu Hv Ht) as [Htime Htimes].
    exists ks, (fun i => periodic_lifted_representative (ns (ks i)) (js i)
      (mul2 (X (ks i)) (C i)) (Rmin t (orbit_roof_time (orbit_shift (js i) (periodic_word (ns (ks i))))))).
    split; [exact Hks|]. split.
    + intro i; apply periodic_peak_bounds_circle; [apply HC|exact (proj1 (Htimes i))].
    + apply bulk_representative_limit; try assumption.
      apply matrix_cv_product; [exact (matrix_cv_subsequence X Y ks HXY Hks)|exact Hcv].
Qed.

Theorem limiting_model_height_lower_approximation : forall nm ns X Y S
  (HX : forall i, det2 (X i) = 1)
  (Hell : forall i, Rabs (trace2 (periodic_return (ns i))) < 2)
  (HY : det2 Y = 1) (HA : det2 (phase_limit_original S) = 1)
  (Hphase : Rabs (trace2 (phase_limit_original S)) < 2),
  indices_tend_to_infinity ns -> matrix_cv X Y ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  forall L, limiting_representative Y (phase_limit_original S) L ->
  exists ks h, indices_tend_to_infinity ks /\
    (forall i, h i <= periodic_peak nm (ns (ks i)) (X (ks i)) (HX (ks i)) (Hell (ks i))) /\
    Un_cv h (cusp_height nm L).
Proof.
  intros nm ns X Y S HX Hell HY HA Hphase Hns HXY HS L HL.
  destruct (limiting_model_matrix_lower_approximation nm ns X Y S HX Hell Hns HXY HS HA Hphase L HL)
    as [ks [U [Hks [Hbound Hcv]]]].
  exists ks, (fun i => cusp_height nm (U i)); split; [exact Hks|]. split; [exact Hbound|].
  apply cusp_height_sequence_limit; [apply (limiting_representatives_unimodular _ _ _ HY HA Hphase HL)|exact Hcv].
Qed.

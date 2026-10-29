From Stdlib Require Import Reals Psatz Lia Arith FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra ReturnIdentity FiberProducts EuclideanNorm MatrixLimits
  SymbolicCoding SymbolicCocycle DefectLimit PeriodicReturns EllipticConjugacy
  TwoSidedCoding LatticeReturns PeriodicWords LimitingWords LimitingFibers LimitingConvergence
  Matrix3Limits CompactMatrices PositionalSubsequences LimitingRepresentatives PositionalLimits
  EllipticContinuity RoofLimits LimitingFamilies PaperTarget SystoleCurves.
Open Scope R_scope.

Theorem converging_periodic_segments_limit_family : forall ns js X Y E F ts t S,
  indices_tend_to_infinity ns -> (forall i, (js i <= ns i)%nat) ->
  matrix_cv X Y -> matrix_cv E F -> Un_cv ts t ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  det2 (phase_limit_original S) = 1 -> Rabs (trace2 (phase_limit_original S)) < 2 ->
  in_elliptic_circle (phase_limit_original S) F ->
  (forall i, 0 <= ts i <= orbit_roof_time (orbit_shift (js i) (periodic_word (ns i)))) ->
  exists ks L, indices_tend_to_infinity ks /\
    matrix3_cv (fun i => periodic_lifted_representative (ns (ks i)) (js (ks i))
      (mul2 (X (ks i)) (E (ks i))) (ts (ks i))) L /\
    limiting_representative Y (phase_limit_original S) L.
Proof.
  intros ns js X Y E F ts t S Hns Hle HX HE Ht HS HA Hell HF Hinterval.
  pose proof (periodic_returns_matrix_limit ns S Hns HS) as HP.
  pose proof (matrix_cv_product X E Y F HX HE) as Hfiber.
  destruct (periodic_positions_subsequence ns js) as [ks [Hks [Hbegin|[Hend|Hbulk]]]].
  - destruct Hbegin as [j Hj].
    assert (Hlengths := cofinal_composition ns ks Hns Hks).
    destruct (periodic_beginning_code_limits (fun i => ns (ks i)) j Hlengths) as [Hu Hv].
    assert (Htime := scalar_cv_subsequence ts t ks Ht Hks).
    assert (Hclosed : 0 <= t <= orbit_roof_time (beginning_word j)).
    { apply (return_segment_time_closed_limit _ _ _ _ Hu Hv Htime).
      intro i. specialize (Hinterval (ks i)); rewrite Hj in Hinterval; exact Hinterval. }
    exists ks, (beginning_representative (mul2 Y F) j t); split; [exact Hks|]. split.
    + assert (Hsame : (fun i => periodic_lifted_representative (ns (ks i)) (js (ks i))
        (mul2 (X (ks i)) (E (ks i))) (ts (ks i))) =
        (fun i => mul3 (diagonal_flow (ts (ks i)))
          (orbit_frame (orbit_shift j (periodic_word (ns (ks i))))
            (mul2 (mul2 (X (ks i)) (E (ks i))) (orbit_product j (periodic_word (ns (ks i)))))))).
      { apply functional_extensionality; intro i; unfold periodic_lifted_representative; rewrite Hj; reflexivity. }
      rewrite Hsame. apply beginning_representative_limit; [exact Hlengths| |exact Htime].
      exact (matrix_cv_subsequence _ _ ks Hfiber Hks).
    + apply limiting_beginning; assumption.
  - destruct Hend as [r Hr].
    assert (Hposition : forall i, js (ks i) = (ns (ks i)-r)%nat).
    { intro i; specialize (Hle (ks i)); specialize (Hr i); lia. }
    assert (Hlengths := cofinal_composition ns ks Hns Hks).
    destruct (periodic_ending_code_limits (fun i => ns (ks i)) r Hlengths) as [Hu Hv].
    assert (Htime := scalar_cv_subsequence ts t ks Ht Hks).
    assert (Hclosed : 0 <= t <= orbit_roof_time (ending_word r)).
    { apply (return_segment_time_closed_limit _ _ _ _ Hu Hv Htime).
      intro i; specialize (Hinterval (ks i)); rewrite Hposition in Hinterval; exact Hinterval. }
    exists ks, (ending_representative (mul2 (mul2 Y F) (phase_limit_original S)) r t).
    split; [exact Hks|]. split.
    + assert (Hsame : (fun i => periodic_lifted_representative (ns (ks i)) (js (ks i))
        (mul2 (X (ks i)) (E (ks i))) (ts (ks i))) =
        (fun i => mul3 (diagonal_flow (ts (ks i)))
          (orbit_frame (orbit_shift (ns (ks i)-r) (periodic_word (ns (ks i))))
            (mul2 (mul2 (mul2 (X (ks i)) (E (ks i))) (periodic_return (ns (ks i))))
              (adj2 (orbit_product (Nat.succ r) (orbit_shift (ns (ks i)-r) (periodic_word (ns (ks i)))))))))).
      { apply functional_extensionality; intro i; unfold periodic_lifted_representative.
        rewrite (periodic_prefix_from_suffix (ns (ks i)) (js (ks i)) r ltac:(specialize (Hle (ks i)); specialize (Hr i); lia)).
        rewrite Hposition. repeat rewrite mul2_assoc; reflexivity. }
      rewrite Hsame. apply ending_representative_limit; [exact Hlengths| |exact Htime].
      apply matrix_cv_product; [exact (matrix_cv_subsequence _ _ ks Hfiber Hks)|exact (matrix_cv_subsequence _ _ ks HP Hks)].
    + rewrite mul2_assoc. apply limiting_ending; [apply elliptic_circle_right_return; assumption|exact Hclosed].
  - destruct Hbulk as [Hjs Hremaining].
    destruct (special_orthogonal_subsequence (fun i => matrix_power constant_rotation (js (ks i)))
      ltac:(intro i; apply matrix_power_unimodular; exact (proj1 constant_rotation_special_orthogonal))
      ltac:(intro i; apply orthogonal_power; exact (proj2 constant_rotation_special_orthogonal)))
      as [ms [R [Hms [HRd [HRo HRcv]]]]].
    set (qs := fun i => ks (ms i)).
    assert (Hqs : indices_tend_to_infinity qs) by exact (cofinal_composition ks ms Hks Hms).
    assert (Hj := cofinal_composition (fun i => js (ks i)) ms Hjs Hms).
    assert (Hrem := cofinal_composition (fun i => (ns (ks i)-js (ks i))%nat) ms Hremaining Hms).
    destruct (periodic_bulk_code_limits (fun i => ns (qs i)) (fun i => js (qs i))
      (fun i => Hle (qs i)) Hj Hrem) as [Hu Hv].
    assert (Htime := scalar_cv_subsequence ts t qs Ht Hqs).
    assert (Hclosed : 0 <= t <= orbit_roof_time constant_word).
    { apply (return_segment_time_closed_limit _ _ _ _ Hu Hv Htime); intro i; apply Hinterval. }
    exists qs, (bulk_representative (mul2 Y F) R t); split; [exact Hqs|]. split.
    + apply bulk_representative_limit; try assumption.
      * intro i; apply Hle.
      * exact (matrix_cv_subsequence _ _ qs Hfiber Hqs).
    + apply limiting_bulk; assumption.
Qed.

Theorem periodic_segment_family_upper_limit : forall nm ns js X Y E ts S,
  indices_tend_to_infinity ns -> (forall i, (js i <= ns i)%nat) ->
  matrix_cv X Y -> det2 Y = 1 ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  Rabs (trace2 (phase_limit_original S)) < 2 ->
  (forall i, in_elliptic_circle (periodic_return (ns i)) (E i)) ->
  (forall i, 0 <= ts i <= orbit_roof_time (orbit_shift (js i) (periodic_word (ns i)))) ->
  exists ks L, indices_tend_to_infinity ks /\ limiting_representative Y (phase_limit_original S) L /\
    Un_cv (fun i => cusp_height nm (periodic_lifted_representative (ns (ks i)) (js (ks i))
      (mul2 (X (ks i)) (E (ks i))) (ts (ks i)))) (cusp_height nm L).
Proof.
  intros nm ns js X Y E ts S Hns Hle HX HY HS Hell HE Hinterval.
  pose proof (periodic_returns_matrix_limit ns S Hns HS) as HP.
  assert (HA : det2 (phase_limit_original S) = 1) by
    (apply (unimodular_limit _ _ HP); intro i; apply periodic_return_unimodular).
  destruct (elliptic_circles_upper_limit _ _ E HP HA Hell HE) as [ms [F [Hms [HF Hcv]]]].
  destruct (bounded_real_subsequence (fun i => ts (ms i)) (Rabs (ln 11)+1)
    ltac:(intro i; apply (return_segment_time_bound _ _ (Hinterval (ms i)))))
    as [rs [t [Hrs Htime]]].
  set (qs := fun i => ms (rs i)).
  assert (Hqs : indices_tend_to_infinity qs) by exact (cofinal_composition ms rs Hms Hrs).
  destruct (converging_periodic_segments_limit_family
    (fun i => ns (qs i)) (fun i => js (qs i)) (fun i => X (qs i)) Y
    (fun i => E (qs i)) F (fun i => ts (qs i)) t S
    (cofinal_composition ns qs Hns Hqs) (fun i => Hle (qs i))
    (matrix_cv_subsequence _ _ qs HX Hqs) (matrix_cv_subsequence _ _ rs Hcv Hrs) Htime
    (matrix_cv_subsequence _ _ qs HS Hqs) HA Hell HF (fun i => Hinterval (qs i)))
    as [ks [L [Hks [HL Hfamily]]]].
  exists (fun i => qs (ks i)), L; split; [apply cofinal_composition; assumption|].
  split; [exact Hfamily|]. apply cusp_height_sequence_limit; [|exact HL].
  apply (limiting_representatives_unimodular Y (phase_limit_original S) L HY HA Hell Hfamily).
Qed.

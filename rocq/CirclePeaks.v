From Stdlib Require Import Reals Psatz Lia Arith ClassicalChoice.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices FiberProducts
  EuclideanNorm MatrixLimits SymbolicCoding SymbolicCocycle DefectLimit PeriodicReturns
  EllipticConjugacy EllipticRecurrence EllipticContinuity ReturnInfiniteOrder
  TwoSidedCoding LatticeReturns PeriodicWords PeriodicOrbits PeriodicHeights
  PositionalLimits Matrix3Limits CompactMatrices RoofLimits LatticeSystole
  SystoleCurves StableForgetting.
Open Scope R_scope.

Lemma adj2_involutive : forall A, adj2 (adj2 A) = A.
Proof. intros []; apply mat2_ext; unfold adj2; simpl; ring. Qed.
Lemma adjugate_orthogonal : forall R,
  det2 R = 1 -> orthogonal2 R -> orthogonal2 (adj2 R).
Proof.
  intros R HR Ho. destruct (special_orthogonal_shape R HR Ho) as [Ha Hb].
  destruct R as [a b c d]. unfold det2 in HR; simpl in *.
  unfold orthogonal2; apply mat2_ext; unfold transpose2,mul2,adj2,id2; simpl; nra.
Qed.
Lemma elliptic_circle_adjugate : forall A R,
  adj2 (elliptic_circle A R) = elliptic_circle A (adj2 R).
Proof.
  intros A R. unfold elliptic_circle. rewrite !adj2_mul,adj2_involutive,mul2_assoc; reflexivity.
Qed.
Theorem elliptic_circle_inverse : forall A E,
  det2 A = 1 -> Rabs (trace2 A) < 2 ->
  in_elliptic_circle A E -> in_elliptic_circle A (adj2 E).
Proof.
  intros A E HA Hell [R [HRd [HRo HE]]].
  exists (adj2 R); split; [rewrite adjugate_determinant; exact HRd|].
  split; [apply adjugate_orthogonal; assumption|rewrite HE,elliptic_circle_adjugate; reflexivity].
Qed.

Theorem elliptic_circle_power_subsequence : forall A E,
  det2 A = 1 -> Rabs (trace2 A) < 2 ->
  (forall k, (0 < k)%nat -> matrix_power A k <> id2) ->
  in_elliptic_circle A E -> exists ks, indices_tend_to_infinity ks /\
    matrix_cv (fun i => matrix_power A (ks i)) E.
Proof.
  intros A E HA Hell Hinf [R [HRd [HRo HE]]].
  destruct (oriented_elliptic_basis_valid A HA Hell) as [HG HR].
  assert (Hchoose : forall i, exists k, (i <= k)%nat /\
    opnorm (sub2 (matrix_power A k) E) < (1/2)^i).
  { intro i. rewrite HE. apply conjugated_orthogonal_powers_dense_late;
      try assumption; apply pow_lt; lra. }
  destruct (@choice nat nat (fun i k => (i <= k)%nat /\
    opnorm (sub2 (matrix_power A k) E) < (1/2)^i) Hchoose) as [ks Hks].
  exists ks; split.
  - intros N; exists N; intros i Hi; specialize (Hks i); lia.
  - intros eps He.
    destruct (pow_lt_1_zero (1/2) ltac:(rewrite Rabs_right; lra) eps He) as [N HN].
    exists N; intros i Hi; specialize (HN i Hi); specialize (Hks i).
    rewrite Rabs_right in HN by (apply Rle_ge,pow_le; lra). lra.
Qed.

Lemma scalar_limit_upper_bound : forall u l B,
  Un_cv u l -> (forall i, u i <= B) -> l <= B.
Proof.
  intros u l B Hu Hb.
  pose proof (scalar_limit_nonnegative (fun i => B-u i) (B-l)
    (CV_minus _ _ _ _ (real_constant_cv B) Hu) ltac:(intro i; specialize (Hb i); lra)). lra.
Qed.

Theorem periodic_peak_bounds_circle : forall nm n X HX Hell E j t,
  in_elliptic_circle (periodic_return n) E -> 0 <= t ->
  cusp_height nm (periodic_lifted_representative n j (mul2 X E) t) <= periodic_peak nm n X HX Hell.
Proof.
  intros nm n X HX Hell E j t HE Ht.
  destruct (elliptic_circle_power_subsequence (periodic_return n) E
    (periodic_return_unimodular n) Hell (periodic_return_infinite_order n) HE)
    as [ks [Hks Hcv]].
  assert (Hmatrix : matrix3_cv
    (fun i => periodic_lifted_representative n j (mul2 X (matrix_power (periodic_return n) (ks i))) t)
    (periodic_lifted_representative n j (mul2 X E) t)).
  { apply flowing_orbit_frame_sequence_limit.
    - split; apply real_constant_cv.
    - split; apply real_constant_cv.
    - apply matrix_cv_right_product,matrix_cv_left_product; exact Hcv.
    - apply real_constant_cv. }
  assert (Hdet : det3 (periodic_lifted_representative n j (mul2 X E) t) = 1).
  { unfold periodic_lifted_representative.
    rewrite mul3_determinant,diagonal_flow_unimodular,orbit_frame_unimodular; [ring|].
    rewrite !det2_mul,HX,(elliptic_circle_unimodular _ _ (periodic_return_unimodular n) Hell HE),
      orbit_product_matches_future,factor_product_unimodular; ring. }
  apply (scalar_limit_upper_bound _ _ _ (cusp_height_sequence_limit nm _ _ Hdet Hmatrix)).
  intro i.
  change (cusp_height nm (periodic_position_frame n X (ks i) j t) <= periodic_peak nm n X HX Hell).
  rewrite <- periodic_height_position by exact HX. apply periodic_peak_upper.
  pose proof (periodic_word_time_positive n); pose proof (pos_INR (ks i)).
  pose proof (orbit_time_lower_bound j (periodic_word n)); pose proof (pos_INR j). nra.
Qed.

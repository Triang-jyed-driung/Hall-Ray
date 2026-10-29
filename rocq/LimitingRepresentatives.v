From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices
  FiberProducts EuclideanNorm MatrixLimits SymbolicCoding SymbolicCocycle
  DefectLimit PeriodicReturns EllipticConjugacy TwoSidedCoding LatticeReturns
  PeriodicWords LimitingWords LimitingFibers LimitingConvergence
  PaperTarget LatticeSystole SystoleCurves Matrix3Limits.
Open Scope R_scope.

Definition beginning_representative E j t := mul3 (diagonal_flow t)
  (orbit_frame (beginning_word j) (mul2 E (matrix_power constant_return j))).
Definition ending_representative E r t := mul3 (diagonal_flow t)
  (orbit_frame (ending_word r) (mul2 E (adj2 (defect_product r)))).
Definition bulk_representative E S t := mul3 (diagonal_flow t)
  (orbit_frame constant_word (mul2 E (mul2 (mul2 constant_basis S) (adj2 constant_basis)))).

Theorem beginning_representative_limit : forall ns j E F t r,
  indices_tend_to_infinity ns -> matrix_cv E F -> Un_cv t r ->
  matrix3_cv (fun i => mul3 (diagonal_flow (t i))
    (orbit_frame (orbit_shift j (periodic_word (ns i)))
      (mul2 (E i) (orbit_product j (periodic_word (ns i))))))
    (beginning_representative F j r).
Proof.
  intros ns j E F t r Hns HE Ht.
  destruct (periodic_beginning_code_limits ns j Hns) as [Hu Hv].
  apply flowing_orbit_frame_sequence_limit; try assumption.
  apply matrix_cv_product; [exact HE|apply periodic_beginning_fiber_limits; exact Hns].
Qed.

Theorem ending_representative_limit : forall ns j E F t r,
  indices_tend_to_infinity ns -> matrix_cv E F -> Un_cv t r ->
  matrix3_cv (fun i => mul3 (diagonal_flow (t i))
    (orbit_frame (orbit_shift (ns i-j) (periodic_word (ns i)))
      (mul2 (E i) (adj2 (orbit_product (S j)
        (orbit_shift (ns i-j) (periodic_word (ns i))))))))
    (ending_representative F j r).
Proof.
  intros ns j E F t r Hns HE Ht.
  destruct (periodic_ending_code_limits ns j Hns) as [Hu Hv].
  apply flowing_orbit_frame_sequence_limit; try assumption.
  apply matrix_cv_product; [exact HE|].
  apply matrix_cv_adjugate, periodic_ending_suffix_limits; exact Hns.
Qed.

Theorem bulk_representative_limit : forall ns js E F S t r,
  (forall i, (js i <= ns i)%nat) ->
  indices_tend_to_infinity js -> indices_tend_to_infinity (fun i => (ns i-js i)%nat) ->
  matrix_cv (fun i => matrix_power constant_rotation (js i)) S ->
  matrix_cv E F -> Un_cv t r ->
  matrix3_cv (fun i => mul3 (diagonal_flow (t i))
    (orbit_frame (orbit_shift (js i) (periodic_word (ns i)))
      (mul2 (E i) (orbit_product (js i) (periodic_word (ns i))))))
    (bulk_representative F S r).
Proof.
  intros ns js E F S t r Hle Hj Hremaining HS HE Ht.
  destruct (periodic_bulk_code_limits ns js Hle Hj Hremaining) as [Hu Hv].
  apply flowing_orbit_frame_sequence_limit; try assumption.
  apply matrix_cv_product; [exact HE|].
  apply periodic_bulk_fiber_limits; assumption.
Qed.

Lemma beginning_representative_unimodular : forall E j t,
  det2 E = 1 -> det3 (beginning_representative E j t) = 1.
Proof.
  intros E j t HE. unfold beginning_representative.
  rewrite mul3_determinant, diagonal_flow_unimodular, orbit_frame_unimodular; [ring|].
  rewrite det2_mul, HE, matrix_power_unimodular; [ring|apply cocycle_unimodular].
Qed.
Lemma ending_representative_unimodular : forall E j t,
  det2 E = 1 -> det3 (ending_representative E j t) = 1.
Proof.
  intros E j t HE. unfold ending_representative.
  rewrite mul3_determinant, diagonal_flow_unimodular, orbit_frame_unimodular; [ring|].
  rewrite det2_mul, HE, adjugate_determinant.
  unfold defect_product; rewrite factor_product_unimodular; ring.
Qed.
Lemma bulk_representative_unimodular : forall E S t,
  det2 E = 1 -> det2 S = 1 -> det3 (bulk_representative E S t) = 1.
Proof.
  intros E S t HE HS. unfold bulk_representative.
  rewrite mul3_determinant, diagonal_flow_unimodular, orbit_frame_unimodular; [ring|].
  rewrite !det2_mul, adjugate_determinant, HE, HS, constant_basis_unimodular; ring.
Qed.

Theorem beginning_height_limit : forall nm ns j E F t r,
  indices_tend_to_infinity ns -> matrix_cv E F -> Un_cv t r -> det2 F = 1 ->
  Un_cv (fun i => cusp_height nm (mul3 (diagonal_flow (t i))
    (orbit_frame (orbit_shift j (periodic_word (ns i)))
      (mul2 (E i) (orbit_product j (periodic_word (ns i)))))))
    (cusp_height nm (beginning_representative F j r)).
Proof.
  intros nm ns j E F t r Hns HE Ht HF. apply cusp_height_sequence_limit.
  - apply beginning_representative_unimodular; exact HF.
  - apply beginning_representative_limit; assumption.
Qed.

Theorem ending_height_limit : forall nm ns j E F t r,
  indices_tend_to_infinity ns -> matrix_cv E F -> Un_cv t r -> det2 F = 1 ->
  Un_cv (fun i => cusp_height nm (mul3 (diagonal_flow (t i))
    (orbit_frame (orbit_shift (ns i-j) (periodic_word (ns i)))
      (mul2 (E i) (adj2 (orbit_product (S j)
        (orbit_shift (ns i-j) (periodic_word (ns i)))))))))
    (cusp_height nm (ending_representative F j r)).
Proof.
  intros nm ns j E F t r Hns HE Ht HF. apply cusp_height_sequence_limit.
  - apply ending_representative_unimodular; exact HF.
  - apply ending_representative_limit; assumption.
Qed.

Theorem bulk_height_limit : forall nm ns js E F S t r,
  (forall i, (js i <= ns i)%nat) ->
  indices_tend_to_infinity js -> indices_tend_to_infinity (fun i => (ns i-js i)%nat) ->
  matrix_cv (fun i => matrix_power constant_rotation (js i)) S ->
  matrix_cv E F -> Un_cv t r -> det2 F = 1 -> det2 S = 1 ->
  Un_cv (fun i => cusp_height nm (mul3 (diagonal_flow (t i))
    (orbit_frame (orbit_shift (js i) (periodic_word (ns i)))
      (mul2 (E i) (orbit_product (js i) (periodic_word (ns i)))))))
    (cusp_height nm (bulk_representative F S r)).
Proof.
  intros nm ns js E F S t r Hle Hj Hremaining HS HE Ht HF HSdet.
  apply cusp_height_sequence_limit.
  - apply bulk_representative_unimodular; assumption.
  - apply bulk_representative_limit; assumption.
Qed.

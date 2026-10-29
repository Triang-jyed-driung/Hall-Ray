module

public import HallRay.BulkSkeleton

@[expose] public section
noncomputable section
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

theorem ellipticCircle_mul {A : Mat2} (hdet : A.det = 1) (hell : Elliptic A)
    (θ φ : Real.Angle) : ellipticCircle A θ * ellipticCircle A φ = ellipticCircle A (θ + φ) := by
  have hG : (ellipticConjugator A)⁻¹ * ellipticConjugator A = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (ellipticConjugator_det hdet hell))
  have hcancel (X : Mat2) : (ellipticConjugator A)⁻¹ * (ellipticConjugator A * X) = X := by
    rw [← Matrix.mul_assoc, hG, one_mul]
  simp only [ellipticCircle, angleRotation_add, Matrix.mul_assoc, hcancel]

/-- Arbitrarily long bulk flights return to the same compact limiting model. -/
theorem bulk_flow_representative (v : TraceParameter) (θ ξ : Real.Angle) {t : ℝ} (ht : 0 ≤ t) :
    ∃ p : LimitingParameter,
      frameLattice (flow t * codedChart constantWord
        (ellipticCircle (ellipticTracePath v) θ * ellipticCircle constantMatrix ξ)) =
      frameLattice (limitingFrame v p) := by
  obtain ⟨m, r, heq, hr0, hr1⟩ := flight_decomposition constantWord ht
  have hshift : shift (m : ℤ) constantWord = constantWord := rfl
  rw [hshift] at hr1
  have hroof : 0 < roof constantWord := lt_trans (by norm_num) (roof_gt_one _)
  let a : FlightParameter := ⟨r / roof constantWord,
    ⟨div_nonneg hr0 hroof.le, (div_le_one hroof).mpr hr1⟩⟩
  let ξ' := ξ + m • (constantAngle : Real.Angle)
  let s : SkeletonPoint := ⟨(constantWord, ellipticCircle constantMatrix ξ'), bulk_mem_limitingSkeleton ξ'⟩
  let p : LimitingParameter := (s, (θ, a))
  refine ⟨p, ?_⟩
  rw [heq]
  have hh := symbolic_lattice_factor constantWord
    (ellipticCircle (ellipticTracePath v) θ * ellipticCircle constantMatrix ξ) m r
  rw [hshift, constant_cocycle] at hh
  have hprod : ellipticCircle constantMatrix ξ * constantMatrix ^ m = ellipticCircle constantMatrix ξ' := by
    rw [← ellipticCircle_phase (fiberMap_det constantWord) constantMatrix_elliptic,
      ellipticCircle_mul (fiberMap_det constantWord) constantMatrix_elliptic]
  rw [Matrix.mul_assoc, hprod] at hh
  simpa only [limitingFrame, p, s, a, div_mul_cancel₀ r hroof.ne'] using hh

/-- The limiting maximum bounds the full forward bulk trajectory, not just one roof interval. -/
theorem bulk_flow_height_le_depth (N : PlaneNorm) (E : FiberParameter) (v : TraceParameter)
    (θ ξ : Real.Angle) {t : ℝ} (ht : 0 ≤ t) :
    frameHeight N (blockFiber E.val * (flow t * codedChart constantWord
      (ellipticCircle (ellipticTracePath v) θ * ellipticCircle constantMatrix ξ))) ≤
      limitingDepth N (E, v) := by
  obtain ⟨p, hp⟩ := bulk_flow_representative v θ ξ ht
  have hC : (ellipticCircle (ellipticTracePath v) θ * ellipticCircle constantMatrix ξ).det = 1 := by
    rw [Matrix.det_mul, ellipticCircle_det (ellipticTracePath_det v)
      (ellipticTracePath_elliptic v.property), ellipticCircle_det (fiberMap_det constantWord)
      constantMatrix_elliptic, one_mul]
  have hl : frameLattice (blockFiber E.val * (flow t * codedChart constantWord
      (ellipticCircle (ellipticTracePath v) θ * ellipticCircle constantMatrix ξ))) =
      frameLattice (blockFiber E.val * limitingFrame v p) := by
    rw [frameLattice_mul_image (blockFiber E.val)
      (flow t * codedChart constantWord (ellipticCircle (ellipticTracePath v) θ * ellipticCircle constantMatrix ξ)),
      frameLattice_mul_image (blockFiber E.val) (limitingFrame v p), hp]
  rw [frameHeight_of_lattice_eq N _ _ ?_ ?_ hl]
  · exact le_sSup ⟨p, rfl⟩
  · rw [Matrix.det_mul, blockFiber_det, E.property, Matrix.det_mul, flow_det,
      codedChart_det _ hC, one_mul, one_mul]
    norm_num
  · rw [Matrix.det_mul, blockFiber_det, E.property, limitingFrame_det, one_mul]
    norm_num

end HallRay

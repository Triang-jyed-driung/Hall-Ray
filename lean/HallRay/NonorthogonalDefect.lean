module

public import HallRay.DefectNormalization

@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace HallRay

theorem commutator_sub_right (A B C : Mat2) :
    commutator A B - commutator A C = commutator A (B - C) := by
  unfold commutator
  noncomm_ring

theorem commutator_norm_le (A B : Mat2) : ‖commutator A B‖ ≤ 2 * ‖A‖ * ‖B‖ := by
  calc
    _ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

/-- The limiting defect really fails to commute with the constant return. -/
theorem defectMatrix_noncommuting : commutator constantMatrix defectMatrix ≠ 0 := by
  intro hz
  have he : commutator constantMatrix (defectApprox 2) =
      commutator constantMatrix (defectApprox 2 - defectMatrix) := by
    rw [← commutator_sub_right, hz, sub_zero]
  have hnorm : ‖commutator constantMatrix (defectApprox 2)‖ ≤ (11 / 400000 : ℝ) := by
    rw [he]
    calc
      _ ≤ 2 * ‖constantMatrix‖ * ‖defectApprox 2 - defectMatrix‖ := commutator_norm_le _ _
      _ ≤ 2 * (11 / 10 : ℝ) * (2 * (1 / 400 : ℝ) ^ 2) := by
        gcongr
        · exact fiberMap_norm_bound constantWord
        · exact defectApprox_error 2
      _ = _ := by norm_num
  have hentry := entry_le_operator_norm (commutator constantMatrix (defectApprox 2)) 1 0
  have hpos := defectApprox_commutator_entry_gt
  have hself : commutator constantMatrix (defectApprox 2) 1 0 ≤
      |commutator constantMatrix (defectApprox 2) 1 0| := le_abs_self _
  linarith

/-- The algebraic form of a rotation, before imposing determinant one. -/
def RotationForm (B : Mat2) : Prop := B 0 0 = B 1 1 ∧ B 0 1 = -B 1 0

theorem rotationForm_commutes {B : Mat2} (hB : RotationForm B) (θ : ℝ) :
    rotation θ * B = B * rotation θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_succ, hB.1, hB.2] <;> ring

abbrev constantAngle : ℝ := ellipticAngle constantMatrix
abbrev constantConjugator : Mat2 := ellipticConjugator constantMatrix

theorem constantMatrix_elliptic : Elliptic constantMatrix := by
  simpa [constantMatrix, fiberMap, constantWord_shift, constantWord] using constantCode_elliptic

theorem constantConjugator_det_ne_zero : constantConjugator.det ≠ 0 :=
  ellipticConjugator_det (fiberMap_det _) constantMatrix_elliptic

theorem constantMatrix_conjugate :
    constantMatrix = constantConjugator * rotation constantAngle * constantConjugator⁻¹ :=
  elliptic_conjugate_rotation (fiberMap_det _) constantMatrix_elliptic

/-- The defect in the basis in which the constant return is a rotation. -/
def rotationDefect : Mat2 := constantConjugator⁻¹ * defectMatrix * constantConjugator

theorem rotationDefect_det : rotationDefect.det = 1 := by
  have hG := constantConjugator_det_ne_zero
  simp [rotationDefect, Matrix.det_mul, Matrix.det_nonsing_inv, defectMatrix_det,
    Ring.inverse_eq_inv, inv_mul_cancel₀ hG]

/-- Lemma `lem:nonorthogonal-defect`, expressed as non-membership in rotation form. -/
theorem rotationDefect_not_rotationForm : ¬RotationForm rotationDefect := by
  intro hB
  have hGl : constantConjugator⁻¹ * constantConjugator = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr constantConjugator_det_ne_zero)
  have hGr : constantConjugator * constantConjugator⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr constantConjugator_det_ne_zero)
  have hD : defectMatrix = constantConjugator * rotationDefect * constantConjugator⁻¹ := by
    unfold rotationDefect
    simp only [← Matrix.mul_assoc, hGr, one_mul]
    rw [Matrix.mul_assoc, hGr, mul_one]
  have hcancel (X : Mat2) : constantConjugator⁻¹ * (constantConjugator * X) = X := by
    rw [← Matrix.mul_assoc, hGl, one_mul]
  have hR := rotationForm_commutes hB constantAngle
  apply defectMatrix_noncommuting
  unfold commutator
  rw [constantMatrix_conjugate, hD]
  apply sub_eq_zero.mpr
  calc
    _ = constantConjugator * (rotation constantAngle * rotationDefect) * constantConjugator⁻¹ := by
      simp only [Matrix.mul_assoc, hcancel]
    _ = constantConjugator * (rotationDefect * rotation constantAngle) * constantConjugator⁻¹ := by rw [hR]
    _ = _ := by simp only [Matrix.mul_assoc, hcancel]

/-- The strict trace-amplitude inequality that produces elliptic and parabolic phases. -/
theorem trace_amplitude_gt_four {B : Mat2} (hdet : B.det = 1) (hB : ¬RotationForm B) :
    4 < (B 0 0 + B 1 1) ^ 2 + (B 0 1 - B 1 0) ^ 2 := by
  rw [Matrix.det_fin_two] at hdet
  by_contra! h
  have h₁ : (B 0 0 - B 1 1) ^ 2 = 0 := by nlinarith [sq_nonneg (B 0 1 + B 1 0)]
  have h₂ : (B 0 1 + B 1 0) ^ 2 = 0 := by nlinarith [sq_nonneg (B 0 0 - B 1 1)]
  apply hB
  constructor
  · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h₁)
  · have := sq_eq_zero_iff.mp h₂
    linarith

theorem rotationDefect_trace_amplitude :
    4 < (rotationDefect 0 0 + rotationDefect 1 1) ^ 2 +
      (rotationDefect 0 1 - rotationDefect 1 0) ^ 2 :=
  trace_amplitude_gt_four rotationDefect_det rotationDefect_not_rotationForm

end HallRay

module

public import HallRay.NonorthogonalDefect
public import Mathlib.LinearAlgebra.Matrix.ZPow

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

def constantPowerBound : ℝ := ‖constantConjugator‖ * ‖constantConjugator⁻¹‖ + 1

theorem constantPowerBound_ge_one : 1 ≤ constantPowerBound := by
  have := mul_nonneg (norm_nonneg constantConjugator) (norm_nonneg (constantConjugator⁻¹))
  dsimp [constantPowerBound]
  linarith

theorem constant_power_norm (j : ℕ) : ‖constantMatrix ^ j‖ ≤ constantPowerBound := by
  have h := elliptic_power_norm_le (fiberMap_det constantWord) constantMatrix_elliptic j
  change ‖constantMatrix ^ j‖ ≤ ‖constantConjugator‖ * ‖constantConjugator⁻¹‖ at h
  dsimp [constantPowerBound]
  linarith

theorem constant_cocycle (j : ℕ) : cocycle fiberMap constantWord j = constantMatrix ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [cocycle_succ, ih, pow_succ]
    rfl

theorem absolute_error_le (P Q : Mat2) (hP : P.det = 1) :
    ‖Q - P‖ ≤ ‖P‖ * ‖P⁻¹ * Q - 1‖ := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (by rw [hP]; exact isUnit_one)
  have he : Q - P = P * (P⁻¹ * Q - 1) := by
    rw [mul_sub, mul_one, ← Matrix.mul_assoc, hPP, one_mul]
  rw [he]
  exact norm_mul_le _ _

/-- Uniform approximation of partial products by the constant elliptic powers. -/
theorem periodic_partial_error (n j : ℕ) (hj : j ≤ n) :
    ‖cocycle fiberMap (periodicWord n) j - constantMatrix ^ j‖ ≤
      constantPowerBound * ((1 / 10 : ℝ) * (1 / 900 : ℝ) ^ (n - j)) := by
  have hagree : ∀ i : ℕ, i < j + (n - j) → constantWord (i : ℤ) = periodicWord n (i : ℤ) := by
    intro i hi
    rw [periodicWord_a (by omega)]
    rfl
  have h := fiber_product_error_sharp j (n - j) hagree
  rw [constant_cocycle] at h
  calc
    _ ≤ ‖constantMatrix ^ j‖ * ‖(constantMatrix ^ j)⁻¹ * cocycle fiberMap (periodicWord n) j - 1‖ :=
      absolute_error_le _ _ (by rw [Matrix.det_pow, fiberMap_det, one_pow])
    _ ≤ _ := mul_le_mul (constant_power_norm j) h (norm_nonneg _) (by
      have := constantPowerBound_ge_one
      linarith)

theorem periodic_partial_norm (n j : ℕ) (hj : j ≤ n) :
    ‖cocycle fiberMap (periodicWord n) j‖ ≤ 2 * constantPowerBound := by
  have he := periodic_partial_error n j hj
  have hp : (1 / 900 : ℝ) ^ (n - j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hK := constantPowerBound_ge_one
  have htri : ‖cocycle fiberMap (periodicWord n) j‖ ≤
      ‖cocycle fiberMap (periodicWord n) j - constantMatrix ^ j‖ + ‖constantMatrix ^ j‖ := by
    simpa using norm_sub_le (cocycle fiberMap (periodicWord n) j - constantMatrix ^ j) (-constantMatrix ^ j)
  have hm := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ constantPowerBound / 10)
  have hc := constant_power_norm j
  nlinarith

theorem periodMatrix_norm (n : ℕ) : ‖periodMatrix n‖ ≤ (11 / 5 : ℝ) * constantPowerBound := by
  unfold periodMatrix
  rw [cocycle_succ]
  exact (norm_mul_le _ _).trans
    ((mul_le_mul (periodic_partial_norm n n le_rfl) (fiberMap_norm_bound _) (norm_nonneg _) (by
      have := constantPowerBound_ge_one
      linarith)).trans_eq (by ring))

theorem periodMatrix_inverse_norm (n : ℕ) : ‖(periodMatrix n)⁻¹‖ ≤ (11 / 5 : ℝ) * constantPowerBound := by
  rw [determinant_one_inverse_norm (periodMatrix_det n)]
  exact periodMatrix_norm n

theorem periodic_defect_error (n : ℕ) :
    ‖cocycle fiberMap (shift (-(n : ℤ)) defectWord) (n + 1) - periodMatrix n‖ ≤
      (11 / 50 : ℝ) * constantPowerBound * (1 / 900 : ℝ) ^ n := by
  have hagree : ∀ i : ℕ, i < n + 1 + n →
      periodicWord n (i : ℤ) = (shift (-(n : ℤ)) defectWord) (i : ℤ) := by
    intro i hi
    exact periodic_defect_agreement n i (by omega)
  have h := fiber_product_error_sharp (n + 1) n hagree
  change ‖(periodMatrix n)⁻¹ * cocycle fiberMap (shift (-(n : ℤ)) defectWord) (n + 1) - 1‖ ≤ _ at h
  calc
    _ ≤ ‖periodMatrix n‖ * ‖(periodMatrix n)⁻¹ *
        cocycle fiberMap (shift (-(n : ℤ)) defectWord) (n + 1) - 1‖ :=
      absolute_error_le _ _ (periodMatrix_det n)
    _ ≤ ((11 / 5 : ℝ) * constantPowerBound) * ((1 / 10 : ℝ) * (1 / 900 : ℝ) ^ n) := by
      exact mul_le_mul (periodMatrix_norm n) h (norm_nonneg _) (by
        have := constantPowerBound_ge_one
        linarith)
    _ = _ := by ring

theorem defectApprox_unscale (n : ℕ) :
    constantMatrix ^ n * defectApprox n = cocycle fiberMap (shift (-(n : ℤ)) defectWord) (n + 1) := by
  have hP : (constantMatrix ^ n).det = 1 := by rw [Matrix.det_pow, fiberMap_det, one_pow]
  have hPP : constantMatrix ^ n * (constantMatrix ^ n)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hP]; exact isUnit_one)
  rw [defectApprox, Matrix.inv_pow', ← Matrix.mul_assoc, hPP, one_mul]

/-- The period asymptotic, with an unspecified fixed constant rather than the
paper's numerical normalization of the conjugator. -/
theorem period_asymptotic_error (n : ℕ) :
    ‖periodMatrix n - constantMatrix ^ n * defectMatrix‖ ≤
      3 * constantPowerBound * (1 / 400 : ℝ) ^ n := by
  let Q := cocycle fiberMap (shift (-(n : ℤ)) defectWord) (n + 1)
  have h₁ : ‖periodMatrix n - Q‖ ≤ (11 / 50 : ℝ) * constantPowerBound * (1 / 900 : ℝ) ^ n := by
    rw [norm_sub_rev]
    exact periodic_defect_error n
  have h₂ : ‖Q - constantMatrix ^ n * defectMatrix‖ ≤
      constantPowerBound * (2 * (1 / 400 : ℝ) ^ n) := by
    have he : Q - constantMatrix ^ n * defectMatrix = constantMatrix ^ n * (defectApprox n - defectMatrix) := by
      rw [mul_sub, defectApprox_unscale]
    rw [he]
    exact (norm_mul_le _ _).trans
      (mul_le_mul (constant_power_norm n) (defectApprox_error n) (norm_nonneg _) (by
        have := constantPowerBound_ge_one
        linarith))
  have hdecomp : periodMatrix n - constantMatrix ^ n * defectMatrix =
      (periodMatrix n - Q) + (Q - constantMatrix ^ n * defectMatrix) := by abel
  rw [hdecomp]
  have hp : (1 / 900 : ℝ) ^ n ≤ (1 / 400 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hK := constantPowerBound_ge_one
  have hm := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ (11 / 50 : ℝ) * constantPowerBound)
  have hn : 0 ≤ constantPowerBound * (1 / 400 : ℝ) ^ n := by positivity
  exact (norm_add_le _ _).trans (by nlinarith)

theorem period_asymptotic_tendsto :
    Tendsto (fun n : ℕ => periodMatrix n - constantMatrix ^ n * defectMatrix) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) period_asymptotic_error
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 400)
    (by norm_num : (1 / 400 : ℝ) < 1)).const_mul (3 * constantPowerBound)
  simpa only [mul_zero] using hlim

end HallRay

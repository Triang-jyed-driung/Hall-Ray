module

public import HallRay.Elliptic
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

abbrev constantMatrix : Mat2 := fiberMap constantWord

def defectApprox (r : ℕ) : Mat2 :=
  (constantMatrix⁻¹) ^ r * cocycle fiberMap (shift (-(r : ℤ)) defectWord) (r + 1)

theorem fiberMap_norm_bound (z : Word) : ‖fiberMap z‖ ≤ 11 / 10 := by
  have h := fiber_norm_le (z 0) (futureCode_mem (shift 1 z))
  change ‖fiberMap z‖ ≤ 26 / 25 at h
  linarith

theorem fiberMap_inverse_norm_bound (z : Word) : ‖(fiberMap z)⁻¹‖ ≤ 11 / 10 := by
  have h := fiber_inverse_norm_le (z 0) (futureCode_mem (shift 1 z))
  change ‖(fiberMap z)⁻¹‖ ≤ 26 / 25 at h
  linarith

theorem fiberProduct_norm_bound (z : Word) (n : ℕ) :
    ‖cocycle fiberMap z n‖ ≤ (11 / 10 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cocycle_succ, pow_succ]
    exact (norm_mul_le _ _).trans
      (mul_le_mul ih (fiberMap_norm_bound _) (norm_nonneg _) (by positivity))

theorem defect_head_difference (r : ℕ) :
    ‖fiberMap (shift (-((r + 1 : ℕ) : ℤ)) defectWord) - constantMatrix‖ ≤
      (2 / 25 : ℝ) * (1 / 900 : ℝ) ^ r := by
  have hagree : ∀ i : ℕ, i < 0 + 1 + r →
      constantWord (i : ℤ) = (shift (-((r + 1 : ℕ) : ℤ)) defectWord) (i : ℤ) := by
    intro i hi
    change Symbol.a = (if (i : ℤ) + -((r + 1 : ℕ) : ℤ) = 0 then Symbol.b else Symbol.a)
    rw [ite_eq_right (by omega)]
  have h := fiber_last_difference 0 r hagree
  simpa only [Nat.cast_zero, shift_zero] using h

theorem defect_shift (r : ℕ) :
    shift 1 (shift (-((r + 1 : ℕ) : ℤ)) defectWord) = shift (-(r : ℤ)) defectWord := by
  rw [shift_add]
  congr 1
  omega

theorem defectApprox_step (r : ℕ) :
    defectApprox (r + 1) - defectApprox r =
      (constantMatrix⁻¹) ^ (r + 1) *
        (fiberMap (shift (-((r + 1 : ℕ) : ℤ)) defectWord) - constantMatrix) *
          cocycle fiberMap (shift (-(r : ℤ)) defectWord) (r + 1) := by
  have hAA : constantMatrix⁻¹ * constantMatrix = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [fiberMap_det]; exact isUnit_one)
  unfold defectApprox
  rw [cocycle_head, defect_shift]
  simp only [pow_succ, mul_sub, sub_mul, Matrix.mul_assoc, hAA, one_mul]

theorem defectApprox_step_norm (r : ℕ) :
    ‖defectApprox (r + 1) - defectApprox r‖ ≤ (1 / 400 : ℝ) ^ r := by
  have hpow : ‖(constantMatrix⁻¹) ^ (r + 1)‖ ≤ (11 / 10 : ℝ) ^ (r + 1) :=
    (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (fiberMap_inverse_norm_bound _) _)
  rw [defectApprox_step]
  calc
    _ ≤ ((11 / 10 : ℝ) ^ (r + 1) * ((2 / 25 : ℝ) * (1 / 900 : ℝ) ^ r)) *
        (11 / 10 : ℝ) ^ (r + 1) := by
      calc
        _ ≤ (‖(constantMatrix⁻¹) ^ (r + 1)‖ *
            ‖fiberMap (shift (-((r + 1 : ℕ) : ℤ)) defectWord) - constantMatrix‖) *
            ‖cocycle fiberMap (shift (-(r : ℤ)) defectWord) (r + 1)‖ := by
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ _ := by
          gcongr
          all_goals first | exact defect_head_difference r | exact fiberProduct_norm_bound _ _
    _ = (121 / 1250 : ℝ) * (121 / 90000 : ℝ) ^ r := by
      rw [show (121 / 90000 : ℝ) = (11 / 10) * (11 / 10) * (1 / 900) by norm_num,
        mul_pow, mul_pow, pow_succ]
      ring
    _ ≤ (1 / 400 : ℝ) ^ r := by
      have hp : (121 / 90000 : ℝ) ^ r ≤ (1 / 400 : ℝ) ^ r :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) r
      have hn : 0 ≤ (121 / 90000 : ℝ) ^ r := by positivity
      linarith

theorem defectApprox_cauchy : CauchySeq defectApprox := by
  apply cauchySeq_of_le_geometric (1 / 400) 1 (by norm_num)
  intro r
  rw [dist_eq_norm, norm_sub_rev, one_mul]
  exact defectApprox_step_norm r

/-- The defect limit before conjugating by the constant-return rotation basis. -/
def defectMatrix : Mat2 := Classical.choose (cauchySeq_tendsto_of_complete defectApprox_cauchy)

theorem defectMatrix_tendsto : Tendsto defectApprox atTop (𝓝 defectMatrix) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete defectApprox_cauchy)

theorem defectApprox_det (r : ℕ) : (defectApprox r).det = 1 := by
  simp [defectApprox, Matrix.det_mul, Matrix.det_pow, Matrix.det_nonsing_inv,
    fiberMap_det, fiberProduct_det]

theorem defectMatrix_det : defectMatrix.det = 1 := by
  have hcont : Continuous (fun A : Mat2 => A.det) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  have ht := (hcont.tendsto defectMatrix).comp defectMatrix_tendsto
  have ht' : Tendsto (fun r : ℕ => (defectApprox r).det) atTop (𝓝 1) := by
    simpa only [defectApprox_det] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  exact tendsto_nhds_unique ht ht'

theorem defectApprox_error (r : ℕ) : ‖defectApprox r - defectMatrix‖ ≤ 2 * (1 / 400 : ℝ) ^ r := by
  have h := dist_le_of_le_geometric_of_tendsto (1 / 400) 1 (by norm_num)
    (fun n => by rw [dist_eq_norm, norm_sub_rev, one_mul]; exact defectApprox_step_norm n)
    defectMatrix_tendsto r
  rw [dist_eq_norm, one_mul] at h
  have hn : 0 ≤ (1 / 400 : ℝ) ^ r := by positivity
  norm_num at h
  linarith

end HallRay

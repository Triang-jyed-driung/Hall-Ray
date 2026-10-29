module

public import HallRay.Matrix2
public import HallRay.ScalarEstimates

@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- The explicit fiber Lipschitz estimate of Lemma `lem:LipMsu`. -/
theorem fiber_lipschitz (s : Symbol) {u v : Point} (hu : U u) (hv : U v) :
    ‖fiber s u - fiber s v‖ ≤ (1 / 5 : ℝ) * supDist u v := by
  have hdec : fiber s u - fiber s v =
      (Real.sqrt (d s u))⁻¹ • (fiberNumerator s u - fiberNumerator s v) +
      ((Real.sqrt (d s u))⁻¹ - (Real.sqrt (d s v))⁻¹) • fiberNumerator s v := by
    simp only [fiber, smul_sub, sub_smul]
    abel
  have hr : 0 ≤ supDist u v := le_trans (abs_nonneg _) (le_max_left _ _)
  have hs : 0 ≤ (Real.sqrt (d s u))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have htwo : Real.sqrt 2 ≤ 71 / 50 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have := Real.sqrt_nonneg 2
    nlinarith
  rw [hdec]
  calc
    _ ≤ ‖(Real.sqrt (d s u))⁻¹ • (fiberNumerator s u - fiberNumerator s v)‖ +
        ‖((Real.sqrt (d s u))⁻¹ - (Real.sqrt (d s v))⁻¹) • fiberNumerator s v‖ := norm_add_le _ _
    _ = (Real.sqrt (d s u))⁻¹ * ‖fiberNumerator s u - fiberNumerator s v‖ +
        |(Real.sqrt (d s u))⁻¹ - (Real.sqrt (d s v))⁻¹| * ‖fiberNumerator s v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs]
    _ ≤ (1 / 10 : ℝ) * (Real.sqrt 2 * supDist u v) +
        ((11 / 2000 : ℝ) * supDist u v) * (21 / 2 : ℝ) := by
      gcongr
      · exact inverse_sqrt_d_le s hu
      · exact numerator_difference_norm s u v
      · exact inverse_sqrt_d_difference s hu hv
      · exact numerator_norm_le s hv
    _ ≤ (1 / 5 : ℝ) * supDist u v := by nlinarith [mul_le_mul_of_nonneg_right htwo hr]

theorem fiber_zero_norm (s : Symbol) : ‖fiber s (0, 0)‖ = 1 := by
  have hN : ‖fiberNumerator s (0, 0)‖ = Real.sqrt 101 := by
    have hsq := numerator_zero_norm_sq s
    have hs : Real.sqrt 101 ^ 2 = 101 := Real.sq_sqrt (by norm_num)
    have := norm_nonneg (fiberNumerator s (0, 0))
    have := Real.sqrt_nonneg 101
    nlinarith
  have hs : 0 < Real.sqrt 101 := Real.sqrt_pos.mpr (by norm_num)
  rw [fiber, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), hN]
  simp [d]

theorem fiber_norm_le (s : Symbol) {u : Point} (hu : U u) : ‖fiber s u‖ ≤ 26 / 25 := by
  have hdiff := fiber_lipschitz s hu (show U (0, 0) by norm_num [U])
  have hdist : supDist u (0, 0) ≤ 1 / 5 := by
    dsimp [supDist]
    simp only [sub_zero]
    exact max_le hu.1 (by linarith [hu.2])
  have hnorm := norm_sub_le (fiber s u - fiber s (0, 0)) (-fiber s (0, 0))
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, fiber_zero_norm] at hnorm
  linarith

theorem fiber_inverse_norm_le (s : Symbol) {u : Point} (hu : U u) : ‖(fiber s u)⁻¹‖ ≤ 26 / 25 := by
  rw [determinant_one_inverse_norm (fiber_det s hu)]
  exact fiber_norm_le s hu

end HallRay

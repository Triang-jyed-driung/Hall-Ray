module

public import HallRay.MatrixEstimates

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace HallRay

theorem entry_le_operator_norm (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) : |A i j| ≤ ‖A‖ := by
  let v : EuclideanSpace ℝ (Fin 2) := PiLp.single 2 j 1
  have hc := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A v) i
  have hop := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A).le_opNorm v
  have hv : ‖v‖ = 1 := by simp [v]
  have he : (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A v).ofLp i = A i j := by
    simp only [v, PiLp.single, Matrix.toEuclideanCLM_toLp, WithLp.ofLp_toLp,
      Matrix.mulVec_single_one, Matrix.col_apply]
  rw [he, Real.norm_eq_abs] at hc
  rw [hv, mul_one, Matrix.l2_opNorm_toEuclideanCLM] at hop
  exact hc.trans hop

end HallRay

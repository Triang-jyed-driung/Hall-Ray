module

public import HallRay.ConjugatedContraction

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

/-- Euclidean coordinates for the unstable vector in the first chart column. -/
def unstableVector (z : Word) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![(futureCode z).1, (futureCode z).2]

def planeCoordinates (x : EuclideanSpace ℝ (Fin 2)) : Point := (x 0, x 1)

theorem planeCoordinates_norm_le (N : PlaneNorm) (x : EuclideanSpace ℝ (Fin 2)) :
    N.value (planeCoordinates x) ≤ N.bound * ‖x‖ := by
  apply (N.upper_bound _).trans
  apply mul_le_mul_of_nonneg_left _ N.bound_nonneg
  rw [planeCoordinates, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (PiLp.norm_apply_le x 0) (PiLp.norm_apply_le x 1)

/-- Exact first-column formula; the stable chart coordinate affects only the scalar. -/
theorem chart_first_column (z : Word) (E F : Mat2) (t : ℝ) :
    (blockFiber E * (flow t * codedChart z F)).mulVec ![1, 0, 0] =
      ![chartScale (futureCode z) (pastCode z) * Real.exp (-2 * t),
        -chartScale (futureCode z) (pastCode z) * Real.exp t *
          (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) E
            (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z))) 0,
        -chartScale (futureCode z) (pastCode z) * Real.exp t *
          (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) E
            (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z))) 1] := by
  ext i
  fin_cases i <;>
    simp [codedChart, chart, blockFiber, flow, rawChart, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Fin.sum_univ_succ, unstableVector] <;> ring

theorem chart_first_vector_norm (N : PlaneNorm) (z : Word) (E F : Mat2) (t : ℝ) :
    ‖N.frameVector (blockFiber E * (flow t * codedChart z F)) (1, (0, 0))‖ =
      max (chartScale (futureCode z) (pastCode z) * Real.exp (-2 * t))
        (chartScale (futureCode z) (pastCode z) * Real.exp t *
          N.value (planeCoordinates (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) E
            (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z))))) := by
  rw [frameVector_norm]
  norm_num only [Int.cast_one, Int.cast_zero]
  rw [chart_first_column]
  change max |chartScale (futureCode z) (pastCode z) * Real.exp (-2 * t)|
    (N.value (-chartScale (futureCode z) (pastCode z) * Real.exp t *
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) E (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z))) 0,
      -chartScale (futureCode z) (pastCode z) * Real.exp t *
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) E (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z))) 1)) = _
  have hp := chartScale_pos (futureCode z) (pastCode z)
  rw [abs_of_pos (mul_pos hp (Real.exp_pos _))]
  have he : (-chartScale (futureCode z) (pastCode z) * Real.exp t *
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) E (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z))) 0,
      -chartScale (futureCode z) (pastCode z) * Real.exp t *
        (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) E (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z))) 1) =
      (-chartScale (futureCode z) (pastCode z) * Real.exp t) •
        planeCoordinates (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) E (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z))) := by rfl
  rw [he, N.smul_eq, abs_mul, abs_neg, abs_of_pos hp, abs_of_pos (Real.exp_pos _)]

theorem chart_first_vector_bound (N : PlaneNorm) (z : Word) (E F : Mat2) (t : ℝ) :
    ‖N.frameVector (blockFiber E * (flow t * codedChart z F)) (1, (0, 0))‖ ≤
      max (chartScale (futureCode z) (pastCode z) * Real.exp (-2 * t))
        ((chartScale (futureCode z) (pastCode z) * Real.exp t * N.bound * ‖E‖) *
          ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z)‖) := by
  rw [chart_first_vector_norm]
  apply max_le_max le_rfl
  have hop := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) E).le_opNorm
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z))
  rw [Matrix.l2_opNorm_toEuclideanCLM] at hop
  have hN := planeCoordinates_norm_le N
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) E (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector z)))
  have htail := hN.trans (mul_le_mul_of_nonneg_left hop N.bound_nonneg)
  have hm := mul_le_mul_of_nonneg_left htail (mul_nonneg
    (chartScale_pos (futureCode z) (pastCode z)).le (Real.exp_pos t).le)
  simpa only [mul_assoc] using hm

end HallRay

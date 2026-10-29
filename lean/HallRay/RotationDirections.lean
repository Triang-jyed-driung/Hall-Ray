module

public import HallRay.ContractingDirections
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section
noncomputable section
namespace HallRay

/-- The real rotation matrix agrees with multiplication by a unit complex number. -/
theorem rotation_complex_coordinates (θ : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    Complex.orthonormalBasisOneI.repr.symm
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (rotation θ) x) =
    (Real.cos θ + Real.sin θ * Complex.I) * Complex.orthonormalBasisOneI.repr.symm x := by
  rw [Complex.orthonormalBasisOneI_repr_symm_apply, Complex.orthonormalBasisOneI_repr_symm_apply]
  change ((Matrix.mulVec (rotation θ) x.ofLp) 0 : ℂ) +
    (Matrix.mulVec (rotation θ) x.ofLp) 1 * Complex.I = _
  apply Complex.ext <;> simp [rotation, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

/-- Rotations act transitively on every Euclidean circle. -/
theorem exists_rotation_sends {x y : EuclideanSpace ℝ (Fin 2)} (hxy : ‖x‖ = ‖y‖) :
    ∃ θ : ℝ, Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (rotation θ) x = y := by
  by_cases hx : x = 0
  · have hy : y = 0 := norm_eq_zero.mp (by simpa only [hx, norm_zero] using hxy.symm)
    exact ⟨0, by simp [hx, hy]⟩
  · let e := Complex.orthonormalBasisOneI.repr.symm
    let c := e y / e x
    have hcx : e x ≠ 0 := by
      intro h
      exact hx (e.injective (by simpa using h))
    have hc : ‖c‖ = 1 := by
      dsimp only [c]
      rw [norm_div, e.norm_map, e.norm_map, ← hxy, div_self (norm_ne_zero_iff.mpr hx)]
    have hphase : (Real.cos c.arg : ℂ) + Real.sin c.arg * Complex.I = c := by
      simpa only [hc, Complex.ofReal_one, one_mul, Complex.ofReal_cos, Complex.ofReal_sin] using Complex.norm_mul_cos_add_sin_mul_I c
    refine ⟨c.arg, e.injective ?_⟩
    rw [rotation_complex_coordinates, hphase]
    exact div_mul_cancel₀ (e y) hcx

end HallRay

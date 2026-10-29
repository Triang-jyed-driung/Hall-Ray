module

public import HallRay.Branches
public import HallRay.ConstantBranch

@[expose] public section
noncomputable section
namespace HallRay

/-- The chart before the scalar determinant normalization, with E = I. -/
def rawChart (u v : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, v.1, v.2; -u.1, 1, 0; -u.2, 0, 1]

def dot (v u : Point) : ℝ := v.1 * u.1 + v.2 * u.2

theorem rawChart_det (u v : Point) : (rawChart u v).det = 1 + dot v u := by
  simp [rawChart, Matrix.det_fin_three, dot]
  ring

theorem chart_positive {u v : Point} (hu : U u) (hv : V v) :
    124 / 125 ≤ 1 + dot v u := by
  have h₁ : |v.1 * u.1| ≤ (1 / 50 : ℝ) * (1 / 5) := by
    rw [abs_mul]
    exact mul_le_mul hv.1 hu.1 (abs_nonneg _) (by norm_num)
  have h₂ : |v.2 * u.2| ≤ (1 / 5 : ℝ) * (1 / 50) := by
    rw [abs_mul]
    exact mul_le_mul hv.2 hu.2 (abs_nonneg _) (by norm_num)
  have h₁' := (abs_le.mp h₁).1
  have h₂' := (abs_le.mp h₂).1
  dsimp [dot]
  linarith

/-- The block diagonal matrix before flow and scalar normalizations. -/
def rawReturn (s : Symbol) (u v : Point) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![e s v, 0, 0;
     0, (10 - sign s * u.2) / d s u, sign s * (u.1 - 1) / d s u;
     0, sign s / d s u, 10 / d s u]

/-- The exact block factorization underlying Proposition 3.1.
The exponential return time and cube-root chart normalization are not included. -/
theorem raw_marked_return (s : Symbol) {u v : Point} (hu : U u) (hv : V v) :
    rawChart (phi s u) v * (gamma s).map (Int.castRingHom ℝ) =
      rawReturn s u v * rawChart u (psi s v) := by
  have hd : d s u ≠ 0 := ne_of_gt (d_pos s hu)
  have he : e s v ≠ 0 := ne_of_gt (e_pos s hv)
  cases s <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rawChart, rawReturn, phi, psi, gamma, sign, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> simp_all [d, e, sign] <;> ring

/-- Direct verification of the real characteristic polynomial used in Section 4. -/
theorem gamma_a_characteristic (x : ℝ) :
    (x • (1 : Matrix (Fin 3) (Fin 3) ℝ) -
      (gamma .a).map (Int.castRingHom ℝ)).det = cubic x := by
  simp [Matrix.det_fin_three, gamma, cubic]
  ring

end HallRay

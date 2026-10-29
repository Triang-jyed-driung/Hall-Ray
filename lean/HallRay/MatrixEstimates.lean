module

public import HallRay.Contraction
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace HallRay

def firstRow (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; 0, 0]

theorem firstRow_mul_star (a b : ℝ) :
    firstRow a b * (firstRow a b)ᴴ = Matrix.diagonal ![a ^ 2 + b ^ 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstRow, Matrix.mul_apply, Fin.sum_univ_succ]
  all_goals ring

theorem diagonal_nonneg_norm {a : ℝ} (ha : 0 ≤ a) :
    ‖(Matrix.diagonal ![a, 0] : Matrix (Fin 2) (Fin 2) ℝ)‖ = a := by
  rw [Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg ha).mpr
    intro i
    fin_cases i <;> simp [Real.norm_eq_abs, abs_of_nonneg ha, ha]
  · have h := norm_le_pi_norm (![a, 0] : Fin 2 → ℝ) 0
    simpa only [Matrix.cons_val_zero, Real.norm_eq_abs, abs_of_nonneg ha] using h

theorem firstRow_norm_sq (a b : ℝ) : ‖firstRow a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (firstRow a b)ᴴ
  rw [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose, firstRow_mul_star,
    diagonal_nonneg_norm (by positivity)] at h
  nlinarith

theorem firstRow_norm_le (a b : ℝ) : ‖firstRow a b‖ ≤ |a| + |b| := by
  have hs := firstRow_norm_sq a b
  have hn := norm_nonneg (firstRow a b)
  have hprod := mul_nonneg (abs_nonneg a) (abs_nonneg b)
  nlinarith [sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]

theorem firstRow_norm_le_sqrt_two {a b r : ℝ} (ha : |a| ≤ r) (hb : |b| ≤ r) :
    ‖firstRow a b‖ ≤ Real.sqrt 2 * r := by
  have hr : 0 ≤ r := (abs_nonneg a).trans ha
  have ha' : a ^ 2 ≤ r ^ 2 := by nlinarith [sq_abs a, mul_self_le_mul_self (abs_nonneg a) ha]
  have hb' : b ^ 2 ≤ r ^ 2 := by nlinarith [sq_abs b, mul_self_le_mul_self (abs_nonneg b) hb]
  have hs := firstRow_norm_sq a b
  have htwo : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := norm_nonneg (firstRow a b)
  have hp : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg _) hr
  have hsq : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by rw [mul_pow, htwo]
  nlinarith

theorem numerator_difference (s : Symbol) (u v : Point) :
    fiberNumerator s u - fiberNumerator s v =
      firstRow (-sign s * (u.2 - v.2)) (sign s * (u.1 - v.1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fiberNumerator, firstRow] <;> ring

theorem numerator_difference_norm (s : Symbol) (u v : Point) :
    ‖fiberNumerator s u - fiberNumerator s v‖ ≤ Real.sqrt 2 * supDist u v := by
  rw [numerator_difference]
  apply firstRow_norm_le_sqrt_two
  · cases s <;> simp [sign, supDist, abs_sub_comm]
  · cases s <;> simp [sign, supDist, abs_sub_comm]

theorem numerator_zero_star (s : Symbol) :
    (fiberNumerator s (0, 0))ᴴ * fiberNumerator s (0, 0) =
      (101 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  cases s <;> ext i j
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [fiberNumerator, sign, Matrix.mul_apply, Fin.sum_univ_succ]

theorem numerator_zero_norm_sq (s : Symbol) : ‖fiberNumerator s (0, 0)‖ ^ 2 = 101 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (fiberNumerator s (0, 0))
  rw [numerator_zero_star, norm_smul, norm_one] at h
  norm_num at h
  nlinarith

theorem numerator_norm_le (s : Symbol) {u : Point} (hu : U u) :
    ‖fiberNumerator s u‖ ≤ 21 / 2 := by
  have hbase : ‖fiberNumerator s (0, 0)‖ ≤ 101 / 10 := by
    have := numerator_zero_norm_sq s
    have := norm_nonneg (fiberNumerator s (0, 0))
    nlinarith
  have hdiff : ‖fiberNumerator s u - fiberNumerator s (0, 0)‖ ≤ |u.2| + |u.1| := by
    rw [numerator_difference]
    have h := firstRow_norm_le (-sign s * (u.2 - 0)) (sign s * (u.1 - 0))
    cases s <;> simpa [sign] using h
  have htri := norm_sub_le (fiberNumerator s u - fiberNumerator s (0, 0))
    (-fiberNumerator s (0, 0))
  have htri' : ‖fiberNumerator s u‖ ≤
      ‖fiberNumerator s u - fiberNumerator s (0, 0)‖ + ‖fiberNumerator s (0, 0)‖ := by
    simpa using htri
  linarith [hu.1, hu.2]

end HallRay

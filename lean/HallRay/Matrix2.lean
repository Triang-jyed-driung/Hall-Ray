module

public import HallRay.MatrixEstimates
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace HallRay

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

def quarterTurn : Matrix2 := !![0, -1; 1, 0]

def adj2 (A : Matrix2) : Matrix2 := !![A 1 1, -A 0 1; -A 1 0, A 0 0]

theorem quarterTurn_star_mul : quarterTurnᴴ * quarterTurn = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [quarterTurn, Matrix.mul_apply, Fin.sum_univ_succ]

theorem quarterTurn_norm : ‖quarterTurn‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self quarterTurn
  rw [quarterTurn_star_mul, norm_one] at h
  have := norm_nonneg quarterTurn
  nlinarith

theorem adj2_formula (A : Matrix2) : adj2 A = quarterTurn * Aᴴ * (-quarterTurn) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj2, quarterTurn, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

theorem adj2_involution (A : Matrix2) : adj2 (adj2 A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj2]

theorem adj2_norm_le (A : Matrix2) : ‖adj2 A‖ ≤ ‖A‖ := by
  rw [adj2_formula]
  calc
    _ ≤ ‖quarterTurn * Aᴴ‖ * ‖-quarterTurn‖ := norm_mul_le _ _
    _ ≤ (‖quarterTurn‖ * ‖Aᴴ‖) * ‖-quarterTurn‖ := by gcongr; exact norm_mul_le _ _
    _ = ‖A‖ := by rw [norm_neg, quarterTurn_norm, Matrix.l2_opNorm_conjTranspose]; ring

theorem adj2_norm (A : Matrix2) : ‖adj2 A‖ = ‖A‖ := by
  apply le_antisymm (adj2_norm_le A)
  simpa only [adj2_involution] using adj2_norm_le (adj2 A)

theorem mul_adj2 (A : Matrix2) : A * adj2 A = A.det • (1 : Matrix2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj2, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem inv_eq_adj2 {A : Matrix2} (hA : A.det = 1) : A⁻¹ = adj2 A := by
  have hl : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (by rw [hA]; exact isUnit_one)
  have hr : A * adj2 A = 1 := by rw [mul_adj2, hA, one_smul]
  calc
    A⁻¹ = A⁻¹ * (A * adj2 A) := by rw [hr, mul_one]
    _ = adj2 A := by rw [← Matrix.mul_assoc, hl, one_mul]

theorem determinant_one_inverse_norm {A : Matrix2} (hA : A.det = 1) : ‖A⁻¹‖ = ‖A‖ := by
  rw [inv_eq_adj2 hA, adj2_norm]

end HallRay

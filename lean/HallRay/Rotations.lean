module

public import HallRay.Matrix2
public import HallRay.InfiniteOrder
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace HallRay

def rotation (θ : ℝ) : Matrix2 := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

@[simp] theorem rotation_zero : rotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation]

theorem rotation_add (θ φ : ℝ) : rotation (θ + φ) = rotation θ * rotation φ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

theorem rotation_pow (θ : ℝ) (n : ℕ) : rotation θ ^ n = rotation ((n : ℝ) * θ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul, rotation_add]

theorem rotation_det (θ : ℝ) : (rotation θ).det = 1 := by
  simp [rotation, Matrix.det_fin_two]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rotation_star_mul (θ : ℝ) : (rotation θ)ᴴ * rotation θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith [Real.sin_sq_add_cos_sq θ]

theorem rotation_norm (θ : ℝ) : ‖rotation θ‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (rotation θ)
  rw [rotation_star_mul, norm_one] at h
  have := norm_nonneg (rotation θ)
  nlinarith

theorem rotation_int_period (m : ℤ) : rotation ((m : ℝ) * (2 * Real.pi)) = 1 := by
  have hs : Real.sin ((m : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using Real.sin_add_int_mul_two_pi 0 m
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation, hs, Real.cos_int_mul_two_pi]

/-- A rational angle divided by pi gives a finite-order rotation. -/
theorem rotation_finite_order_of_not_irrational {θ : ℝ} (hθ : ¬Irrational (θ / Real.pi)) :
    ∃ k : ℕ, 0 < k ∧ rotation θ ^ k = 1 := by
  obtain ⟨q, hq⟩ : ∃ q : ℚ, (q : ℝ) = θ / Real.pi := by simpa [Irrational] using hθ
  have hθ' : θ = (q : ℝ) * Real.pi := by
    have h := (div_eq_iff Real.pi_ne_zero).mp hq.symm
    exact h
  refine ⟨2 * q.den, by have := q.pos; omega, ?_⟩
  rw [rotation_pow]
  have he : ((2 * q.den : ℕ) : ℝ) * θ = (q.num : ℝ) * (2 * Real.pi) := by
    rw [hθ', Rat.cast_def]
    push_cast
    field_simp
  rw [he, rotation_int_period]

theorem conjugate_rotation_pow {A G : Matrix2} (hG : G.det ≠ 0) {θ : ℝ}
    (hconj : A = G * rotation θ * G⁻¹) (n : ℕ) :
    A ^ n = G * rotation ((n : ℝ) * θ) * G⁻¹ := by
  have hGl : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hG)
  have hGr : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG)
  have hp : ∀ n : ℕ, A ^ n = G * rotation θ ^ n * G⁻¹ := by
    intro n
    induction n with
    | zero => simpa using hGr.symm
    | succ n ih =>
      rw [pow_succ, ih, hconj]
      simp only [Matrix.mul_assoc]
      have he : G⁻¹ * (G * (rotation θ * G⁻¹)) = rotation θ * G⁻¹ := by
        rw [← Matrix.mul_assoc, hGl, one_mul]
      rw [he]
      simp only [← Matrix.mul_assoc, ← pow_succ]
  rw [hp, rotation_pow]

theorem conjugate_rotation_power_norm_le {A G : Matrix2} (hG : G.det ≠ 0) {θ : ℝ}
    (hconj : A = G * rotation θ * G⁻¹) (n : ℕ) : ‖A ^ n‖ ≤ ‖G‖ * ‖G⁻¹‖ := by
  rw [conjugate_rotation_pow hG hconj]
  calc
    _ ≤ ‖G * rotation ((n : ℝ) * θ)‖ * ‖G⁻¹‖ := norm_mul_le _ _
    _ ≤ (‖G‖ * ‖rotation ((n : ℝ) * θ)‖) * ‖G⁻¹‖ := by gcongr; exact norm_mul_le _ _
    _ = _ := by rw [rotation_norm, mul_one]

/-- Infinite order of an elliptic fiber forces any conjugate rotation angle to be irrational. -/
theorem irrational_of_infinite_order {A G : Matrix2} (hG : G.det ≠ 0) {θ : ℝ}
    (hconj : A = G * rotation θ * G⁻¹) (horder : ∀ k : ℕ, 0 < k → A ^ k ≠ 1) :
    Irrational (θ / Real.pi) := by
  by_contra hθ
  obtain ⟨k, hk, hrot⟩ := rotation_finite_order_of_not_irrational hθ
  have hGr : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG)
  apply horder k hk
  rw [conjugate_rotation_pow hG hconj k, ← rotation_pow, hrot, mul_one, hGr]

end HallRay

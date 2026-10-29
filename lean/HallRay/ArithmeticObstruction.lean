module

public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Tactic

/-! An elementary alternative to the splitting-field argument in Section 4.
A cubic integer characteristic polynomial cannot have two equal contracting
positive eigenvalues and determinant one. This is the obstruction needed
when an elliptic return is assumed to have rational rotation angle. -/
@[expose] public section
noncomputable section
namespace HallRay

/-- Integer coefficients force a repeated contracting root to be an integer.
The hypotheses are the elementary symmetric functions of (A, r, r). -/
theorem no_repeated_contracting_root (s t : ℤ) {A r : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hdet : A * r ^ 2 = 1)
    (hs : (s : ℝ) = A + 2 * r) (ht : (t : ℝ) = 2 * A * r + r ^ 2) : False := by
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hA : 1 < A := by
    by_contra! h
    have hh := mul_le_mul_of_nonneg_right h (sq_nonneg r)
    nlinarith
  have hdenid : (s : ℝ) ^ 2 - 3 * (t : ℝ) = (A - r) ^ 2 := by rw [hs, ht]; ring
  have hden : (s : ℝ) ^ 2 - 3 * (t : ℝ) ≠ 0 := by
    rw [hdenid]
    exact ne_of_gt (sq_pos_of_pos (by linarith))
  have hrel : (s : ℝ) * (t : ℝ) - 9 =
      2 * r * ((s : ℝ) ^ 2 - 3 * (t : ℝ)) := by
    rw [hs, ht]
    linear_combination 9 * hdet
  let q : ℚ := (s * t - 9) / (2 * (s ^ 2 - 3 * t))
  have hq : (q : ℝ) = r := by
    have hcast : (q : ℝ) = ((s : ℝ) * (t : ℝ) - 9) /
        (2 * ((s : ℝ) ^ 2 - 3 * (t : ℝ))) := by dsimp [q]; norm_cast
    rw [hcast]
    apply (div_eq_iff (mul_ne_zero (by norm_num) hden)).mpr
    nlinarith
  let p : Polynomial ℤ := Polynomial.X ^ 3 - Polynomial.C s * Polynomial.X ^ 2 +
    Polynomial.C t * Polynomial.X - 1
  have hp : p.Monic := by
    apply Polynomial.monic_of_degree_le 3
    · dsimp [p]
      compute_degree!
    · simp only [p, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        Polynomial.coeff_mul_X, Polynomial.coeff_X_pow, Polynomial.coeff_one]
      norm_num
      change (Polynomial.C t).coeff 2 = 0
      rw [Polynomial.coeff_C]
      norm_num
  have hroot : r ^ 3 - (s : ℝ) * r ^ 2 + (t : ℝ) * r - 1 = 0 := by
    rw [hs, ht]
    linear_combination hdet
  have hint : IsIntegral ℤ r := by
    refine ⟨p, hp, ?_⟩
    change Polynomial.eval₂ (algebraMap ℤ ℝ) r p = 0
    dsimp [p]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one]
    exact_mod_cast hroot
  obtain ⟨k, hk⟩ := hint.mem_range_ratCast_iff.mp ⟨q, hq⟩
  have hk0 : 0 < k := by exact_mod_cast (hk ▸ hr)
  have hk1 : k < 1 := by exact_mod_cast (hk ▸ hr1)
  omega

end HallRay

module

public import HallRay.FiberEstimates
public import HallRay.Suspension

@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace HallRay

theorem relative_error_append (P P' A B : Mat2) (hA : A.det = 1) :
    (P * A)⁻¹ * (P' * B) - 1 =
      A⁻¹ * (P⁻¹ * P' - 1) * B + A⁻¹ * (B - A) := by
  have hAA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (by rw [hA]; exact isUnit_one)
  rw [Matrix.mul_inv_rev]
  calc
    _ = A⁻¹ * (P⁻¹ * P' - 1) * B + A⁻¹ * (B - A) + (A⁻¹ * A - 1) := by
      noncomm_ring
    _ = _ := by rw [hAA]; simp

/-- The last factors of two agreeing words differ by a geometrically small amount. -/
theorem fiber_last_difference {z z' : Word} (l N : ℕ)
    (h : ∀ i : ℕ, i < l + 1 + N → z (i : ℤ) = z' (i : ℤ)) :
    ‖fiberMap (shift (l : ℤ) z') - fiberMap (shift (l : ℤ) z)‖ ≤
      (2 / 25 : ℝ) * (1 / 900 : ℝ) ^ N := by
  have hs : (shift (l : ℤ) z') 0 = (shift (l : ℤ) z) 0 := by
    simpa [shift] using (h l (by omega)).symm
  have hfuture : ∀ i : ℕ, i < N →
      (shift 1 (shift (l : ℤ) z')) (i : ℤ) = (shift 1 (shift (l : ℤ) z)) (i : ℤ) := by
    intro i hi
    have hh := (h (i + 1 + l) (by omega)).symm
    simpa [shift, Nat.cast_add, Nat.cast_one, add_assoc] using hh
  unfold fiberMap
  rw [hs]
  calc
    _ ≤ (1 / 5 : ℝ) * supDist (futureCode (shift 1 (shift (l : ℤ) z')))
        (futureCode (shift 1 (shift (l : ℤ) z))) :=
      fiber_lipschitz _ (futureCode_mem _) (futureCode_mem _)
    _ ≤ (1 / 5 : ℝ) * ((2 / 5 : ℝ) * (1 / 900 : ℝ) ^ N) := by
      gcongr
      exact futureCode_closeness N hfuture
    _ = _ := by ring

/-- A slightly sharper estimate than the paper's uniform finite-word bound.
The induction uses the extra future symbol at each preceding product length,
which avoids introducing a separate telescoping-sum formalization. -/
theorem fiber_product_error_sharp (l N : ℕ) {z z' : Word}
    (h : ∀ i : ℕ, i < l + N → z (i : ℤ) = z' (i : ℤ)) :
    ‖(cocycle fiberMap z l)⁻¹ * cocycle fiberMap z' l - 1‖ ≤
      (1 / 10 : ℝ) * (1 / 900 : ℝ) ^ N := by
  induction l generalizing N z z' with
  | zero => simp
  | succ l ih =>
    have hprev : ∀ i : ℕ, i < l + (N + 1) → z (i : ℤ) = z' (i : ℤ) := by
      intro i hi
      exact h i (by omega)
    have he := ih (N + 1) hprev
    have hd := fiber_last_difference l N (fun i hi => h i (by omega))
    have hnA : ‖(fiberMap (shift (l : ℤ) z))⁻¹‖ ≤ 11 / 10 := by
      have := fiber_inverse_norm_le ((shift (l : ℤ) z) 0) (futureCode_mem (shift 1 (shift (l : ℤ) z)))
      change ‖(fiberMap (shift (l : ℤ) z))⁻¹‖ ≤ 26 / 25 at this
      linarith
    have hnB : ‖fiberMap (shift (l : ℤ) z')‖ ≤ 11 / 10 := by
      have := fiber_norm_le ((shift (l : ℤ) z') 0) (futureCode_mem (shift 1 (shift (l : ℤ) z')))
      change ‖fiberMap (shift (l : ℤ) z')‖ ≤ 26 / 25 at this
      linarith
    rw [cocycle_succ, cocycle_succ, relative_error_append _ _ _ _ (fiberMap_det _)]
    calc
      _ ≤ ‖(fiberMap (shift (l : ℤ) z))⁻¹ *
          ((cocycle fiberMap z l)⁻¹ * cocycle fiberMap z' l - 1) * fiberMap (shift (l : ℤ) z')‖ +
          ‖(fiberMap (shift (l : ℤ) z))⁻¹ * (fiberMap (shift (l : ℤ) z') - fiberMap (shift (l : ℤ) z))‖ :=
        norm_add_le _ _
      _ ≤ ((11 / 10 : ℝ) * ((1 / 10 : ℝ) * (1 / 900 : ℝ) ^ (N + 1))) * (11 / 10 : ℝ) +
          (11 / 10 : ℝ) * ((2 / 25 : ℝ) * (1 / 900 : ℝ) ^ N) := by
        apply add_le_add
        · calc
            _ ≤ (‖(fiberMap (shift (l : ℤ) z))⁻¹‖ *
                ‖(cocycle fiberMap z l)⁻¹ * cocycle fiberMap z' l - 1‖) * ‖fiberMap (shift (l : ℤ) z')‖ := by
              exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            _ ≤ _ := by gcongr
        · exact (norm_mul_le _ _).trans (mul_le_mul hnA hd (norm_nonneg _) (by norm_num))
      _ ≤ (1 / 10 : ℝ) * (1 / 900 : ℝ) ^ N := by
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 900) N]

/-- Lemma `lem:fiber-bound`, in an equivalent nonnegative-power notation. -/
theorem fiber_product_error (l N : ℕ) {z z' : Word}
    (h : ∀ i : ℕ, i < l + N → z (i : ℤ) = z' (i : ℤ)) :
    ‖(cocycle fiberMap z l)⁻¹ * cocycle fiberMap z' l - 1‖ ≤ (1 / 600 : ℝ) ^ N := by
  have hs := fiber_product_error_sharp l N h
  have hp : (1 / 900 : ℝ) ^ N ≤ (1 / 600 : ℝ) ^ N :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) N
  have hn : 0 ≤ (1 / 900 : ℝ) ^ N := by positivity
  linarith

end HallRay

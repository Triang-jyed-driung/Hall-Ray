module

public import HallRay.Spectrum
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
noncomputable section
namespace HallRay
namespace PlaneNorm

variable (N : PlaneNorm)

theorem zero : N.value 0 = 0 := (N.eq_zero_iff 0).mpr rfl

theorem neg (u : Point) : N.value (-u) = N.value u := by
  have h := N.smul_eq (-1) u
  simpa using h

theorem reverse_triangle (u v : Point) : |N.value u - N.value v| ≤ N.value (u - v) := by
  have h₁ := N.add_le (u - v) v
  have h₂ := N.add_le (v - u) u
  simp only [sub_add_cancel] at h₁ h₂
  have he : N.value (v - u) = N.value (u - v) := by rw [← neg_sub, N.neg]
  rw [he] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def bound : ℝ := N.value (1, 0) + N.value (0, 1)

theorem bound_nonneg : 0 ≤ N.bound := add_nonneg (N.nonneg _) (N.nonneg _)

theorem upper_bound (u : Point) : N.value u ≤ N.bound * ‖u‖ := by
  have he : u = u.1 • ((1, 0) : Point) + u.2 • ((0, 1) : Point) := by ext <;> simp
  have h := N.add_le (u.1 • ((1, 0) : Point)) (u.2 • ((0, 1) : Point))
  rw [← he, N.smul_eq, N.smul_eq] at h
  have hx : |u.1| ≤ ‖u‖ := by rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_left _ _
  have hy : |u.2| ≤ ‖u‖ := by rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]; exact le_max_right _ _
  calc
    _ ≤ |u.1| * N.value (1, 0) + |u.2| * N.value (0, 1) := h
    _ ≤ ‖u‖ * N.value (1, 0) + ‖u‖ * N.value (0, 1) := by
      gcongr <;> exact N.nonneg _
    _ = _ := by dsimp [bound]; ring

theorem lipschitz : LipschitzWith N.bound.toNNReal N.value := by
  apply LipschitzWith.of_dist_le'
  intro u v
  rw [Real.dist_eq, dist_eq_norm]
  exact (N.reverse_triangle u v).trans (N.upper_bound (u - v))

theorem continuous : Continuous N.value := N.lipschitz.continuous

/-- Every plane norm dominates a positive multiple of the usual sup norm. -/
theorem exists_lower_bound : ∃ c : ℝ, 0 < c ∧ ∀ u : Point, c * ‖u‖ ≤ N.value u := by
  have hnonempty : (Metric.sphere (0 : Point) 1).Nonempty := by
    refine ⟨(1, 0), ?_⟩
    simp [Prod.norm_def]
  obtain ⟨v, hv, hmin⟩ := (isCompact_sphere (0 : Point) 1).exists_isMinOn hnonempty N.continuous.continuousOn
  have hvnorm : ‖v‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hv
  have hv0 : v ≠ 0 := by intro he; rw [he, norm_zero] at hvnorm; norm_num at hvnorm
  have hNv : 0 < N.value v := lt_of_le_of_ne (N.nonneg v) (by
    intro he
    exact hv0 ((N.eq_zero_iff v).mp he.symm))
  refine ⟨N.value v, hNv, ?_⟩
  intro u
  by_cases hu : u = 0
  · simp [hu, N.zero]
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hunit : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm), inv_mul_cancel₀ (ne_of_gt hnorm)]
  have hmem : ‖u‖⁻¹ • u ∈ Metric.sphere (0 : Point) 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hunit
  have hm := hmin hmem
  change N.value v ≤ N.value (‖u‖⁻¹ • u) at hm
  rw [N.smul_eq, abs_of_pos (inv_pos.mpr hnorm)] at hm
  have hmul := mul_le_mul_of_nonneg_right hm hnorm.le
  have he : (‖u‖⁻¹ * N.value u) * ‖u‖ = N.value u := by
    field_simp
  rw [he] at hmul
  exact hmul

end PlaneNorm
end HallRay

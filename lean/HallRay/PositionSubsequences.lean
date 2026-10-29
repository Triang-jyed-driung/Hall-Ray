module

public import HallRay.BoundaryHeightLimits

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- A bounded return position recurs along a subsequence, or the positions escape. -/
theorem nat_sequence_constant_subseq_or_tendsto (j : ℕ → ℕ) :
    (∃ r : ℕ, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, j (φ i) = r) ∨ Tendsto j atTop atTop := by
  classical
  by_cases h : Tendsto j atTop atTop
  · exact Or.inr h
  · left
    rw [tendsto_atTop] at h
    push Not at h
    obtain ⟨b, hb⟩ := h
    have hf : ∃ᶠ i in atTop, ∃ r ∈ Finset.range b, j i = r := by
      exact hb.mono (fun i hi => ⟨j i, Finset.mem_range.mpr hi, rfl⟩)
    obtain ⟨r, _, hr⟩ := (Finset.frequently_exists (Finset.range b)).mp hf
    obtain ⟨φ, hφ, hconst⟩ := extraction_of_frequently_atTop hr
    exact ⟨r, φ, hφ, hconst⟩

/-- Partial periodic products in the bulk converge to their constant rotation phase. -/
theorem periodic_bulk_product_limit {n j : ℕ → ℕ} (hj : ∀ i, j i ≤ n i)
    (hd : Tendsto (fun i => n i - j i) atTop atTop) {ξ : Real.Angle}
    (hξ : Tendsto (fun i => phase (j i)) atTop (𝓝 ξ)) :
    Tendsto (fun i => cocycle fiberMap (periodicWord (n i)) (j i)) atTop
      (𝓝 (ellipticCircle constantMatrix ξ)) := by
  have he : Tendsto (fun i => cocycle fiberMap (periodicWord (n i)) (j i) - constantMatrix ^ j i)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun i => periodic_partial_error (n i) (j i) (hj i))
    have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 900)
      (by norm_num : (1 / 900 : ℝ) < 1)).comp hd
    simpa only [mul_zero, Function.comp_def] using (hp.const_mul (1 / 10 : ℝ)).const_mul constantPowerBound
  have hc : Tendsto (fun i => constantMatrix ^ j i) atTop (𝓝 (ellipticCircle constantMatrix ξ)) := by
    have h := (ellipticCircle_continuous constantMatrix).continuousAt.tendsto.comp hξ
    simpa only [phase, Function.comp_def, ellipticCircle_phase (fiberMap_det constantWord)
      constantMatrix_elliptic] using h
  simpa only [sub_add_cancel, zero_add] using he.add hc

theorem periodic_bulk_word_limit {n j : ℕ → ℕ} (hjle : ∀ i, j i ≤ n i)
    (hj : Tendsto j atTop atTop) (hd : Tendsto (fun i => n i - j i) atTop atTop) :
    Tendsto (fun i => shift (j i : ℤ) (periodicWord (n i))) atTop (𝓝 constantWord) := by
  apply periodicWord_bulk_limit hj
  have hcast := (tendsto_natCast_atTop_atTop (R := ℤ)).comp hd
  exact hcast.congr (fun i => by exact Nat.cast_sub (hjle i))

end HallRay

module

public import HallRay.DepthDegeneration

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

theorem depthFunction_continuousOn (N : PlaneNorm) (E : FiberParameter) :
    ContinuousOn (depthFunction N E) (Set.Ioo (-2) 2) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have he : (Set.Ioo (-2 : ℝ) 2).domRestrict (depthFunction N E) =
      fun v : TraceParameter => limitingDepth N (E, v) := by
    funext v
    simp [depthFunction, v.property]
  rw [he]
  exact Continuous.comp (f := fun v : TraceParameter => (E, v))
    (g := limitingDepth N) (limitingDepth_continuous N) (continuous_const.prodMk continuous_id)

/-- The continuous limiting maxima themselves contain a ray.
Realizing these as single-orbit limsups still requires concatenation. -/
theorem limiting_maxima_ray (N : PlaneNorm) (E : FiberParameter) :
    ∃ T : ℝ, 0 < T ∧ ∀ A : ℝ, T < A →
      ∃ v : TraceParameter, limitingDepth N (E, v) = ENNReal.ofReal A := by
  let v₀ : TraceParameter := ⟨0, by norm_num⟩
  let T := (limitingDepth N (E, v₀)).toReal + 1
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T, hT, ?_⟩
  intro A hA
  have hAp : 0 < A := hT.trans hA
  let : NeBot (𝓝[Set.Ioo (-2 : ℝ) 2] 2) := by
    rw [nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (-2 : ℝ) < 2)]
    infer_instance
  have hmem : ∀ᶠ v : ℝ in 𝓝[Set.Ioo (-2) 2] 2, v ∈ Set.Ioo (-2) 2 := self_mem_nhdsWithin
  obtain ⟨v, hv, hhigh⟩ := (hmem.and
    (limitingDepth_uniform_lower N (norm_nonneg E.val) hAp.le)).exists
  have hlo : depthFunction N E 0 ≤ ENNReal.ofReal A := by
    rw [depthFunction, dite_eq_left (by norm_num)]
    have hz : ENNReal.ofReal ((limitingDepth N (E, v₀)).toReal) = limitingDepth N (E, v₀) :=
      ENNReal.ofReal_toReal (limitingDepth_ne_top N (E, v₀))
    change limitingDepth N (E, v₀) ≤ _
    rw [← hz]
    apply ENNReal.ofReal_le_ofReal
    dsimp [T] at hA
    linarith
  have hhi : ENNReal.ofReal A ≤ depthFunction N E v := by
    rw [depthFunction, dite_eq_left hv]
    exact (ENNReal.ofReal_le_ofReal (by linarith : A ≤ A + 1)).trans (hhigh hv E le_rfl)
  obtain ⟨u, hu, heq⟩ := isPreconnected_Ioo.intermediate_value
    (show (0 : ℝ) ∈ Set.Ioo (-2) 2 by norm_num) hv (depthFunction_continuousOn N E) ⟨hlo, hhi⟩
  refine ⟨⟨u, hu⟩, ?_⟩
  simpa only [depthFunction, dite_eq_left hu] using heq

end HallRay

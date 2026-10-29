module

public import HallRay.AdjustedPeriodicChoice

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

def identityFiber : FiberParameter := ⟨1, by simp⟩
def zeroTrace : TraceParameter := ⟨0, by norm_num⟩

def traceSegment (v : TraceParameter) (a : FlightParameter) : TraceParameter :=
  ⟨(a : ℝ) * (v : ℝ), by
    by_cases h0 : (a : ℝ) = 0
    · simp [h0]
    · have ha : 0 < (a : ℝ) := lt_of_le_of_ne a.property.1 (Ne.symm h0)
      have hl := mul_lt_mul_of_pos_left v.property.1 ha
      have hu := mul_lt_mul_of_pos_left v.property.2 ha
      constructor <;> nlinarith [a.property.2]⟩

@[fun_prop] theorem traceSegment_continuous (v : TraceParameter) : Continuous (traceSegment v) :=
  (continuous_subtype_val.mul_const (v : ℝ)).subtype_mk _

@[simp] theorem traceSegment_zero (v : TraceParameter) : traceSegment v ⟨0, by norm_num⟩ = zeroTrace := by
  apply Subtype.ext
  simp [traceSegment, zeroTrace]

@[simp] theorem traceSegment_one (v : TraceParameter) : traceSegment v ⟨1, by norm_num⟩ = v := by
  apply Subtype.ext
  simp [traceSegment]

/-- Small changes of the accumulated fiber can be compensated by changing the elliptic trace.
The accompanying power bound is independent of that fiber change. -/
theorem fiber_adjustment (N : PlaneNorm) :
    ∃ T : ℝ, 0 < T ∧ ∀ A : ℝ, T < A →
      ∃ δ K : ℝ, 0 < δ ∧ δ < 1 ∧ 1 ≤ K ∧
        ∀ E : FiberParameter, ‖E.val - 1‖ ≤ δ →
          ∃ v : TraceParameter, realLimitingDepth N (E, v) = A ∧
            ellipticPowerConstant (ellipticTracePath v) < K := by
  let T := max 1 (realLimitingDepth N (identityFiber, zeroTrace))
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨T, hT, ?_⟩
  intro A hA
  have hAp : 0 < A := hT.trans hA
  have hlo₀ : realLimitingDepth N (identityFiber, zeroTrace) < A :=
    lt_of_le_of_lt (le_max_right _ _) hA
  let : NeBot (𝓝[Set.Ioo (-2 : ℝ) 2] 2) := by
    rw [nhdsWithin_Ioo_eq_nhdsLT (by norm_num : (-2 : ℝ) < 2)]
    infer_instance
  have hmem : ∀ᶠ v : ℝ in 𝓝[Set.Ioo (-2) 2] 2, v ∈ Set.Ioo (-2) 2 := self_mem_nhdsWithin
  obtain ⟨b, hb, hhigh⟩ := (hmem.and
    (limitingDepth_uniform_lower N (norm_nonneg identityFiber.val) hAp.le)).exists
  let vPlus : TraceParameter := ⟨b, hb⟩
  have hhi₀ : A < realLimitingDepth N (identityFiber, vPlus) := by
    have hh := ENNReal.toReal_mono (limitingDepth_ne_top N (identityFiber, vPlus))
      (hhigh hb identityFiber le_rfl)
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ A + 1)] at hh
    exact lt_of_lt_of_le (by linarith : A < A + 1) hh
  have hc (v : TraceParameter) : Continuous (fun E : FiberParameter => realLimitingDepth N (E, v)) :=
    Continuous.comp (g := realLimitingDepth N) (f := fun E : FiberParameter => (E, v))
      (realLimitingDepth_continuous N) (continuous_id.prodMk continuous_const)
  have hneigh : ∀ᶠ E in 𝓝 identityFiber,
      realLimitingDepth N (E, zeroTrace) < A ∧ A < realLimitingDepth N (E, vPlus) :=
    ((hc zeroTrace).tendsto identityFiber |>.eventually (gt_mem_nhds hlo₀)).and
      ((hc vPlus).tendsto identityFiber |>.eventually (lt_mem_nhds hhi₀))
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hneigh
  let δ := min (d / 2) (1 / 2 : ℝ)
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδd : δ < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨K, hK, hbound⟩ := trace_compact_power_bound (isCompact_range (traceSegment_continuous vPlus))
  refine ⟨δ, K, hδ, hδ1, hK, ?_⟩
  intro E hE
  have hdist : dist E identityFiber < d := by
    rw [Subtype.dist_eq, dist_eq_norm]
    exact hE.trans_lt hδd
  have hbracket := hball (Metric.mem_ball.mpr hdist)
  have hf : Continuous (fun a : FlightParameter => realLimitingDepth N (E, traceSegment vPlus a)) :=
    Continuous.comp (g := realLimitingDepth N)
      (f := fun a : FlightParameter => (E, traceSegment vPlus a))
      (realLimitingDepth_continuous N) (continuous_const.prodMk (traceSegment_continuous vPlus))
  have hlo : realLimitingDepth N (E, traceSegment vPlus ⟨0, by norm_num⟩) ≤ A := by
    simpa only [traceSegment_zero] using hbracket.1.le
  have hhi : A ≤ realLimitingDepth N (E, traceSegment vPlus ⟨1, by norm_num⟩) := by
    simpa only [traceSegment_one] using hbracket.2.le
  obtain ⟨a, _, ha⟩ := isPreconnected_univ.intermediate_value
    (Set.mem_univ (⟨0, by norm_num⟩ : FlightParameter))
    (Set.mem_univ (⟨1, by norm_num⟩ : FlightParameter)) hf.continuousOn ⟨hlo, hhi⟩
  exact ⟨traceSegment vPlus a, ha, hbound _ (Set.mem_range_self a)⟩

end HallRay

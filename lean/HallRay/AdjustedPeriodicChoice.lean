module

public import HallRay.WordSplicing

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

def realLimitingDepth (N : PlaneNorm) (d : FiberParameter × TraceParameter) : ℝ :=
  (limitingDepth N d).toReal

theorem realLimitingDepth_continuous (N : PlaneNorm) : Continuous (realLimitingDepth N) := by
  apply continuous_iff_continuousAt.mpr
  intro d
  exact (ENNReal.continuousAt_toReal (limitingDepth_ne_top N d)).comp
    (limitingDepth_continuous N).continuousAt

theorem realPeriodicDepth_tendsto (N : PlaneNorm) {n : ℕ → ℕ}
    (hn : Tendsto n atTop atTop) (hadm : ∀ᶠ i in atTop, Admissible (n i))
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    {E : ℕ → FiberParameter} {E₀ : FiberParameter} (hE : Tendsto E atTop (𝓝 E₀)) :
    Tendsto (fun i => (periodicDepth N (n i) (E i)).toReal) atTop (𝓝 (realLimitingDepth N (E₀, v))) :=
  (ENNReal.continuousAt_toReal (limitingDepth_ne_top N (E₀, v))).tendsto.comp
    (periodicDepth_tendsto N hn hadm v hP hE)

/-- Choose a long periodic block with the prescribed depth and a common all-powers bound. -/
theorem adjusted_periodic_choice (N : PlaneNorm) (E : FiberParameter) (v : TraceParameter)
    {A K ε : ℝ} (htarget : realLimitingDepth N (E, v) = A)
    (hK : ellipticPowerConstant (ellipticTracePath v) < K) (hε : 0 < ε) (M : ℕ) :
    ∃ n : ℕ, M < n ∧ Admissible n ∧
      |(periodicDepth N n E).toReal - A| < ε ∧ ellipticPowerConstant (periodMatrix n) < K := by
  obtain ⟨n, hn, hphase, hadm⟩ := admissible_approximating_sequence
    (tracePhase rotationDefect v) (ellipticTracePath_elliptic v.property)
  have hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)) :=
    period_phase_limit hn.tendsto_atTop hphase
  have hdepth := realPeriodicDepth_tendsto N hn.tendsto_atTop hadm v hP
    (tendsto_const_nhds (x := E))
  rw [htarget] at hdepth
  have hclose : ∀ᶠ i in atTop, |(periodicDepth N (n i) E).toReal - A| < ε := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hdepth ε hε)
  have hbound : ∀ᶠ i in atTop, ellipticPowerConstant (periodMatrix (n i)) < K :=
    ((ellipticPowerConstant_continuousAt (ellipticTracePath_det v)
      (ellipticTracePath_elliptic v.property)).tendsto.comp hP).eventually (gt_mem_nhds hK)
  obtain ⟨i, hi, ha, hc, hb⟩ := ((hn.tendsto_atTop.eventually (eventually_gt_atTop M)).and
    (hadm.and (hclose.and hbound))).exists
  exact ⟨n i, hi, ha, hc, hb⟩

end HallRay

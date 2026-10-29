module

public import HallRay.PeriodicFrameClusters

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

/-- No sequence of maximizing periodic representatives can overshoot the limiting maximum. -/
theorem periodic_limsup_le_limitingDepth (N : PlaneNorm) {n : ℕ → ℕ}
    (hn : Tendsto n atTop atTop) (hadm : ∀ᶠ i in atTop, Admissible (n i))
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    {E : ℕ → FiberParameter} {E₀ : FiberParameter} (hE : Tendsto E atTop (𝓝 E₀)) :
    limsup (fun i => periodicDepth N (n i) (E i)) atTop ≤ limitingDepth N (E₀, v) := by
  classical
  apply (limsup_le_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
  intro y hy
  by_contra hnot
  have hfreq : ∃ᶠ i in atTop, y ≤ periodicDepth N (n i) (E i) := by
    simpa only [not_lt] using not_eventually.mp hnot
  obtain ⟨φ, hφ, hall⟩ := extraction_of_frequently_atTop (hfreq.and_eventually hadm)
  choose A hA hmax using (fun i => periodicDepth_attained N (n (φ i)) (hall i).2 (E (φ i)))
  have hrep (i : ℕ) : ∃ j : Fin (n (φ i) + 1), ∃ p : Real.Angle × FlightParameter,
      periodicFrame (n (φ i)) j p = A i := Set.mem_iUnion.mp (hA i)
  choose j p hrep using hrep
  obtain ⟨ψ, hψ, q, hheight⟩ := periodic_height_cluster N (hn.comp hφ.tendsto_atTop)
    (fun i => Nat.le_of_lt_succ (j i).isLt) (Eventually.of_forall (fun i => (hall i).2)) v
    (hP.comp hφ.tendsto_atTop) (hE.comp hφ.tendsto_atTop) (fun i => (p i).1) (fun i => (p i).2)
  have hbad (i : ℕ) : y ≤ frameHeight N (blockFiber (E (φ (ψ i))).val *
      beginningPeriodicFrame (n (φ (ψ i))) (j (ψ i)).val (p (ψ i)).1 (p (ψ i)).2) := by
    have hh := (hall (ψ i)).1
    rw [hmax (ψ i), ← hrep (ψ i)] at hh
    exact hh
  have hlow := ge_of_tendsto hheight (Eventually.of_forall hbad)
  have hu : limitingHeightFamily N (E₀, v) q ≤ limitingDepth N (E₀, v) := le_sSup ⟨q, rfl⟩
  exact (not_le_of_gt hy) (hlow.trans hu)

/-- Joint sequential convergence of periodic maxima, including moving initial fibers. -/
theorem periodicDepth_tendsto (N : PlaneNorm) {n : ℕ → ℕ}
    (hn : Tendsto n atTop atTop) (hadm : ∀ᶠ i in atTop, Admissible (n i))
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    {E : ℕ → FiberParameter} {E₀ : FiberParameter} (hE : Tendsto E atTop (𝓝 E₀)) :
    Tendsto (fun i => periodicDepth N (n i) (E i)) atTop (𝓝 (limitingDepth N (E₀, v))) := by
  exact tendsto_of_le_liminf_of_limsup_le (limitingDepth_le_periodic_liminf N hn hadm v hP hE)
    (periodic_limsup_le_limitingDepth N hn hadm v hP hE)

/-- Every elliptic trace has arbitrarily long periodic approximations with converging maxima. -/
theorem periodic_approximating_depths (N : PlaneNorm) (v : TraceParameter) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ (∀ᶠ i in atTop, Admissible (n i)) ∧
      ∀ E : FiberParameter, Tendsto (fun i => periodicDepth N (n i) E) atTop
        (𝓝 (limitingDepth N (E, v))) := by
  obtain ⟨n, hn, hphase, hadm⟩ := admissible_approximating_sequence
    (tracePhase rotationDefect v) (ellipticTracePath_elliptic v.property)
  refine ⟨n, hn, hadm, ?_⟩
  intro E
  exact periodicDepth_tendsto N hn.tendsto_atTop hadm v (period_phase_limit hn.tendsto_atTop hphase)
    tendsto_const_nhds

end HallRay

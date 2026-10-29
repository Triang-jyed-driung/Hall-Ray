module

public import HallRay.MovingBoundaryFrames

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

theorem beginning_height_cluster (N : PlaneNorm) {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    {E : ℕ → FiberParameter} {E₀ : FiberParameter} (hE : Tendsto E atTop (𝓝 E₀))
    (r : ℕ) (θ : ℕ → Real.Angle) (a : ℕ → FlightParameter) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : LimitingParameter,
      Tendsto (fun i => frameHeight N (blockFiber (E (φ i)).val *
        beginningPeriodicFrame (n (φ i)) r (θ (φ i)) (a (φ i)))) atTop
          (𝓝 (limitingHeightFamily N (E₀, v) p)) := by
  obtain ⟨q, φ, hφ, hq⟩ := CompactSpace.tendsto_subseq (fun i => (θ i, a i))
  have hθ : Tendsto (fun i => θ (φ i)) atTop (𝓝 q.1) := continuous_fst.continuousAt.tendsto.comp hq
  have ha : Tendsto (fun i => a (φ i)) atTop (𝓝 q.2) := continuous_snd.continuousAt.tendsto.comp hq
  have hf := beginningPeriodicFrame_limit_moving (hn.comp hφ.tendsto_atTop) v
    (hP.comp hφ.tendsto_atTop) r hθ ha
  exact ⟨φ, hφ, _, translated_frame_height_limit N (hE.comp hφ.tendsto_atTop) hf (limitingFrame_det _ _)⟩

theorem end_height_cluster (N : PlaneNorm) {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    {E : ℕ → FiberParameter} {E₀ : FiberParameter} (hE : Tendsto E atTop (𝓝 E₀))
    (r : ℕ) (θ : ℕ → Real.Angle) (a : ℕ → FlightParameter) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : LimitingParameter,
      Tendsto (fun i => frameHeight N (blockFiber (E (φ i)).val *
        endPeriodicFrame (n (φ i)) r (θ (φ i)) (a (φ i)))) atTop
          (𝓝 (limitingHeightFamily N (E₀, v) p)) := by
  obtain ⟨q, φ, hφ, hq⟩ := CompactSpace.tendsto_subseq (fun i => (θ i, a i))
  have hθ : Tendsto (fun i => θ (φ i)) atTop (𝓝 q.1) := continuous_fst.continuousAt.tendsto.comp hq
  have ha : Tendsto (fun i => a (φ i)) atTop (𝓝 q.2) := continuous_snd.continuousAt.tendsto.comp hq
  have hf := endPeriodicFrame_limit_moving (hn.comp hφ.tendsto_atTop) v
    (hP.comp hφ.tendsto_atTop) r hθ ha
  exact ⟨φ, hφ, _, translated_frame_height_limit N (hE.comp hφ.tendsto_atTop) hf (limitingFrame_det _ _)⟩

theorem bulk_height_cluster (N : PlaneNorm) {n j : ℕ → ℕ} (hjle : ∀ i, j i ≤ n i)
    (hj : Tendsto j atTop atTop) (hd : Tendsto (fun i => n i - j i) atTop atTop)
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    {E : ℕ → FiberParameter} {E₀ : FiberParameter} (hE : Tendsto E atTop (𝓝 E₀))
    (θ : ℕ → Real.Angle) (a : ℕ → FlightParameter) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : LimitingParameter,
      Tendsto (fun i => frameHeight N (blockFiber (E (φ i)).val *
        beginningPeriodicFrame (n (φ i)) (j (φ i)) (θ (φ i)) (a (φ i)))) atTop
          (𝓝 (limitingHeightFamily N (E₀, v) p)) := by
  obtain ⟨q, φ, hφ, hq⟩ := CompactSpace.tendsto_subseq (fun i => (θ i, a i, phase (j i)))
  have hθ : Tendsto (fun i => θ (φ i)) atTop (𝓝 q.1) := continuous_fst.continuousAt.tendsto.comp hq
  have ha : Tendsto (fun i => a (φ i)) atTop (𝓝 q.2.1) :=
    (continuous_fst.comp continuous_snd).continuousAt.tendsto.comp hq
  have hξ : Tendsto (fun i => phase (j (φ i))) atTop (𝓝 q.2.2) :=
    (continuous_snd.comp continuous_snd).continuousAt.tendsto.comp hq
  have hp := periodic_bulk_product_limit (fun i => hjle (φ i)) (hd.comp hφ.tendsto_atTop) hξ
  have hw := (periodic_bulk_word_limit hjle hj hd).comp hφ.tendsto_atTop
  have hc := ellipticCircle_tendsto (hP.comp hφ.tendsto_atTop) (ellipticTracePath_det v)
    (ellipticTracePath_elliptic v.property) hθ
  let p : LimitingParameter :=
    (⟨(constantWord, ellipticCircle constantMatrix q.2.2), bulk_mem_limitingSkeleton q.2.2⟩, (q.1, q.2.1))
  have hf : Tendsto (fun i => beginningPeriodicFrame (n (φ i)) (j (φ i)) (θ (φ i)) (a (φ i))) atTop
      (𝓝 (limitingFrame v p)) := flightChart_limit hw (hc.mul hp) ha
  exact ⟨φ, hφ, p, translated_frame_height_limit N (hE.comp hφ.tendsto_atTop) hf (limitingFrame_det _ _)⟩

/-- Every sequence of periodic representatives has a height subsequence in the limiting model. -/
theorem periodic_height_cluster (N : PlaneNorm) {n j : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    (hjle : ∀ i, j i ≤ n i) (hadm : ∀ᶠ i in atTop, Admissible (n i))
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    {E : ℕ → FiberParameter} {E₀ : FiberParameter} (hE : Tendsto E atTop (𝓝 E₀))
    (θ : ℕ → Real.Angle) (a : ℕ → FlightParameter) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ p : LimitingParameter,
      Tendsto (fun i => frameHeight N (blockFiber (E (φ i)).val *
        beginningPeriodicFrame (n (φ i)) (j (φ i)) (θ (φ i)) (a (φ i)))) atTop
          (𝓝 (limitingHeightFamily N (E₀, v) p)) := by
  rcases nat_sequence_constant_subseq_or_tendsto j with (⟨r, φ, hφ, hr⟩ | hj)
  · obtain ⟨ψ, hψ, p, hp⟩ := beginning_height_cluster N (hn.comp hφ.tendsto_atTop) v
      (hP.comp hφ.tendsto_atTop) (hE.comp hφ.tendsto_atTop) r (θ ∘ φ) (a ∘ φ)
    refine ⟨φ ∘ ψ, hφ.comp hψ, p, ?_⟩
    simpa only [Function.comp_def, hr] using hp
  rcases nat_sequence_constant_subseq_or_tendsto (fun i => n i - j i) with (⟨r, φ, hφ, hr⟩ | hd)
  · let θ' := fun i => θ (φ i) + (ellipticAngle (periodMatrix (n (φ i))) : Real.Angle)
    obtain ⟨ψ, hψ, p, hp⟩ := end_height_cluster N (hn.comp hφ.tendsto_atTop) v
      (hP.comp hφ.tendsto_atTop) (hE.comp hφ.tendsto_atTop) r θ' (a ∘ φ)
    refine ⟨φ ∘ ψ, hφ.comp hψ, p, hp.congr' ?_⟩
    filter_upwards [(hφ.tendsto_atTop.comp hψ.tendsto_atTop).eventually hadm] with i hi
    dsimp only [Function.comp_def, θ']
    have hpos := hjle (φ (ψ i))
    have he := hr (ψ i)
    have hlarge : r ≤ n (φ (ψ i)) := by omega
    have hj : j (φ (ψ i)) = n (φ (ψ i)) - r := by omega
    rw [hj, beginningPeriodicFrame_as_end _ _ hlarge hi]
  · exact bulk_height_cluster N hjle hj hd v hP hE θ a

end HallRay

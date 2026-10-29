module

public import HallRay.ShortBulkVectors

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

/-- The first lattice column becomes arbitrarily short, uniformly over bounded initial fibers. -/
theorem short_bulk_vectors_uniform (N : PlaneNorm) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ᶠ v : ℝ in 𝓝[Set.Ioo (-2) 2] 2, ∃ ξ : Real.Angle,
      ∀ E : Mat2, ‖E‖ ≤ B →
        ‖N.frameVector (blockFiber E * (flow t * codedChart constantWord
          (ellipticCircle (ellipticTracePath v) ((Real.pi / 2 : ℝ) : Real.Angle) *
            ellipticCircle constantMatrix ξ))) (1, (0, 0))‖ < ε := by
  let a := chartScale (futureCode constantWord) (pastCode constantWord)
  have ha : 0 < a := chartScale_pos _ _
  have hN := N.bound_nonneg
  have hexp : Tendsto (fun t : ℝ => a * Real.exp (-2 * t)) atTop (𝓝 0) := by
    have hm : Tendsto (fun t : ℝ => 2 * t) atTop atTop :=
      tendsto_id.const_mul_atTop (by norm_num)
    simpa only [mul_zero, neg_mul, Function.comp_def] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hm).const_mul a
  obtain ⟨t, ht, hsmall⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (hexp.eventually (gt_mem_nhds hε))).exists
  let C := a * Real.exp t * N.bound * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let δ := ε / (C + 1)
  have hden : 0 < C + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have hδeq : (C + 1) * δ = ε := by dsimp [δ]; exact mul_div_cancel₀ ε hden.ne'
  have hCδ : C * δ < ε := by nlinarith
  refine ⟨t, ht, ?_⟩
  filter_upwards [bulk_vector_arbitrary_contraction (unstableVector constantWord) hδ] with v hv
  obtain ⟨ξ, hξ⟩ := hv
  refine ⟨ξ, ?_⟩
  intro E hE
  let F := ellipticCircle (ellipticTracePath v) ((Real.pi / 2 : ℝ) : Real.Angle) *
    ellipticCircle constantMatrix ξ
  have hb := chart_first_vector_bound N constantWord E F t
  have hscale : (a * Real.exp t * N.bound * ‖E‖) *
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector constantWord)‖ ≤
      C * δ := by
    have hcoeff : a * Real.exp t * N.bound * ‖E‖ ≤ C :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    have hξ' : ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) F (unstableVector constantWord)‖ ≤ δ := hξ.le
    exact mul_le_mul hcoeff hξ' (norm_nonneg _) hC
  apply hb.trans_lt
  exact max_lt hsmall (hscale.trans_lt hCδ)

/-- Uniform escape of the limiting maxima over every norm-bounded set of initial fibers. -/
theorem limitingDepth_uniform_lower (N : PlaneNorm) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) :
    ∀ᶠ v : ℝ in 𝓝[Set.Ioo (-2) 2] 2, ∀ hv : v ∈ Set.Ioo (-2) 2,
      ∀ E : FiberParameter, ‖E.val‖ ≤ B →
        ENNReal.ofReal (M + 1) ≤ limitingDepth N (E, ⟨v, hv⟩) := by
  let ε := (M + 1)⁻¹
  have hMp : 0 < M + 1 := by linarith
  have hε : 0 < ε := inv_pos.mpr hMp
  obtain ⟨t, ht, hshort⟩ := short_bulk_vectors_uniform N hB hε
  filter_upwards [hshort] with v hvshort
  intro hv E hE
  obtain ⟨ξ, hξ⟩ := hvshort
  let A := blockFiber E.val * (flow t * codedChart constantWord
    (ellipticCircle (ellipticTracePath v) ((Real.pi / 2 : ℝ) : Real.Angle) *
      ellipticCircle constantMatrix ξ))
  have hsys : frameSystole N A ≤ ENNReal.ofReal ε := by
    apply (iInf_le (fun w : {w : ℤ × (ℤ × ℤ) // w ≠ 0} =>
      ENNReal.ofReal ‖N.frameVector A w.val‖) ⟨(1, (0, 0)), by simp⟩).trans
    exact ENNReal.ofReal_le_ofReal (hξ E.val hE).le
  have hlow : ENNReal.ofReal (M + 1) ≤ frameHeight N A := by
    have hi := ENNReal.inv_le_inv.mpr hsys
    rw [← ENNReal.ofReal_inv_of_pos hε] at hi
    simpa only [ε, inv_inv, frameHeight] using hi
  exact hlow.trans (bulk_flow_height_le_depth N E ⟨v, hv⟩ _ ξ ht)

/-- A harmless extension outside the elliptic trace interval, used only to state endpoint limits. -/
def depthFunction (N : PlaneNorm) (E : FiberParameter) (v : ℝ) : ℝ≥0∞ :=
  if hv : v ∈ Set.Ioo (-2) 2 then limitingDepth N (E, ⟨v, hv⟩) else 0

/-- The limiting maximum diverges at the parabolic endpoint. -/
theorem limitingDepth_tendsto_top (N : PlaneNorm) (E : FiberParameter) :
    Tendsto (depthFunction N E) (𝓝[Set.Ioo (-2) 2] 2) (𝓝 ⊤) := by
  apply ENNReal.tendsto_nhds_top_iff_nnreal.mpr
  intro x
  filter_upwards [self_mem_nhdsWithin,
    limitingDepth_uniform_lower N (norm_nonneg E.val) (NNReal.coe_nonneg x)] with v hv hlow
  have he : (x : ℝ≥0∞) < ENNReal.ofReal ((x : ℝ) + 1) := by
    have hh := (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < (x : ℝ) + 1)).mpr
      (show (x : ℝ) < (x : ℝ) + 1 by linarith)
    simpa only [ENNReal.ofReal_coe_nnreal] using hh
  rw [depthFunction, dite_eq_left hv]
  exact he.trans_le (hlow hv E le_rfl)

end HallRay

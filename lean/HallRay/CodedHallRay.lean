module

public import HallRay.FlightTimes

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

def codedOrbitHeight (N : PlaneNorm) (z : Word) : ℝ≥0∞ :=
  limsup (fun t : ℝ => frameHeight N (flow t * codedChart z 1)) atTop

theorem coded_flow_height_ne_top (N : PlaneNorm) (z : Word) (t : ℝ) :
    frameHeight N (flow t * codedChart z 1) ≠ ⊤ := by
  apply frameHeight_ne_top
  rw [Matrix.det_mul, flow_det, codedChart_det _ (by simp), one_mul]
  norm_num

/-- The summable concatenation has exactly the prescribed lattice-orbit height limsup. -/
theorem concatenation_height_limsup {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hcontrol : ∀ i, ρ i ≤ shadowTolerance N (2 * P.bound + 1) i) :
    codedOrbitHeight N (concatenationWord P hρ) = ENNReal.ofReal A := by
  let z := concatenationWord P hρ
  have hupper (I : ℕ) : codedOrbitHeight N z ≤ ENNReal.ofReal (A + 2 * stageError (I + 1)) := by
    apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop (timeSum z ((concatenationStages P hρ I).finish + 1))] with t ht
    obtain ⟨m, hm, a, heq⟩ := late_time_as_late_flight z (concatenationStages P hρ I).finish ht
    have hb := concatenation_late_flights_upper P hρ hcontrol I m hm a
    rw [heq, flightTime_height]
    have hfinite : frameHeight N (returnFlightFrame z 1 m a) ≠ ⊤ :=
      frameHeight_ne_top N _ (by rw [returnFlightFrame_det z (by simp) m a]; norm_num)
    rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hb
  have he₀ : Tendsto (fun i : ℕ => stageError (i + 1)) atTop (𝓝 0) :=
    stageError_tendsto.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun I : ℕ => ENNReal.ofReal (A + 2 * stageError (I + 1))) atTop
      (𝓝 (ENNReal.ofReal A)) := by
    have hr := (he₀.const_mul 2).const_add A
    simp only [mul_zero, add_zero] at hr
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr
  apply le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hupper))
  let m := fun i => (concatenationStages P hρ (i + 1)).start + (concatenationStages P hρ (i + 1)).witness
  let a := fun i => (concatenationStages P hρ (i + 1)).fraction
  let t := fun i => flightTime z (m i) (a i)
  have ht : Tendsto t atTop atTop := by
    have hr := (tendsto_natCast_atTop_atTop (R := ℝ)).comp
      (concatenation_finishes_strictMono P hρ).tendsto_atTop
    apply tendsto_atTop_mono (f := fun i => ((concatenationStages P hρ i).finish : ℝ)) ?_ hr
    intro i
    have hstart := (concatenationStages_extends P hρ i).1
    have hm : (concatenationStages P hρ i).finish ≤ m i := by dsimp [m]; rw [hstart]; omega
    exact (show ((concatenationStages P hρ i).finish : ℝ) ≤ (m i : ℝ) by exact_mod_cast hm).trans
      (flightTime_ge_index z (m i) (a i))
  have hreal : Tendsto (fun i => (frameHeight N (flow (t i) * codedChart z 1)).toReal) atTop (𝓝 A) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he : ∀ᶠ i in atTop, 3 * stageError (i + 1) < ε := by
      have hh := he₀.const_mul 3
      simp only [mul_zero] at hh
      exact hh.eventually (gt_mem_nhds hε)
    filter_upwards [he] with i hi
    rw [Real.dist_eq, flightTime_height]
    exact (concatenation_block_witness P hρ hcontrol i).trans hi
  have henn : Tendsto (fun i => frameHeight N (flow (t i) * codedChart z 1)) atTop (𝓝 (ENNReal.ofReal A)) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
    exact hh.congr (fun i => ENNReal.ofReal_toReal (coded_flow_height_ne_top N z (t i)))
  have hc : MapClusterPt (ENNReal.ofReal A) atTop (fun t : ℝ => frameHeight N (flow t * codedChart z 1)) :=
    MapClusterPt.of_comp ht henn.mapClusterPt
  exact hc.le_limsup

/-- A ray of exact height limsups is realized by the explicitly constructed symbolic charts. -/
theorem coded_hall_ray (N : PlaneNorm) :
    ∃ T : ℝ, 0 < T ∧ ∀ A : ℝ, T < A → ∃ z : Word, codedOrbitHeight N z = ENNReal.ofReal A := by
  obtain ⟨T, hT, hchoice⟩ := uniform_adjusted_periodic_choices N
  refine ⟨T, hT, ?_⟩
  intro A hA
  obtain ⟨δ, K, hδ, hδ1, hK, hselect⟩ := hchoice A hA
  let P : ConcatenationParameters N A := {
    radius := δ, bound := K, radius_pos := hδ, radius_lt_one := hδ1, bound_ge_one := hK, select := hselect }
  let ρ := shadowTolerance N (2 * P.bound + 1)
  have hρ : ∀ i, 0 < ρ i := shadowTolerance_pos N (2 * P.bound + 1)
  exact ⟨concatenationWord P hρ, concatenation_height_limsup P hρ (fun _ => le_rfl)⟩

end HallRay

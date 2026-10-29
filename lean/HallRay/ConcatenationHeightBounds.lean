module

public import HallRay.BlockShadowing

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

theorem stageError_antitone : Antitone stageError := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : i + 1 ≤ j + 1)

/-- Every late block stays below the prescribed height, up to its geometric error. -/
theorem concatenation_block_height_upper {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hcontrol : ∀ i, ρ i ≤ shadowTolerance N (2 * P.bound + 1) i) (i j : ℕ)
    (hj : j < (concatenationStages P hρ (i + 1)).repetitions * ((concatenationStages P hρ (i + 1)).n + 1))
    (a : FlightParameter) :
    (frameHeight N (returnFlightFrame (concatenationWord P hρ) 1
      ((concatenationStages P hρ (i + 1)).start + j) a)).toReal ≤ A + 2 * stageError (i + 1) := by
  let T := concatenationStages P hρ (i + 1)
  have hs := block_flight_shadowing P hρ hcontrol i j hj a
  have hp := periodic_returnFlight_height_le N T.n T.admissible T.input j a
  have hr := ENNReal.toReal_mono (periodicDepth_ne_top N T.n T.admissible T.input) hp
  have hd := T.depth_near
  have hh := (abs_lt.mp hs).2
  have hd' := (abs_lt.mp hd).2
  linarith

/-- One flight in each late block visits the target height, within three geometric errors. -/
theorem concatenation_block_witness {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hcontrol : ∀ i, ρ i ≤ shadowTolerance N (2 * P.bound + 1) i) (i : ℕ) :
    let T := concatenationStages P hρ (i + 1)
    |(frameHeight N (returnFlightFrame (concatenationWord P hρ) 1 (T.start + T.witness) T.fraction)).toReal - A| <
      3 * stageError (i + 1) := by
  let T := concatenationStages P hρ (i + 1)
  have hs := block_flight_shadowing P hρ hcontrol i T.witness T.witness_lt T.fraction
  have hv := T.visit_near
  have hd := T.depth_near
  apply abs_lt.mpr
  have hs' := abs_lt.mp hs
  have hv' := abs_lt.mp hv
  have hd' := abs_lt.mp hd
  constructor <;> linarith

/-- Every sufficiently late return index belongs to a later selected block. -/
theorem concatenation_return_in_block {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (I m : ℕ)
    (hm : (concatenationStages P hρ I).finish ≤ m) :
    ∃ i : ℕ, I ≤ i ∧ ∃ j : ℕ,
      j < (concatenationStages P hρ (i + 1)).repetitions * ((concatenationStages P hρ (i + 1)).n + 1) ∧
      m = (concatenationStages P hρ (i + 1)).start + j := by
  let r := fun i => (concatenationStages P hρ i).finish
  have hr := concatenation_finishes_strictMono P hρ
  change r I ≤ m at hm
  have hex : ∃ k : ℕ, m < r k := by
    exact ⟨m + 1, lt_of_lt_of_le (by omega) (hr.le_apply (x := m + 1))⟩
  let k := Nat.find hex
  have hk : m < r k := Nat.find_spec hex
  have hIk : I < k := by
    by_contra h
    have hh : r k ≤ r I := hr.monotone (Nat.le_of_not_gt h)
    omega
  have hk0 : 1 ≤ k := by omega
  have hprev : r (k - 1) ≤ m := by
    have hh := Nat.find_min hex (show k - 1 < k by omega)
    exact le_of_not_gt hh
  let i := k - 1
  have hki : k = i + 1 := by dsimp [i]; omega
  have hs := (concatenationStages_extends P hρ i).1
  have hstart : (concatenationStages P hρ (i + 1)).start ≤ m := by
    rw [hs]
    exact hprev
  refine ⟨i, by dsimp [i]; omega, m - (concatenationStages P hρ (i + 1)).start, ?_, by omega⟩
  rw [hki] at hk
  change m < (concatenationStages P hρ (i + 1)).start +
    (concatenationStages P hρ (i + 1)).repetitions * ((concatenationStages P hρ (i + 1)).n + 1) at hk
  omega

/-- A uniform bound for all flights after the end of block I. -/
theorem concatenation_late_flights_upper {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hcontrol : ∀ i, ρ i ≤ shadowTolerance N (2 * P.bound + 1) i) (I m : ℕ)
    (hm : (concatenationStages P hρ I).finish ≤ m) (a : FlightParameter) :
    (frameHeight N (returnFlightFrame (concatenationWord P hρ) 1 m a)).toReal ≤ A + 2 * stageError (I + 1) := by
  obtain ⟨i, hi, j, hj, heq⟩ := concatenation_return_in_block P hρ I m hm
  rw [heq]
  exact (concatenation_block_height_upper P hρ hcontrol i j hj a).trans
    (by have hh := stageError_antitone (by omega : I + 1 ≤ i + 1); linarith)

end HallRay

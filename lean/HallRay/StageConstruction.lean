module

public import HallRay.ConcatenationStages

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- Periodic selection can simultaneously satisfy the geometric overlap budget. -/
theorem choose_stage_period {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i M : ℕ) (E : FiberParameter)
    (hE : ‖E.val - 1‖ ≤ P.radius) :
    ∃ n : ℕ, M < n ∧ i + 1 ≤ n ∧ Admissible n ∧
      |(periodicDepth N n E).toReal - A| < stageError i ∧
      (∀ m : ℕ, ‖cocycle fiberMap (periodicWord n) m‖ ≤ P.bound ∧
        ‖(cocycle fiberMap (periodicWord n) m)⁻¹‖ ≤ P.bound) ∧
      (1 / 600 : ℝ) ^ n < overlapBudget P ρ i := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 600)
    (by norm_num : (1 / 600 : ℝ) < 1)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (hp.eventually (gt_mem_nhds (overlapBudget_pos P hρ i)))
  obtain ⟨n, hn, ha, hd, hb⟩ := P.select E hE (stageError i) (stageError_pos i) (max M (max i M₀))
  refine ⟨n, by omega, by omega, ha, hd, hb, hM₀ n (by omega)⟩

/-- The first block has no inherited prefix error. -/
theorem initial_concatenation_stage {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) :
    ∃ S : ConcatenationStage P ρ 0, S.start = 0 ∧ ∀ i : ℤ, i < 0 → S.word i = constantWord i := by
  have hI : ‖identityFiber.val - 1‖ ≤ P.radius := by
    change ‖(1 : Mat2) - 1‖ ≤ P.radius
    simpa only [sub_self, norm_zero] using P.radius_pos.le
  obtain ⟨n, _, hn, ha, hd, hb, hsmall⟩ := choose_stage_period P hρ 0 0 identityFiber hI
  obtain ⟨L, m, hL, hm, hret, a, hvisit⟩ := choose_periodic_repetition N n ha identityFiber
    (stageError_pos 0) (div_pos P.radius_pos (by norm_num : (0 : ℝ) < 2)) 1
  let z := spliceWord constantWord 0 (periodicWord n)
  have htail (m : ℕ) : shift (0 : ℤ) z (m : ℤ) = periodicWord n (m : ℤ) :=
    spliceWord_tail constantWord (periodicWord n) 0 m
  have hprod : cocycle fiberMap z (0 + L * (n + 1)) = periodMatrix n ^ L := by
    rw [spliceWord_period_product, cocycle_zero, one_mul]
  have hterm : ‖cocycle fiberMap z (0 + L * (n + 1)) - 1‖ ≤ P.radius * (1 - stageError 0) := by
    rw [hprod, stageError_zero]
    linarith
  let S : ConcatenationStage P ρ 0 := {
    n := n, repetitions := L, start := 0, word := z, input := identityFiber,
    n_large := hn, repetitions_large := hL, tail := htail, admissible := ha,
    partial_bound := hb, input_near := hI, depth_near := hd,
    witness := m, fraction := a, witness_lt := hm, visit_near := hvisit,
    terminal_near := hterm, overlap_small := hsmall }
  exact ⟨S, rfl, fun i hi => spliceWord_before _ _ _ hi⟩

/-- The data linking two successive finite stages. -/
def StageExtends {N : PlaneNorm} {A : ℝ} {P : ConcatenationParameters N A} {ρ : ℕ → ℝ} {i : ℕ}
    (S : ConcatenationStage P ρ i) (T : ConcatenationStage P ρ (i + 1)) : Prop :=
  T.start = S.finish ∧ S.n < T.n ∧ T.word = spliceWord S.word S.finish (periodicWord T.n) ∧
    T.input.val = S.fiber

/-- One induction step; the geometric reserve absorbs both sources of fiber drift. -/
theorem next_concatenation_stage {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) {i : ℕ} (S : ConcatenationStage P ρ i) :
    ∃ T : ConcatenationStage P ρ (i + 1), StageExtends S T := by
  obtain ⟨n, hnold, hn, ha, hd, hb, hsmall⟩ :=
    choose_stage_period P hρ (i + 1) S.n S.fiberParameter S.fiber_near
  let η := P.radius * stageError i / 8
  have hη : 0 < η := div_pos (mul_pos P.radius_pos (stageError_pos i)) (by norm_num)
  obtain ⟨L, m, hL, hm, hret, a, hvisit⟩ := choose_periodic_repetition N n ha S.fiberParameter
    (stageError_pos (i + 1)) hη (i + 2)
  let z := spliceWord S.word S.finish (periodicWord n)
  let F := cocycle fiberMap z (S.finish + L * (n + 1))
  let E := periodMatrix n ^ L
  have hEnorm : ‖E‖ < 2 := by
    have ht : ‖E‖ ≤ ‖E - 1‖ + 1 := by
      simpa only [sub_add_cancel, norm_one] using norm_add_le (E - 1) (1 : Mat2)
    have he := stageError_le_half i
    have hep := stageError_pos i
    have hδ := P.radius_lt_one
    have hδp := P.radius_pos
    dsimp [η] at hret
    change ‖E - 1‖ < P.radius * stageError i / 8 at hret
    nlinarith
  have hFprev := S.fiber_norm_lt_two
  have herror : ‖F - S.fiber * E‖ ≤ 4 * (1 / 600 : ℝ) ^ S.n := by
    have he := splice_fiber_increment S.word S.finish S.n n L hnold.le S.terminal_tail
    have hcoeff : ‖S.fiber‖ * ‖E‖ ≤ 4 := by nlinarith [norm_nonneg S.fiber, norm_nonneg E]
    exact he.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))
  have hq : (1 / 600 : ℝ) ^ S.n < P.radius * stageError i / 16 :=
    S.overlap_small.trans_le (min_le_left _ _)
  have htriangle : ‖F - 1‖ ≤ ‖F - S.fiber * E‖ + ‖S.fiber‖ * ‖E - 1‖ + ‖S.fiber - 1‖ := by
    have heq : F - 1 = (F - S.fiber * E) + S.fiber * (E - 1) + (S.fiber - 1) := by noncomm_ring
    rw [heq]
    exact (norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))) le_rfl)
  have hmove : ‖S.fiber‖ * ‖E - 1‖ ≤ 2 * η := by
    exact mul_le_mul hFprev.le hret.le (norm_nonneg _) (by norm_num)
  have hterm : ‖F - 1‖ ≤ P.radius * (1 - stageError (i + 1)) := by
    have hold := S.terminal_near
    change ‖S.fiber - 1‖ ≤ P.radius * (1 - stageError i) at hold
    rw [stageError_succ]
    dsimp [η] at hmove
    nlinarith
  let T : ConcatenationStage P ρ (i + 1) := {
    n := n, repetitions := L, start := S.finish, word := z, input := S.fiberParameter,
    n_large := hn, repetitions_large := hL, tail := spliceWord_tail S.word (periodicWord n) S.finish,
    admissible := ha, partial_bound := hb, input_near := S.fiber_near, depth_near := hd,
    witness := m, fraction := a, witness_lt := hm, visit_near := hvisit,
    terminal_near := hterm, overlap_small := hsmall }
  exact ⟨T, rfl, hnold, rfl, rfl⟩

end HallRay

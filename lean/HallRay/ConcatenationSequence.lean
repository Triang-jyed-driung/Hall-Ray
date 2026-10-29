module

public import HallRay.StageConstruction

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- The actual dependent sequence of finite blocks produced by the summable induction. -/
def concatenationStages {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) : (i : ℕ) → ConcatenationStage P ρ i
  | 0 => Classical.choose (initial_concatenation_stage P hρ)
  | i + 1 => Classical.choose (next_concatenation_stage P hρ (concatenationStages P hρ i))

theorem concatenationStages_extends {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i : ℕ) :
    StageExtends (concatenationStages P hρ i) (concatenationStages P hρ (i + 1)) :=
  Classical.choose_spec (next_concatenation_stage P hρ (concatenationStages P hρ i))

theorem concatenationStages_start_zero {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) : (concatenationStages P hρ 0).start = 0 :=
  (Classical.choose_spec (initial_concatenation_stage P hρ)).1

theorem concatenation_finishes_strictMono {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) : StrictMono (fun i => (concatenationStages P hρ i).finish) := by
  apply strictMono_nat_of_lt_succ
  intro i
  have hs := (concatenationStages_extends P hρ i).1
  have hL := (concatenationStages P hρ (i + 1)).repetitions_large
  have hp : 0 < (concatenationStages P hρ (i + 1)).repetitions *
      ((concatenationStages P hρ (i + 1)).n + 1) := Nat.mul_pos (by omega) (by omega)
  change (concatenationStages P hρ i).finish <
    (concatenationStages P hρ (i + 1)).start +
      (concatenationStages P hρ (i + 1)).repetitions * ((concatenationStages P hρ (i + 1)).n + 1)
  rw [hs]
  omega

theorem concatenation_lengths_strictMono {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) : StrictMono (fun i => (concatenationStages P hρ i).n) := by
  apply strictMono_nat_of_lt_succ
  intro i
  exact (concatenationStages_extends P hρ i).2.1

theorem concatenation_prefix_stable {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i : ℕ) (j : ℤ)
    (hj : j < ((concatenationStages P hρ i).finish : ℤ)) :
    (concatenationStages P hρ (i + 1)).word j = (concatenationStages P hρ i).word j := by
  rw [(concatenationStages_extends P hρ i).2.2.1]
  exact spliceWord_before _ _ _ hj

theorem concatenation_extra_stable {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i : ℕ) (j : ℤ)
    (hj : j < (((concatenationStages P hρ i).finish + (concatenationStages P hρ i).n : ℕ) : ℤ)) :
    (concatenationStages P hρ (i + 1)).word j = (concatenationStages P hρ i).word j := by
  let S := concatenationStages P hρ i
  let T := concatenationStages P hρ (i + 1)
  have he := concatenationStages_extends P hρ i
  change j < ((S.finish + S.n : ℕ) : ℤ) at hj
  by_cases hj0 : 0 ≤ j
  · have ha := spliceWord_periodic_agreement S.word S.finish S.n T.n he.2.1.le S.terminal_tail
      j.toNat (by omega)
    rw [Int.toNat_of_nonneg hj0] at ha
    rw [he.2.2.1]
    exact ha.symm
  · apply concatenation_prefix_stable P hρ i j
    have hr : (0 : ℤ) ≤ S.finish := Int.natCast_nonneg _
    omega

theorem concatenation_extra_growth {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i : ℕ) :
    (concatenationStages P hρ i).finish + (concatenationStages P hρ i).n ≤
      (concatenationStages P hρ (i + 1)).finish := by
  let T := concatenationStages P hρ (i + 1)
  have he := concatenationStages_extends P hρ i
  have hL : 1 ≤ T.repetitions := by have h := T.repetitions_large; omega
  have hp : T.n + 1 ≤ T.repetitions * (T.n + 1) := by nlinarith
  change _ ≤ T.start + T.repetitions * (T.n + 1)
  rw [he.1]
  have hn : (concatenationStages P hρ i).n < T.n := he.2.1
  omega

/-- The final bi-infinite word of the construction. -/
def concatenationWord {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) : Word :=
  prefixLimitWord (fun i => (concatenationStages P hρ i).word)

theorem concatenationWord_agreement {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i : ℕ) {j : ℤ}
    (hj : j < (((concatenationStages P hρ i).finish + (concatenationStages P hρ i).n : ℕ) : ℤ)) :
    concatenationWord P hρ j = (concatenationStages P hρ i).word j :=
  prefixLimitWord_extra_agreement (concatenation_finishes_strictMono P hρ)
    (concatenation_prefix_stable P hρ) (concatenation_extra_stable P hρ)
    (concatenation_extra_growth P hρ) i hj

theorem concatenationWord_negative {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) {j : ℤ} (hj : j < 0) : concatenationWord P hρ j = constantWord j := by
  have hnonneg : (0 : ℤ) ≤ (concatenationStages P hρ 0).finish + (concatenationStages P hρ 0).n := by positivity
  rw [concatenationWord_agreement P hρ 0 (hj.trans_le hnonneg)]
  exact (Classical.choose_spec (initial_concatenation_stage P hρ)).2 j hj

end HallRay

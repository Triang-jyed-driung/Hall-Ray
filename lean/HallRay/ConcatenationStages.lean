module

public import HallRay.FlightContinuity

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- The geometric accuracy used for successive blocks. -/
def stageError (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ (i + 1)

theorem stageError_pos (i : ℕ) : 0 < stageError i := by unfold stageError; positivity

theorem stageError_le_half (i : ℕ) : stageError i ≤ 1 / 2 := by
  rw [stageError, pow_succ]
  have h : (1 / 2 : ℝ) ^ i ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  linarith

@[simp] theorem stageError_zero : stageError 0 = 1 / 2 := by norm_num [stageError]

theorem stageError_succ (i : ℕ) : stageError (i + 1) = stageError i / 2 := by
  unfold stageError
  rw [pow_succ]
  ring

theorem stageError_tendsto : Tendsto stageError atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  unfold stageError
  simpa only [Function.comp_def] using hp.comp (tendsto_add_atTop_nat 1)

/-- Fixed constants and the periodic selection theorem used throughout one construction. -/
structure ConcatenationParameters (N : PlaneNorm) (A : ℝ) where
  radius : ℝ
  bound : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  bound_ge_one : 1 ≤ bound
  select : ∀ E : FiberParameter, ‖E.val - 1‖ ≤ radius → ∀ ε : ℝ, 0 < ε → ∀ M : ℕ,
    ∃ n : ℕ, M < n ∧ Admissible n ∧ |(periodicDepth N n E).toReal - A| < ε ∧
      ∀ m : ℕ, ‖cocycle fiberMap (periodicWord n) m‖ ≤ bound ∧
        ‖(cocycle fiberMap (periodicWord n) m)⁻¹‖ ≤ bound

/-- The overlap error must fit both the fiber reserve and the next shadowing tolerance. -/
def overlapBudget {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    (ρ : ℕ → ℝ) (i : ℕ) : ℝ :=
  min (P.radius * stageError i / 16) (ρ (i + 1) / (6 * P.bound + 3))

theorem overlapBudget_pos {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i : ℕ) : 0 < overlapBudget P ρ i := by
  apply lt_min
  · exact div_pos (mul_pos P.radius_pos (stageError_pos i)) (by norm_num)
  · exact div_pos (hρ _) (by have h := P.bound_ge_one; linarith)

/-- A single finite stage, including its periodic near-maximum witness and terminal fiber reserve. -/
structure ConcatenationStage {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    (ρ : ℕ → ℝ) (i : ℕ) where
  n : ℕ
  repetitions : ℕ
  start : ℕ
  word : Word
  input : FiberParameter
  n_large : i + 1 ≤ n
  repetitions_large : i + 1 ≤ repetitions
  tail : ∀ m : ℕ, shift (start : ℤ) word (m : ℤ) = periodicWord n (m : ℤ)
  admissible : Admissible n
  partial_bound : ∀ m : ℕ, ‖cocycle fiberMap (periodicWord n) m‖ ≤ P.bound ∧
    ‖(cocycle fiberMap (periodicWord n) m)⁻¹‖ ≤ P.bound
  input_near : ‖input.val - 1‖ ≤ P.radius
  depth_near : |(periodicDepth N n input).toReal - A| < stageError i
  witness : ℕ
  fraction : FlightParameter
  witness_lt : witness < repetitions * (n + 1)
  visit_near : |(frameHeight N (returnFlightFrame (periodicWord n) input.val witness fraction)).toReal -
    (periodicDepth N n input).toReal| < stageError i
  terminal_near : ‖cocycle fiberMap word (start + repetitions * (n + 1)) - 1‖ ≤
    P.radius * (1 - stageError i)
  overlap_small : (1 / 600 : ℝ) ^ n < overlapBudget P ρ i

namespace ConcatenationStage

def finish {N : PlaneNorm} {A : ℝ} {P : ConcatenationParameters N A} {ρ : ℕ → ℝ} {i : ℕ}
    (S : ConcatenationStage P ρ i) : ℕ := S.start + S.repetitions * (S.n + 1)

def fiber {N : PlaneNorm} {A : ℝ} {P : ConcatenationParameters N A} {ρ : ℕ → ℝ} {i : ℕ}
    (S : ConcatenationStage P ρ i) : Mat2 := cocycle fiberMap S.word S.finish

theorem fiber_det {N : PlaneNorm} {A : ℝ} {P : ConcatenationParameters N A} {ρ : ℕ → ℝ} {i : ℕ}
    (S : ConcatenationStage P ρ i) : S.fiber.det = 1 := fiberProduct_det _ _

def fiberParameter {N : PlaneNorm} {A : ℝ} {P : ConcatenationParameters N A} {ρ : ℕ → ℝ} {i : ℕ}
    (S : ConcatenationStage P ρ i) : FiberParameter := ⟨S.fiber, S.fiber_det⟩

theorem fiber_near {N : PlaneNorm} {A : ℝ} {P : ConcatenationParameters N A} {ρ : ℕ → ℝ} {i : ℕ}
    (S : ConcatenationStage P ρ i) : ‖S.fiber - 1‖ ≤ P.radius := by
  apply S.terminal_near.trans
  have hp := P.radius_pos
  have he := stageError_pos i
  nlinarith

theorem fiber_norm_lt_two {N : PlaneNorm} {A : ℝ} {P : ConcatenationParameters N A} {ρ : ℕ → ℝ} {i : ℕ}
    (S : ConcatenationStage P ρ i) : ‖S.fiber‖ < 2 := by
  have ht : ‖S.fiber‖ ≤ ‖S.fiber - 1‖ + 1 := by
    simpa only [sub_add_cancel, norm_one] using norm_add_le (S.fiber - 1) (1 : Mat2)
  have h := S.fiber_near
  have hp := P.radius_lt_one
  linarith

/-- Exact periodic future at the terminal return of a stage. -/
theorem terminal_tail {N : PlaneNorm} {A : ℝ} {P : ConcatenationParameters N A} {ρ : ℕ → ℝ} {i : ℕ}
    (S : ConcatenationStage P ρ i) (m : ℕ) :
    shift (S.finish : ℤ) S.word (m : ℤ) = periodicWord S.n (m : ℤ) := by
  have ht := S.tail (m + S.repetitions * (S.n + 1))
  have hp := congrArg (fun w : Word => w (m : ℤ))
    (shift_nat_mul_of_periodic (periodicWord_period S.n) S.repetitions)
  simpa only [shift, finish, Nat.cast_add, add_assoc, add_comm, add_left_comm] using ht.trans hp

end ConcatenationStage
end HallRay

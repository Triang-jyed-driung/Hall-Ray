module

public import HallRay.ConcatenationSequence

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- In the last n+1 positions of a period, only position -1 is a defect. -/
theorem periodicWord_negative (n d : ℕ) (hd : 1 ≤ d) (hdn : d ≤ n + 1) :
    periodicWord n (-(d : ℤ)) = if d = 1 then .b else .a := by
  have h0 : 0 ≤ -(d : ℤ) + ((n : ℤ) + 1) := by omega
  have h1 : -(d : ℤ) + ((n : ℤ) + 1) < (n : ℤ) + 1 := by omega
  have he : -(d : ℤ) % ((n : ℤ) + 1) = -(d : ℤ) + ((n : ℤ) + 1) := by
    have hh := Int.emod_eq_of_lt h0 h1
    simpa only [Int.add_emod_right] using hh
  by_cases hdone : d = 1
  · subst d
    have hrem : (-1 : ℤ) % ((n : ℤ) + 1) = (n : ℤ) := by
      simp only [Nat.cast_one] at he
      omega
    simp [periodicWord, hrem]
  · simp only [periodicWord, he, ite_eq_right hdone]
    rw [ite_eq_right (by omega)]

/-- A stage retains the last period before its terminal return. -/
theorem stage_past_at_finish {N : PlaneNorm} {A : ℝ} {P : ConcatenationParameters N A}
    {ρ : ℕ → ℝ} {i : ℕ} (S : ConcatenationStage P ρ i) (d : ℕ)
    (_hd : 1 ≤ d) (hdn : d ≤ S.n + 1) :
    S.word ((S.finish : ℤ) - d) = periodicWord S.n (-(d : ℤ)) := by
  have hL : 1 ≤ S.repetitions := by have h := S.repetitions_large; omega
  have hspan : S.n + 1 ≤ S.repetitions * (S.n + 1) := by nlinarith
  have hnonneg : 0 ≤ ((S.repetitions * (S.n + 1) : ℕ) : ℤ) - d := by omega
  have ht := S.tail (((S.repetitions * (S.n + 1) : ℕ) : ℤ) - d).toNat
  rw [Int.toNat_of_nonneg hnonneg] at ht
  have hp := congrArg (fun w : Word => w (-(d : ℤ)))
    (shift_nat_mul_of_periodic (periodicWord_period S.n) S.repetitions)
  have he : (S.start : ℤ) + (((S.repetitions * (S.n + 1) : ℕ) : ℤ) - d) = (S.finish : ℤ) - d := by
    simp only [ConcatenationStage.finish, Nat.cast_add]
    ring
  simp only [shift] at ht hp
  rw [add_comm _ (S.start : ℤ), he] at ht
  exact ht.trans (by simpa only [sub_eq_add_neg, add_comm] using hp)

/-- On every retained block and its extra a-run, the limiting word has the exact periodic symbols. -/
theorem concatenation_block_value {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i : ℕ) {j : ℤ}
    (hstart : ((concatenationStages P hρ i).start : ℤ) ≤ j)
    (hend : j < (((concatenationStages P hρ i).finish + (concatenationStages P hρ i).n : ℕ) : ℤ)) :
    concatenationWord P hρ j = periodicWord (concatenationStages P hρ i).n
      (j - (concatenationStages P hρ i).start) := by
  rw [concatenationWord_agreement P hρ i hend]
  have ht := (concatenationStages P hρ i).tail (j - (concatenationStages P hρ i).start).toNat
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hstart)] at ht
  simpa only [shift, sub_add_cancel] using ht

/-- Future agreement lasts for the remaining repeated block and the next a-run. -/
theorem concatenation_block_future {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i j m : ℕ)
    (hm : m + j < (concatenationStages P hρ i).repetitions *
      ((concatenationStages P hρ i).n + 1) + (concatenationStages P hρ i).n) :
    shift (((concatenationStages P hρ i).start + j : ℕ) : ℤ) (concatenationWord P hρ) (m : ℤ) =
      shift (j : ℤ) (periodicWord (concatenationStages P hρ i).n) (m : ℤ) := by
  unfold shift
  rw [concatenation_block_value P hρ i (by push_cast; omega) (by
    simp only [ConcatenationStage.finish, Nat.cast_add]
    omega)]
  congr 1
  push_cast
  ring

/-- At a block boundary, the actual past and the longer periodic past share the old a-run. -/
theorem concatenation_block_past {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i j d : ℕ)
    (hj : j < (concatenationStages P hρ (i + 1)).repetitions *
      ((concatenationStages P hρ (i + 1)).n + 1))
    (hd : 1 ≤ d) (hdn : d ≤ (concatenationStages P hρ i).n) :
    shift (((concatenationStages P hρ (i + 1)).start + j : ℕ) : ℤ)
      (concatenationWord P hρ) (-(d : ℤ)) =
      shift (j : ℤ) (periodicWord (concatenationStages P hρ (i + 1)).n) (-(d : ℤ)) := by
  let S := concatenationStages P hρ i
  let T := concatenationStages P hρ (i + 1)
  have he := concatenationStages_extends P hρ i
  have hstart : T.start = S.finish := he.1
  have hn : S.n < T.n := he.2.1
  change j < T.repetitions * (T.n + 1) at hj
  change d ≤ S.n at hdn
  change concatenationWord P hρ (-(d : ℤ) + ((T.start + j : ℕ) : ℤ)) =
    periodicWord T.n (-(d : ℤ) + j)
  by_cases hdj : d ≤ j
  · rw [concatenation_block_value P hρ (i + 1) (by
      change (T.start : ℤ) ≤ -(d : ℤ) + ((T.start + j : ℕ) : ℤ)
      push_cast
      omega) (by
      change -(d : ℤ) + ((T.start + j : ℕ) : ℤ) < ((T.finish + T.n : ℕ) : ℤ)
      simp only [ConcatenationStage.finish, Nat.cast_add]
      omega)]
    congr 1
    push_cast
    ring
  · have hdiff : 1 ≤ d - j := by omega
    have hdiffn : d - j ≤ S.n + 1 := by omega
    have hdiffT : d - j ≤ T.n + 1 := by omega
    have heq : -(d : ℤ) + ((T.start + j : ℕ) : ℤ) = (S.finish : ℤ) - (d - j : ℕ) := by
      rw [hstart, Nat.cast_add, Nat.cast_sub (by omega)]
      ring
    rw [heq, concatenationWord_agreement P hρ i (by
      change (S.finish : ℤ) - (d - j : ℕ) < ((S.finish + S.n : ℕ) : ℤ)
      have hnpos := S.n_large
      push_cast
      omega), stage_past_at_finish S (d - j) hdiff hdiffn,
      periodicWord_negative S.n (d - j) hdiff hdiffn]
    have harg : -(d : ℤ) + (j : ℤ) = -((d - j : ℕ) : ℤ) := by rw [Nat.cast_sub (by omega)]; ring
    rw [harg, periodicWord_negative T.n (d - j) hdiff hdiffT]

end HallRay

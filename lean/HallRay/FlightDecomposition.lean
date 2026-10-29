module

public import HallRay.PeriodicWords
public import Mathlib.Algebra.Order.Archimedean.Basic

@[expose] public section
noncomputable section
namespace HallRay

theorem timeSum_strictMono (z : Word) : StrictMono (timeSum z) := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [timeSum_succ]
  have h := roof_gt_one (shift (m : ℤ) z)
  linarith

/-- Every nonnegative time belongs to a flight following a symbolic return. -/
theorem flight_decomposition (z : Word) {t : ℝ} (ht : 0 ≤ t) :
    ∃ m : ℕ, ∃ r : ℝ, t = timeSum z m + r ∧ 0 ≤ r ∧ r ≤ roof (shift (m : ℤ) z) := by
  have hex : ∃ m : ℕ, t < timeSum z (m + 1) := by
    obtain ⟨m, hm⟩ := exists_nat_gt t
    have hm' : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
    exact ⟨m, hm.trans_le (hm'.trans (timeSum_ge z (m + 1)))⟩
  let m := Nat.find hex
  have hm : t < timeSum z (m + 1) := Nat.find_spec hex
  have hprev : timeSum z m ≤ t := by
    by_cases h0 : m = 0
    · simpa only [h0, timeSum_zero] using ht
    · have hh : ¬ t < timeSum z ((m - 1) + 1) := Nat.find_min hex (show m - 1 < m by omega)
      rw [Nat.sub_add_cancel (show 1 ≤ m by omega)] at hh
      exact le_of_not_gt hh
  refine ⟨m, t - timeSum z m, by ring, sub_nonneg.mpr hprev, ?_⟩
  rw [timeSum_succ] at hm
  linarith

/-- The flight index for a periodic code splits into complete periods and a bounded remainder. -/
theorem periodic_flight_decomposition (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ k : ℕ, ∃ j : Fin (n + 1), ∃ r : ℝ,
      t = (k : ℝ) * periodTime n + timeSum (periodicWord n) j.val + r ∧
      0 ≤ r ∧ r ≤ roof (shift (j.val : ℤ) (periodicWord n)) := by
  obtain ⟨m, r, heq, hr0, hr1⟩ := flight_decomposition (periodicWord n) ht
  let k := m / (n + 1)
  let j : Fin (n + 1) := ⟨m % (n + 1), Nat.mod_lt m (by omega)⟩
  have hm : m = k * (n + 1) + j.val := by
    simpa only [k, j, Nat.mul_comm] using (Nat.div_add_mod m (n + 1)).symm
  have hshift : shift (m : ℤ) (periodicWord n) = shift (j.val : ℤ) (periodicWord n) := by
    rw [hm, Nat.cast_add, add_comm, ← shift_add,
      shift_nat_mul_of_periodic (periodicWord_period n)]
  refine ⟨k, j, r, ?_, hr0, by simpa only [hshift] using hr1⟩
  rw [heq, hm, timeSum_periods_remainder (periodicWord_period n)]
  rfl

end HallRay

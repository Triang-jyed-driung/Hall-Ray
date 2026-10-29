module

public import HallRay.PhaseModel

@[expose] public section
noncomputable section
open Filter Topology
namespace HallRay

/-- In a fixed window around the beginning, the preceding defect is at -1. -/
theorem periodicWord_beginning_eventually (i : ℤ) :
    ∀ᶠ n : ℕ in atTop, periodicWord n i = (shift 1 defectWord) i := by
  filter_upwards [eventually_ge_atTop (i.natAbs + 1)] with n hn
  have hi : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
  have hni : -(i.natAbs : ℤ) ≤ i := by
    have h : -i ≤ ((-i).natAbs : ℤ) := Int.le_natAbs
    simpa using neg_le_neg h
  by_cases hpos : 0 ≤ i
  · have he := Int.emod_eq_of_lt hpos (show i < (n : ℤ) + 1 by omega)
    simp [periodicWord, he, shift, defectWord, show i ≠ (n : ℤ) by omega,
      show i + 1 ≠ 0 by omega]
  · have h0 : 0 ≤ i + ((n : ℤ) + 1) := by omega
    have h1 : i + ((n : ℤ) + 1) < (n : ℤ) + 1 := by omega
    have he : i % ((n : ℤ) + 1) = i + ((n : ℤ) + 1) := by
      have hh := Int.emod_eq_of_lt h0 h1
      simpa only [Int.add_emod_right] using hh
    by_cases hm : i = -1
    · subst i
      simp [periodicWord, he, shift, defectWord]
    · have hne : i + ((n : ℤ) + 1) ≠ (n : ℤ) := by omega
      simp only [periodicWord, he, ite_eq_right hne, shift, defectWord,
        ite_eq_right (show i + 1 ≠ 0 by omega)]

theorem periodicWord_beginning_limit :
    Tendsto periodicWord atTop (𝓝 (shift 1 defectWord)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact tendsto_const_nhds.congr' ((periodicWord_beginning_eventually i).mono (fun _ h => h.symm))

theorem periodicWord_fixed_position_limit (r : ℤ) :
    Tendsto (fun n => shift r (periodicWord n)) atTop (𝓝 (shift (r + 1) defectWord)) := by
  simpa only [shift_add, Function.comp_def] using
    (shift_continuous r).continuousAt.tendsto.comp periodicWord_beginning_limit

/-- Moving to the end of a period is exactly a fixed negative shift. -/
theorem periodicWord_end_shift (n r : ℕ) :
    shift ((n : ℤ) - r) (periodicWord n) = shift (-(r : ℤ) - 1) (periodicWord n) := by
  have h := congrArg (shift (-(r : ℤ) - 1)) (periodicWord_period n)
  simpa only [shift_add, Nat.cast_add, Nat.cast_one,
    show -(r : ℤ) - 1 + ((n : ℤ) + 1) = (n : ℤ) - r by ring] using h

theorem periodicWord_end_limit (r : ℕ) :
    Tendsto (fun n : ℕ => shift ((n : ℤ) - r) (periodicWord n)) atTop
      (𝓝 (shift (-(r : ℤ)) defectWord)) := by
  simpa only [periodicWord_end_shift, sub_add_cancel] using
    periodicWord_fixed_position_limit (-(r : ℤ) - 1)

/-- Any observation position far from both ends sees the constant code. -/
theorem periodicWord_bulk_limit {n j : ℕ → ℕ}
    (hj : Tendsto j atTop atTop) (hend : Tendsto (fun k => (n k : ℤ) - j k) atTop atTop) :
    Tendsto (fun k => shift (j k : ℤ) (periodicWord (n k))) atTop (𝓝 constantWord) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have he : ∀ᶠ k : ℕ in atTop,
      shift (j k : ℤ) (periodicWord (n k)) i = constantWord i := by
    filter_upwards [hj.eventually (eventually_ge_atTop (i.natAbs + 1)),
      hend.eventually (eventually_ge_atTop ((i.natAbs : ℤ) + 1))] with k hk hl
    have hi : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
    have hni : -(i.natAbs : ℤ) ≤ i := by
      have h : -i ≤ ((-i).natAbs : ℤ) := Int.le_natAbs
      simpa using neg_le_neg h
    have h0 : 0 ≤ i + (j k : ℤ) := by omega
    have h1 : i + (j k : ℤ) < (n k : ℤ) := by omega
    have hm := Int.emod_eq_of_lt h0 (show i + (j k : ℤ) < (n k : ℤ) + 1 by omega)
    simp [shift, periodicWord, hm, constantWord, show i + (j k : ℤ) ≠ (n k : ℤ) by omega]
  exact tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm))

end HallRay

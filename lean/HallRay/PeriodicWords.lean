module

public import HallRay.Lattices
public import HallRay.FiberProducts

@[expose] public section
noncomputable section
namespace HallRay

/-- The word (a^n b)^infinity with a defect at positions n modulo n+1. -/
def periodicWord (n : ℕ) : Word := fun i => if i % ((n : ℤ) + 1) = (n : ℤ) then .b else .a

def defectWord : Word := fun i => if i = 0 then .b else .a

theorem periodicWord_period (n : ℕ) : shift ((n + 1 : ℕ) : ℤ) (periodicWord n) = periodicWord n := by
  funext i
  simp [shift, periodicWord]

theorem periodicWord_a {n j : ℕ} (hj : j < n) : periodicWord n (j : ℤ) = .a := by
  have hj' : (j : ℤ) < ((n + 1 : ℕ) : ℤ) := by omega
  have he := Int.emod_eq_of_lt (Int.natCast_nonneg j) hj'
  simp only [Nat.cast_add, Nat.cast_one] at he
  simp only [periodicWord, he]
  rw [ite_eq_right (by omega)]

theorem periodicWord_b (n : ℕ) : periodicWord n (n : ℤ) = .b := by
  have he := Int.emod_eq_of_lt (Int.natCast_nonneg n)
    (show (n : ℤ) < ((n + 1 : ℕ) : ℤ) by omega)
  simp [periodicWord]

theorem shift_nat_mul_of_periodic {z : Word} {p : ℕ} (hp : shift (p : ℤ) z = z) (k : ℕ) :
    shift ((k * p : ℕ) : ℤ) z = z := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul, Nat.cast_add, ← shift_add, hp, ih]

theorem timeSum_periods {z : Word} {p : ℕ} (hp : shift (p : ℤ) z = z) (k : ℕ) :
    timeSum z (k * p) = (k : ℝ) * timeSum z p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, timeSum_add, shift_nat_mul_of_periodic hp, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem timeSum_periods_remainder {z : Word} {p : ℕ} (hp : shift (p : ℤ) z = z) (k j : ℕ) :
    timeSum z (k * p + j) = (k : ℝ) * timeSum z p + timeSum z j := by
  rw [timeSum_add, shift_nat_mul_of_periodic hp, timeSum_periods hp]

def periodMatrix (n : ℕ) : Mat2 := cocycle fiberMap (periodicWord n) (n + 1)

def periodTime (n : ℕ) : ℝ := timeSum (periodicWord n) (n + 1)

theorem periodMatrix_det (n : ℕ) : (periodMatrix n).det = 1 := fiberProduct_det _ _

theorem periodTime_pos (n : ℕ) : 0 < periodTime n := by
  have h := timeSum_ge (periodicWord n) (n + 1)
  change ((n + 1 : ℕ) : ℝ) ≤ periodTime n at h
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) h

/-- The forward-time part of Proposition `prop:complete-orbit`.
It holds for every remainder j, hence in particular for 0 ≤ j ≤ n. -/
theorem periodic_complete_orbit (n k j : ℕ) (E : Mat2) (r : ℝ) :
    frameLattice (flow ((k : ℝ) * periodTime n + timeSum (periodicWord n) j + r) *
      codedChart (periodicWord n) E) =
    frameLattice (flow r * codedChart (shift (j : ℤ) (periodicWord n))
      (E * periodMatrix n ^ k * cocycle fiberMap (periodicWord n) j)) := by
  have h := symbolic_lattice_factor (periodicWord n) E (k * (n + 1) + j) r
  have hshift : shift ((k * (n + 1) + j : ℕ) : ℤ) (periodicWord n) =
      shift (j : ℤ) (periodicWord n) := by
    rw [Nat.cast_add, add_comm, ← shift_add, shift_nat_mul_of_periodic (periodicWord_period n)]
  rw [timeSum_periods_remainder (periodicWord_period n),
    cocycle_periods_remainder _ _ _ (periodicWord_period n), hshift] at h
  simpa only [periodTime, periodMatrix, Matrix.mul_assoc] using h

/-- The periodic word and the shifted single-defect word agree for 2n+1 symbols. -/
theorem periodic_defect_agreement (n : ℕ) :
    ∀ i : ℕ, i < 2 * n + 1 → periodicWord n (i : ℤ) = (shift (-(n : ℤ)) defectWord) (i : ℤ) := by
  intro i hi
  by_cases hip : i < n + 1
  · have he := Int.emod_eq_of_lt (Int.natCast_nonneg i)
      (show (i : ℤ) < (n : ℤ) + 1 by omega)
    by_cases hin : i = n
    · subst i
      simp [periodicWord_b, shift, defectWord]
    · have hinZ : (i : ℤ) ≠ (n : ℤ) := by omega
      simp [periodicWord, he, shift, defectWord, hinZ, show (i : ℤ) + -(n : ℤ) ≠ 0 by omega]
  · have hi0 : 0 ≤ (i : ℤ) - ((n : ℤ) + 1) := by omega
    have hi1 : (i : ℤ) - ((n : ℤ) + 1) < (n : ℤ) + 1 := by omega
    have he : (i : ℤ) % ((n : ℤ) + 1) = (i : ℤ) - ((n : ℤ) + 1) := by
      have he' := Int.emod_eq_of_lt hi0 hi1
      rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod] at he'
      exact he'
    simp only [periodicWord, he, shift, defectWord]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]

end HallRay

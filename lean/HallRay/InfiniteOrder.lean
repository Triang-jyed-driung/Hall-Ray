module

public import HallRay.MonodromyObstruction
public import HallRay.PeriodicWords

@[expose] public section
noncomputable section
namespace HallRay

/-- Every positive-time periodic code has an infinite-order fiber return.
This proves the arithmetic obstruction used for the irrational elliptic angles,
without introducing splitting fields or Galois groups. -/
theorem periodic_fiber_infinite_order {z : Word} {p : ℕ} (hp0 : 0 < p)
    (hp : shift (p : ℤ) z = z) {k : ℕ} (hk : 0 < k) :
    cocycle fiberMap z p ^ k ≠ 1 := by
  intro hfinite
  let t := timeSum z (k * p)
  let C := codedChart z 1
  let Γ := cocycle integerMarking z (k * p)
  have ht : 0 < t := by
    have h := timeSum_ge z (k * p)
    exact lt_of_lt_of_le (by exact_mod_cast Nat.mul_pos hk hp0) h
  have hC : C.det = 1 := codedChart_det z (by simp)
  have hΓ : Γ.det = 1 := integerMarkingProduct_det z (k * p)
  have hCleft : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C (by rw [hC]; exact isUnit_one)
  have hCright : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (by rw [hC]; exact isUnit_one)
  have hmat : flow t * C * Γ.map (Int.castRingHom ℝ) = C := by
    have h := symbolic_iterated_return z 1 (k * p)
    rw [shift_nat_mul_of_periodic hp, cocycle_periods fiberMap z p hp k, hfinite,
      one_mul, markingProduct_map] at h
    exact h
  have hflow : flow (-t) * flow t = 1 := by rw [← flow_add]; simp [flow_zero]
  have hconj : C * Γ.map (Int.castRingHom ℝ) * C⁻¹ = flow (-t) := by
    calc
      _ = flow (-t) * (flow t * C * Γ.map (Int.castRingHom ℝ)) * C⁻¹ := by
        simp only [← Matrix.mul_assoc, hflow, one_mul]
      _ = flow (-t) * C * C⁻¹ := by rw [hmat]
      _ = _ := by rw [Matrix.mul_assoc, hCright, mul_one]
  have hdiag : flow (-t) = Matrix.diagonal ![Real.exp (2 * t), Real.exp (-t), Real.exp (-t)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [flow]
  rw [hdiag] at hconj
  exact no_contracting_scalar_monodromy Γ hΓ C hC (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr (by linarith)) hconj

theorem periodMatrix_infinite_order (n : ℕ) {k : ℕ} (hk : 0 < k) : periodMatrix n ^ k ≠ 1 :=
  periodic_fiber_infinite_order (Nat.succ_pos n) (periodicWord_period n) hk

theorem constantFiber_infinite_order {k : ℕ} (hk : 0 < k) : fiberMap constantWord ^ k ≠ 1 := by
  have h := periodic_fiber_infinite_order (z := constantWord) (p := 1)
    (by omega) constantWord_shift hk
  simpa [cocycle_succ] using h

end HallRay

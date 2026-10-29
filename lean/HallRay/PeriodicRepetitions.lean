module

public import HallRay.FiberAlgebra

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

def returnFlightFrame (z : Word) (Q : Mat2) (m : ℕ) (a : FlightParameter) : Mat3 :=
  flightChart a (shift (m : ℤ) z, Q * cocycle fiberMap z m)

theorem periodic_returnFlight_representative (n : ℕ) (h : Admissible n) (E : Mat2) (m : ℕ)
    (a : FlightParameter) :
    ∃ A ∈ periodicFrames n, returnFlightFrame (periodicWord n) E m a = blockFiber E * A := by
  let k := m / (n + 1)
  let j : Fin (n + 1) := ⟨m % (n + 1), Nat.mod_lt m (by omega)⟩
  have hm : m = k * (n + 1) + j.val := by
    simpa only [k, j, Nat.mul_comm] using (Nat.div_add_mod m (n + 1)).symm
  let p : Real.Angle × FlightParameter := (k • (ellipticAngle (periodMatrix n) : Real.Angle), a)
  refine ⟨periodicFrame n j p, Set.mem_iUnion.mpr ⟨j, ⟨p, rfl⟩⟩, ?_⟩
  have hshift : shift (m : ℤ) (periodicWord n) = shift (j.val : ℤ) (periodicWord n) := by
    rw [hm, Nat.cast_add, add_comm, ← shift_add,
      shift_nat_mul_of_periodic (periodicWord_period n)]
  unfold returnFlightFrame
  rw [hshift, hm, cocycle_periods_remainder _ _ _ (periodicWord_period n)]
  change flightChart a (shift (j.val : ℤ) (periodicWord n),
    E * (periodMatrix n ^ k * cocycle fiberMap (periodicWord n) j.val)) = _
  rw [← flightChart_left]
  congr 1
  simp only [periodicFrame, p, ellipticCircle_phase (periodMatrix_det n) h, flightChart]

theorem periodic_returnFlight_height_le (N : PlaneNorm) (n : ℕ) (h : Admissible n)
    (E : FiberParameter) (m : ℕ) (a : FlightParameter) :
    frameHeight N (returnFlightFrame (periodicWord n) E.val m a) ≤ periodicDepth N n E := by
  obtain ⟨A, hA, heq⟩ := periodic_returnFlight_representative n h E.val m a
  rw [heq]
  exact le_periodicDepth N n E hA

theorem ellipticCircle_zero {A : Mat2} (hA : A.det = 1) (hell : Elliptic A) : ellipticCircle A 0 = 1 := by
  rw [ellipticCircle, angleRotation_zero, mul_one]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (ellipticConjugator_det hA hell))

/-- Near-identity full-period multipliers occur beyond every prescribed repetition count. -/
theorem periodic_near_identity_late (n : ℕ) (h : Admissible n) {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∃ L : ℕ, M ≤ L ∧ ‖periodMatrix n ^ L - 1‖ < ε := by
  obtain ⟨k, hk, hpow⟩ := (elliptic_power_cluster (periodMatrix_det n) h
    (periodic_angle_irrational n h) 0).tendsto_subseq
  rw [ellipticCircle_zero (periodMatrix_det n) h] at hpow
  have hc : ∀ᶠ i in atTop, ‖periodMatrix n ^ k i - 1‖ < ε := by
    simpa only [dist_eq_norm, Function.comp_def] using Metric.tendsto_nhds.mp hpow ε hε
  obtain ⟨i, hi, he⟩ := ((hk.tendsto_atTop.eventually (eventually_ge_atTop M)).and hc).exists
  exact ⟨k i, hi, he⟩

/-- A finite collection of flights already visits within ε of the periodic maximum. -/
theorem periodic_flight_near_maximum (N : PlaneNorm) (n : ℕ) (h : Admissible n)
    (E : FiberParameter) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∃ a : FlightParameter,
      |(frameHeight N (returnFlightFrame (periodicWord n) E.val m a)).toReal -
        (periodicDepth N n E).toReal| < ε := by
  obtain ⟨A, hA, hmax⟩ := periodicDepth_attained N n h E
  obtain ⟨j, p, rfl⟩ := Set.mem_iUnion.mp hA
  obtain ⟨k, hk, hpow⟩ := (elliptic_power_cluster (periodMatrix_det n) h
    (periodic_angle_irrational n h) p.1).tendsto_subseq
  let z := shift (j.val : ℤ) (periodicWord n)
  let C := cocycle fiberMap (periodicWord n) j.val
  have hc : Continuous (fun Q : Mat2 => flightChart (p.2 : ℝ) (z, Q * C)) :=
    Continuous.comp (g := flightChart (p.2 : ℝ)) (f := fun Q : Mat2 => (z, Q * C))
      (flightChart_continuous _) (continuous_const.prodMk (continuous_id.mul_const C))
  have hf : Tendsto (fun i => flightChart (p.2 : ℝ) (z, periodMatrix n ^ k i * C)) atTop
      (𝓝 (periodicFrame n j p)) := hc.continuousAt.tendsto.comp hpow
  have hh := translated_frame_height_limit N (tendsto_const_nhds (x := E)) hf (periodicFrame_det n h j p)
  have hreal := (ENNReal.continuousAt_toReal (by rw [← hmax]; exact periodicDepth_ne_top N n h E)).tendsto.comp hh
  rw [← hmax] at hreal
  have hclose := Metric.tendsto_nhds.mp hreal ε hε
  obtain ⟨i, hi⟩ := hclose.exists
  refine ⟨k i * (n + 1) + j.val, p.2, ?_⟩
  have hshift : shift ((k i * (n + 1) + j.val : ℕ) : ℤ) (periodicWord n) = z := by
    rw [Nat.cast_add, add_comm, ← shift_add,
      shift_nat_mul_of_periodic (periodicWord_period n)]
  unfold returnFlightFrame
  rw [hshift, cocycle_periods_remainder _ _ _ (periodicWord_period n), ← flightChart_left]
  exact hi

/-- A sufficiently long repetition both visits the maximum and returns its fiber near identity. -/
theorem choose_periodic_repetition (N : PlaneNorm) (n : ℕ) (h : Admissible n)
    (E : FiberParameter) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) (M : ℕ) :
    ∃ L m : ℕ, M ≤ L ∧ m < L * (n + 1) ∧ ‖periodMatrix n ^ L - 1‖ < η ∧
      ∃ a : FlightParameter, |(frameHeight N (returnFlightFrame (periodicWord n) E.val m a)).toReal -
        (periodicDepth N n E).toReal| < ε := by
  obtain ⟨m, a, ha⟩ := periodic_flight_near_maximum N n h E hε
  obtain ⟨L, hL, hclose⟩ := periodic_near_identity_late n h hη (max M (m + 1))
  refine ⟨L, m, (le_max_left _ _).trans hL, ?_, hclose, a, ha⟩
  have hm : m < L := lt_of_lt_of_le (by omega) ((le_max_right _ _).trans hL)
  nlinarith

end HallRay

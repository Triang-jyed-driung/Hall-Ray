module

public import HallRay.ConcatenationHeightBounds

@[expose] public section
noncomputable section
open Filter Topology
namespace HallRay

def flightTime (z : Word) (m : ℕ) (a : FlightParameter) : ℝ :=
  timeSum z m + (a : ℝ) * roof (shift (m : ℤ) z)

theorem returnFlightFrame_det (z : Word) {Q : Mat2} (hQ : Q.det = 1) (m : ℕ) (a : FlightParameter) :
    (returnFlightFrame z Q m a).det = 1 := by
  apply flightChart_det
  rw [Matrix.det_mul, hQ, fiberProduct_det, one_mul]

theorem flightTime_ge_index (z : Word) (m : ℕ) (a : FlightParameter) : (m : ℝ) ≤ flightTime z m a := by
  have htime := timeSum_ge z m
  have hroof := roof_gt_one (shift (m : ℤ) z)
  have ha := a.property.1
  have hm : 0 ≤ (a : ℝ) * roof (shift (m : ℤ) z) := mul_nonneg ha (by linarith)
  unfold flightTime
  linarith

/-- Symbolic flight heights agree with heights along the original lattice orbit. -/
theorem flightTime_height (N : PlaneNorm) (z : Word) (m : ℕ) (a : FlightParameter) :
    frameHeight N (flow (flightTime z m a) * codedChart z 1) =
      frameHeight N (returnFlightFrame z 1 m a) := by
  apply frameHeight_of_lattice_eq
  · rw [Matrix.det_mul, flow_det, codedChart_det _ (by simp), one_mul]
    norm_num
  · rw [returnFlightFrame_det z (by simp) m a]
    norm_num
  · exact symbolic_lattice_factor z 1 m ((a : ℝ) * roof (shift (m : ℤ) z))

/-- Real time is covered exactly by the return-flight parametrization. -/
theorem time_as_flight (z : Word) {t : ℝ} (ht : 0 ≤ t) :
    ∃ m : ℕ, ∃ a : FlightParameter, t = flightTime z m a := by
  obtain ⟨m, r, heq, hr0, hr1⟩ := flight_decomposition z ht
  have hroof : 0 < roof (shift (m : ℤ) z) := lt_trans (by norm_num) (roof_gt_one _)
  let a : FlightParameter := ⟨r / roof (shift (m : ℤ) z),
    ⟨div_nonneg hr0 hroof.le, (div_le_one hroof).mpr hr1⟩⟩
  exact ⟨m, a, by simpa only [flightTime, a, div_mul_cancel₀ r hroof.ne'] using heq⟩

/-- A sufficiently late real time belongs to a sufficiently late symbolic flight. -/
theorem late_time_as_late_flight (z : Word) (M : ℕ) {t : ℝ} (ht : timeSum z (M + 1) ≤ t) :
    ∃ m : ℕ, M ≤ m ∧ ∃ a : FlightParameter, t = flightTime z m a := by
  have ht0 : 0 ≤ t := ((Nat.cast_nonneg (M + 1)).trans (timeSum_ge z (M + 1))).trans ht
  obtain ⟨m, a, heq⟩ := time_as_flight z ht0
  refine ⟨m, ?_, a, heq⟩
  by_contra hm
  have hmM : m + 1 ≤ M := by omega
  have horder := (timeSum_strictMono z).monotone hmM
  have hstrict := (timeSum_strictMono z) (Nat.lt_succ_self M)
  have hroof : 0 ≤ roof (shift (m : ℤ) z) := by have h := roof_gt_one (shift (m : ℤ) z); linarith
  have hfrac := mul_le_mul_of_nonneg_right a.property.2 hroof
  have hflight : flightTime z m a ≤ timeSum z (m + 1) := by
    rw [flightTime, timeSum_succ]
    linarith
  rw [heq] at ht
  linarith

end HallRay

module

public import HallRay.PeriodicDepth

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

def beginningPeriodicFrame (n r : ℕ) (θ : Real.Angle) (a : FlightParameter) : Mat3 :=
  flightChart a (shift (r : ℤ) (periodicWord n),
    ellipticCircle (periodMatrix n) θ * cocycle fiberMap (periodicWord n) r)

def endPeriodicFrame (n r : ℕ) (θ : Real.Angle) (a : FlightParameter) : Mat3 :=
  flightChart a (shift ((n - r : ℕ) : ℤ) (periodicWord n),
    ellipticCircle (periodMatrix n) θ *
      (cocycle fiberMap (shift ((n - r : ℕ) : ℤ) (periodicWord n)) (r + 1))⁻¹)

theorem beginningPeriodicFrame_mem (n r : ℕ) (hr : r ≤ n) (θ : Real.Angle) (a : FlightParameter) :
    beginningPeriodicFrame n r θ a ∈ periodicFrames n := by
  exact Set.mem_iUnion.mpr ⟨⟨r, by omega⟩, ⟨(θ, a), rfl⟩⟩

/-- Absorbing the full period into the circle changes a prefix into an inverse suffix. -/
theorem periodic_circle_suffix (n r : ℕ) (hr : r ≤ n) (h : Admissible n) (θ : Real.Angle) :
    ellipticCircle (periodMatrix n) θ *
      (cocycle fiberMap (shift ((n - r : ℕ) : ℤ) (periodicWord n)) (r + 1))⁻¹ =
    ellipticCircle (periodMatrix n) (θ - (ellipticAngle (periodMatrix n) : Real.Angle)) *
      cocycle fiberMap (periodicWord n) (n - r) := by
  let S := cocycle fiberMap (shift ((n - r : ℕ) : ℤ) (periodicWord n)) (r + 1)
  have hperiod : cocycle fiberMap (periodicWord n) (n - r) * S = periodMatrix n := by
    rw [← cocycle_add, show n - r + (r + 1) = n + 1 by omega]
    rfl
  have hInv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by
    rw [fiberProduct_det]; exact isUnit_one)
  have hcircle : ellipticCircle (periodMatrix n)
      (θ - (ellipticAngle (periodMatrix n) : Real.Angle)) * periodMatrix n =
      ellipticCircle (periodMatrix n) θ := by
    have hh := ellipticCircle_phase (periodMatrix_det n) h 1
    simp only [one_nsmul, pow_one] at hh
    calc
      _ = ellipticCircle (periodMatrix n) (θ - (ellipticAngle (periodMatrix n) : Real.Angle)) *
          ellipticCircle (periodMatrix n) (ellipticAngle (periodMatrix n) : Real.Angle) :=
        congrArg (fun Q => ellipticCircle (periodMatrix n)
          (θ - (ellipticAngle (periodMatrix n) : Real.Angle)) * Q) hh.symm
      _ = _ := by rw [ellipticCircle_mul (periodMatrix_det n) h, sub_add_cancel]
  change ellipticCircle (periodMatrix n) θ * S⁻¹ = _
  rw [← hcircle, ← hperiod]
  simp only [Matrix.mul_assoc, hInv, mul_one]

theorem endPeriodicFrame_mem (n r : ℕ) (hr : r ≤ n) (h : Admissible n)
    (θ : Real.Angle) (a : FlightParameter) : endPeriodicFrame n r θ a ∈ periodicFrames n := by
  unfold endPeriodicFrame
  rw [periodic_circle_suffix n r hr h θ]
  exact Set.mem_iUnion.mpr ⟨⟨n - r, by omega⟩,
    ⟨(θ - (ellipticAngle (periodMatrix n) : Real.Angle), a), rfl⟩⟩

theorem beginningPeriodicFrame_as_end (n r : ℕ) (hr : r ≤ n) (h : Admissible n)
    (θ : Real.Angle) (a : FlightParameter) :
    beginningPeriodicFrame n (n - r) θ a =
      endPeriodicFrame n r (θ + (ellipticAngle (periodMatrix n) : Real.Angle)) a := by
  unfold beginningPeriodicFrame endPeriodicFrame
  rw [periodic_circle_suffix n r hr h, add_sub_cancel_right]

theorem beginningPeriodicFrame_limit {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    (r : ℕ) (θ : Real.Angle) (a : FlightParameter) :
    Tendsto (fun i => beginningPeriodicFrame (n i) r θ a) atTop
      (𝓝 (limitingFrame v (⟨beginningSkeleton r, subset_closure (Or.inl ⟨r, rfl⟩)⟩, (θ, a)))) := by
  have hw := (periodicWord_fixed_position_limit (r : ℤ)).comp hn
  have hprod := (beginning_fiber_limit r).comp hn
  have hconst : cocycle fiberMap (shift 1 defectWord) r = constantMatrix ^ r := by
    simpa only [Nat.cast_zero, zero_add] using defect_beginning_product 0 r
  rw [hconst] at hprod
  have hc := ellipticCircle_tendsto hP (ellipticTracePath_det v)
    (ellipticTracePath_elliptic v.property) (tendsto_const_nhds (x := θ))
  have hh := (flightChart_continuous (a : ℝ)).continuousAt.tendsto.comp
    (hw.prodMk_nhds (hc.mul hprod))
  simpa only [beginningPeriodicFrame, limitingFrame, beginningSkeleton, flightChart,
    defect_beginning_product, Nat.cast_zero, zero_add, Function.comp_def] using hh

theorem endPeriodicFrame_limit {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    (r : ℕ) (θ : Real.Angle) (a : FlightParameter) :
    Tendsto (fun i => endPeriodicFrame (n i) r θ a) atTop
      (𝓝 (limitingFrame v (⟨endSkeleton r, subset_closure (Or.inr ⟨r, rfl⟩)⟩, (θ, a)))) := by
  have hlarge : ∀ᶠ i in atTop, r ≤ n i := hn.eventually (eventually_ge_atTop r)
  have hword := (periodicWord_end_limit r).comp hn
  have hsuffix := (end_suffix_limit r).comp hn
  have hcast : ∀ᶠ i in atTop, ((n i - r : ℕ) : ℤ) = (n i : ℤ) - r := by
    filter_upwards [hlarge] with i hi
    exact Nat.cast_sub hi
  have hw : Tendsto (fun i => shift ((n i - r : ℕ) : ℤ) (periodicWord (n i))) atTop
      (𝓝 (shift (-(r : ℤ)) defectWord)) := hword.congr' (hcast.mono (fun i hi => by dsimp only [Function.comp_def]; rw [hi]))
  have hs : Tendsto (fun i => cocycle fiberMap
      (shift ((n i - r : ℕ) : ℤ) (periodicWord (n i))) (r + 1)) atTop
      (𝓝 (cocycle fiberMap (shift (-(r : ℤ)) defectWord) (r + 1))) :=
    hsuffix.congr' (hcast.mono (fun i hi => by dsimp only [Function.comp_def]; rw [hi]))
  have hinv := continuousAt_matrix_inv
    (cocycle fiberMap (shift (-(r : ℤ)) defectWord) (r + 1)) (by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (by rw [fiberProduct_det]; norm_num))
  have hc := ellipticCircle_tendsto hP (ellipticTracePath_det v)
    (ellipticTracePath_elliptic v.property) (tendsto_const_nhds (x := θ))
  have hh := (flightChart_continuous (a : ℝ)).continuousAt.tendsto.comp
    (hw.prodMk_nhds (hc.mul (hinv.tendsto.comp hs)))
  simpa only [endPeriodicFrame, limitingFrame, endSkeleton, flightChart, Function.comp_def] using hh

end HallRay

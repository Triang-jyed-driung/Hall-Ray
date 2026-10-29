module

public import HallRay.PositionSubsequences

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

theorem flightChart_limit {z : ℕ → Word} {z₀ : Word} {F : ℕ → Mat2} {F₀ : Mat2}
    (hz : Tendsto z atTop (𝓝 z₀)) (hF : Tendsto F atTop (𝓝 F₀))
    {a : ℕ → FlightParameter} {a₀ : FlightParameter} (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun i => flightChart (a i) (z i, F i)) atTop (𝓝 (flightChart a₀ (z₀, F₀))) := by
  have har : Tendsto (fun i => (a i : ℝ)) atTop (𝓝 (a₀ : ℝ)) :=
    Tendsto.comp (g := fun a : FlightParameter => (a : ℝ)) (f := a)
      continuous_subtype_val.continuousAt.tendsto ha
  exact Tendsto.comp (g := fun q : ℝ × (Word × Mat2) => flightChart q.1 q.2)
    (f := fun i => ((a i : ℝ), (z i, F i))) (flightChart_joint_continuous.continuousAt (x := ((a₀ : ℝ), (z₀, F₀)))).tendsto
    (har.prodMk_nhds (hz.prodMk_nhds hF))

theorem beginningPeriodicFrame_limit_moving {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    (r : ℕ) {θ : ℕ → Real.Angle} {θ₀ : Real.Angle} (hθ : Tendsto θ atTop (𝓝 θ₀))
    {a : ℕ → FlightParameter} {a₀ : FlightParameter} (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun i => beginningPeriodicFrame (n i) r (θ i) (a i)) atTop
      (𝓝 (limitingFrame v (⟨beginningSkeleton r, subset_closure (Or.inl ⟨r, rfl⟩)⟩, (θ₀, a₀)))) := by
  have hw := (periodicWord_fixed_position_limit (r : ℤ)).comp hn
  have hp := (beginning_fiber_limit r).comp hn
  have hconst : cocycle fiberMap (shift 1 defectWord) r = constantMatrix ^ r := by
    simpa only [Nat.cast_zero, zero_add] using defect_beginning_product 0 r
  rw [hconst] at hp
  have hc := ellipticCircle_tendsto hP (ellipticTracePath_det v) (ellipticTracePath_elliptic v.property) hθ
  simpa only [beginningPeriodicFrame, limitingFrame, beginningSkeleton, flightChart,
    Function.comp_def] using flightChart_limit hw (hc.mul hp) ha

theorem periodic_end_word_limit_nat {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (r : ℕ) :
    Tendsto (fun i => shift ((n i - r : ℕ) : ℤ) (periodicWord (n i))) atTop
      (𝓝 (shift (-(r : ℤ)) defectWord)) := by
  have hword := (periodicWord_end_limit r).comp hn
  apply hword.congr'
  filter_upwards [hn.eventually (eventually_ge_atTop r)] with i hi
  dsimp only [Function.comp_def]
  rw [Nat.cast_sub hi]

theorem periodic_end_inverse_limit {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (r : ℕ) :
    Tendsto (fun i => (cocycle fiberMap (shift ((n i - r : ℕ) : ℤ) (periodicWord (n i))) (r + 1))⁻¹)
      atTop (𝓝 (endSkeleton r).2) := by
  have hs := (fiberProduct_continuous (r + 1)).continuousAt.tendsto.comp (periodic_end_word_limit_nat hn r)
  have hinv := continuousAt_matrix_inv
    (cocycle fiberMap (shift (-(r : ℤ)) defectWord) (r + 1)) (by
      rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ (by rw [fiberProduct_det]; norm_num))
  exact hinv.tendsto.comp hs

theorem endPeriodicFrame_limit_moving {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    (r : ℕ) {θ : ℕ → Real.Angle} {θ₀ : Real.Angle} (hθ : Tendsto θ atTop (𝓝 θ₀))
    {a : ℕ → FlightParameter} {a₀ : FlightParameter} (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto (fun i => endPeriodicFrame (n i) r (θ i) (a i)) atTop
      (𝓝 (limitingFrame v (⟨endSkeleton r, subset_closure (Or.inr ⟨r, rfl⟩)⟩, (θ₀, a₀)))) := by
  have hc := ellipticCircle_tendsto hP (ellipticTracePath_det v) (ellipticTracePath_elliptic v.property) hθ
  simpa only [endPeriodicFrame, limitingFrame, endSkeleton, flightChart] using
    flightChart_limit (periodic_end_word_limit_nat hn r) (hc.mul (periodic_end_inverse_limit hn r)) ha

end HallRay

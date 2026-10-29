module

public import HallRay.BoundaryFrames

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

/-- Left translation by converging initial fibers preserves a frame height limit. -/
theorem translated_frame_height_limit (N : PlaneNorm) {E : ℕ → FiberParameter} {E₀ : FiberParameter}
    (hE : Tendsto E atTop (𝓝 E₀)) {A : ℕ → Mat3} {L : Mat3}
    (hA : Tendsto A atTop (𝓝 L)) (hL : L.det = 1) :
    Tendsto (fun i => frameHeight N (blockFiber (E i).val * A i)) atTop
      (𝓝 (frameHeight N (blockFiber E₀.val * L))) := by
  have he := (blockFiber_continuous.comp continuous_subtype_val).continuousAt.tendsto.comp hE
  have hdet : (blockFiber E₀.val * L).det = 1 := by
    rw [Matrix.det_mul, blockFiber_det, E₀.property, hL, one_mul]
  exact (frameHeight_continuousAt N _ (by rw [hdet]; norm_num)).tendsto.comp (he.mul hA)

/-- A raw skeleton point, before restricting to the compact closure. -/
def skeletonFrame (v : TraceParameter) (θ : Real.Angle) (a : FlightParameter) (s : Word × Mat2) : Mat3 :=
  flightChart a (s.1, ellipticCircle (ellipticTracePath v) θ * s.2)

@[fun_prop] theorem skeletonFrame_continuous (v : TraceParameter) (θ : Real.Angle) (a : FlightParameter) :
    Continuous (skeletonFrame v θ a) := by
  exact Continuous.comp (g := flightChart (a : ℝ))
    (f := fun s : Word × Mat2 => (s.1, ellipticCircle (ellipticTracePath v) θ * s.2))
    (flightChart_continuous _) (continuous_fst.prodMk (continuous_const.mul continuous_snd))

theorem skeletonFrame_det (v : TraceParameter) (θ : Real.Angle) (a : FlightParameter)
    {s : Word × Mat2} (hs : s.2.det = 1) : (skeletonFrame v θ a s).det = 1 := by
  apply flightChart_det
  rw [Matrix.det_mul, ellipticCircle_det (ellipticTracePath_det v)
    (ellipticTracePath_elliptic v.property), hs, one_mul]

theorem skeleton_height_continuousAt (N : PlaneNorm) (E : FiberParameter)
    (v : TraceParameter) (θ : Real.Angle) (a : FlightParameter) {s : Word × Mat2} (hs : s.2.det = 1) :
    ContinuousAt (fun q => frameHeight N (blockFiber E.val * skeletonFrame v θ a q)) s := by
  have hm : Continuous (fun q => blockFiber E.val * skeletonFrame v θ a q) :=
    continuous_const.mul (skeletonFrame_continuous v θ a)
  have hdet : (blockFiber E.val * skeletonFrame v θ a s).det = 1 := by
    rw [Matrix.det_mul, blockFiber_det, E.property, skeletonFrame_det v θ a hs, one_mul]
  exact (frameHeight_continuousAt N _ (by rw [hdet]; norm_num)).comp hm.continuousAt

/-- Fixed beginning and end positions give the lower bound for convergence of periodic maxima. -/
theorem limitingDepth_le_periodic_liminf (N : PlaneNorm) {n : ℕ → ℕ}
    (hn : Tendsto n atTop atTop) (hadm : ∀ᶠ i in atTop, Admissible (n i))
    (v : TraceParameter) (hP : Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (ellipticTracePath v)))
    {E : ℕ → FiberParameter} {E₀ : FiberParameter} (hE : Tendsto E atTop (𝓝 E₀)) :
    limitingDepth N (E₀, v) ≤ liminf (fun i => periodicDepth N (n i) (E i)) atTop := by
  let L := liminf (fun i => periodicDepth N (n i) (E i)) atTop
  have hsource (θ : Real.Angle) (a : FlightParameter) :
      ∀ s ∈ Set.range beginningSkeleton ∪ Set.range endSkeleton,
        frameHeight N (blockFiber E₀.val * skeletonFrame v θ a s) ≤ L := by
    rintro s (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · have hf := beginningPeriodicFrame_limit hn v hP r θ a
      have hh := translated_frame_height_limit N hE hf (limitingFrame_det _ _)
      have hle : ∀ᶠ i in atTop, frameHeight N (blockFiber (E i).val * beginningPeriodicFrame (n i) r θ a) ≤
          periodicDepth N (n i) (E i) := by
        filter_upwards [hn.eventually (eventually_ge_atTop r)] with i hi
        exact le_periodicDepth N (n i) (E i) (beginningPeriodicFrame_mem (n i) r hi θ a)
      have hl := liminf_le_liminf hle
      rw [hh.liminf_eq] at hl
      exact hl
    · have hf := endPeriodicFrame_limit hn v hP r θ a
      have hh := translated_frame_height_limit N hE hf (limitingFrame_det _ _)
      have hle : ∀ᶠ i in atTop, frameHeight N (blockFiber (E i).val * endPeriodicFrame (n i) r θ a) ≤
          periodicDepth N (n i) (E i) := by
        filter_upwards [hn.eventually (eventually_ge_atTop r), hadm] with i hi ha
        exact le_periodicDepth N (n i) (E i) (endPeriodicFrame_mem (n i) r hi ha θ a)
      have hl := liminf_le_liminf hle
      rw [hh.liminf_eq] at hl
      exact hl
  apply sSup_le
  rintro _ ⟨p, rfl⟩
  have hc := skeleton_height_continuousAt N E₀ v p.2.1 p.2.2 (limitingSkeleton_det p.1.property)
  exact ContinuousWithinAt.closure_le p.1.property hc.continuousWithinAt
    continuousWithinAt_const (hsource p.2.1 p.2.2)

end HallRay

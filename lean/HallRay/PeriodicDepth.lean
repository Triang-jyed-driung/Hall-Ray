module

public import HallRay.LimitingRay

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

/-- Periodic maximum after applying the specified initial fiber. -/
def periodicDepth (N : PlaneNorm) (n : ℕ) (E : FiberParameter) : ℝ≥0∞ :=
  sSup ((fun A => frameHeight N (blockFiber E.val * A)) '' periodicFrames n)

theorem le_periodicDepth (N : PlaneNorm) (n : ℕ) (E : FiberParameter) {A : Mat3}
    (hA : A ∈ periodicFrames n) : frameHeight N (blockFiber E.val * A) ≤ periodicDepth N n E :=
  le_sSup ⟨A, hA, rfl⟩

theorem periodicDepth_attained (N : PlaneNorm) (n : ℕ) (h : Admissible n) (E : FiberParameter) :
    ∃ A ∈ periodicFrames n, periodicDepth N n E = frameHeight N (blockFiber E.val * A) := by
  apply (periodicFrames_compact n).exists_sSup_image_eq (periodicFrames_nonempty n)
  intro A hA
  have hdet : (blockFiber E.val * A).det = 1 := by
    rw [Matrix.det_mul, blockFiber_det, E.property, periodicFrames_det n h hA, one_mul]
  have hm : Continuous (fun X : Mat3 => blockFiber E.val * X) := continuous_const.mul continuous_id
  exact (ContinuousAt.comp (f := fun X : Mat3 => blockFiber E.val * X) (g := frameHeight N)
    (frameHeight_continuousAt N _ (by rw [hdet]; norm_num)) hm.continuousAt).continuousWithinAt

theorem periodicDepth_ne_top (N : PlaneNorm) (n : ℕ) (h : Admissible n) (E : FiberParameter) :
    periodicDepth N n E ≠ ⊤ := by
  obtain ⟨A, hA, heq⟩ := periodicDepth_attained N n h E
  rw [heq]
  apply frameHeight_ne_top
  rw [Matrix.det_mul, blockFiber_det, E.property, periodicFrames_det n h hA, one_mul]
  norm_num

/-- A return chart at a fixed fraction of its roof time. -/
def flightChart (a : ℝ) (p : Word × Mat2) : Mat3 :=
  flow (a * roof p.1) * codedChart p.1 p.2

@[fun_prop] theorem flightChart_continuous (a : ℝ) : Continuous (flightChart a) := by
  exact (flow_continuous.comp ((roof_continuous.comp continuous_fst).const_mul a)).mul
    codedChart_continuous

@[fun_prop] theorem flightChart_joint_continuous :
    Continuous (fun p : ℝ × (Word × Mat2) => flightChart p.1 p.2) := by
  have hz : Continuous (fun p : ℝ × (Word × Mat2) => p.2.1) := by fun_prop
  have hm : Continuous (fun p : ℝ × (Word × Mat2) => codedChart p.2.1 p.2.2) :=
    codedChart_continuous.comp continuous_snd
  exact (flow_continuous.comp (continuous_fst.mul (roof_continuous.comp hz))).mul hm

theorem flightChart_det (a : ℝ) (p : Word × Mat2) (hp : p.2.det = 1) : (flightChart a p).det = 1 := by
  rw [flightChart, Matrix.det_mul, flow_det, codedChart_det _ hp, one_mul]

/-- A moving elliptic return and angle have the expected limiting circle element. -/
theorem ellipticCircle_tendsto {A : ℕ → Mat2} {L : Mat2} (hA : Tendsto A atTop (𝓝 L))
    (hdet : L.det = 1) (hell : Elliptic L) {θ : ℕ → Real.Angle} {φ : Real.Angle}
    (hθ : Tendsto θ atTop (𝓝 φ)) :
    Tendsto (fun i => ellipticCircle (A i) (θ i)) atTop (𝓝 (ellipticCircle L φ)) := by
  exact Tendsto.comp (f := fun i => (A i, θ i))
    (g := fun p : Mat2 × Real.Angle => ellipticCircle p.1 p.2)
    (ellipticCircle_joint_continuousAt hdet hell φ).tendsto (hA.prodMk_nhds hθ)

end HallRay

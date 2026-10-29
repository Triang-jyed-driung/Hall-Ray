module

public import HallRay.PeriodicEstimates
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.Group.SubmonoidClosure

@[expose] public section
noncomputable section
open Filter Topology
namespace HallRay

instance : CompactSpace Real.Angle := by
  change CompactSpace (AddCircle (2 * Real.pi))
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  infer_instance

def angleRotation (θ : Real.Angle) : Mat2 := !![θ.cos, -θ.sin; θ.sin, θ.cos]

@[simp] theorem angleRotation_coe (θ : ℝ) : angleRotation (θ : Real.Angle) = rotation θ := by
  simp [angleRotation, rotation]

@[fun_prop] theorem angleRotation_continuous : Continuous angleRotation := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [angleRotation] using Real.Angle.continuous_cos
  · change Continuous (fun θ : Real.Angle => -θ.sin)
    exact Real.Angle.continuous_sin.neg
  · simpa [angleRotation] using Real.Angle.continuous_sin
  · simpa [angleRotation] using Real.Angle.continuous_cos

theorem angleRotation_det (θ : Real.Angle) : (angleRotation θ).det = 1 := by
  induction θ using Real.Angle.induction_on
  rw [angleRotation_coe, rotation_det]

def phase (n : ℕ) : Real.Angle := n • (constantAngle : Real.Angle)

theorem phase_coe (n : ℕ) : phase n = ((n : ℝ) * constantAngle : ℝ) := by
  simp only [phase, ← Real.Angle.coe_nsmul, nsmul_eq_mul]

theorem constant_phase_irrational : Irrational (constantAngle / (2 * Real.pi)) := by
  have h := constant_angle_irrational.div_ratCast (q := 2) (by norm_num)
  convert h using 1
  norm_num
  ring

theorem phase_zsmul_dense : DenseRange (fun n : ℤ => n • (constantAngle : Real.Angle)) :=
  AddCircle.denseRange_zsmul_coe_iff.mpr constant_phase_irrational

theorem phase_dense : DenseRange phase := denseRange_zsmul_iff_nsmul.mp phase_zsmul_dense

theorem phase_cluster (θ : Real.Angle) : MapClusterPt θ atTop phase := by
  change MapClusterPt θ atTop (fun n : ℕ => n • (constantAngle : Real.Angle))
  rw [mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples]
  change θ ∈ closure (Set.range (fun n : ℤ => n • (constantAngle : Real.Angle)))
  rw [phase_zsmul_dense.closure_range]
  trivial

theorem phase_approximating_sequence (θ : Real.Angle) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => phase (n i)) atTop (𝓝 θ) :=
  (phase_cluster θ).tendsto_subseq

/-- The limiting period matrix at a prescribed rotation phase. -/
def limitMatrix (θ : Real.Angle) : Mat2 :=
  constantConjugator * angleRotation θ * rotationDefect * constantConjugator⁻¹

theorem limitMatrix_continuous : Continuous limitMatrix := by
  unfold limitMatrix
  fun_prop

theorem limitMatrix_det (θ : Real.Angle) : (limitMatrix θ).det = 1 := by
  have hG := constantConjugator_det_ne_zero
  simp [limitMatrix, Matrix.det_mul, Matrix.det_nonsing_inv, angleRotation_det,
    rotationDefect_det, Ring.inverse_eq_inv, mul_inv_cancel₀ hG]

theorem constant_power_defect_model (n : ℕ) :
    constantMatrix ^ n * defectMatrix = limitMatrix (phase n) := by
  have hGr : constantConjugator * constantConjugator⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr constantConjugator_det_ne_zero)
  rw [conjugate_rotation_pow constantConjugator_det_ne_zero constantMatrix_conjugate,
    limitMatrix, phase_coe, angleRotation_coe, rotationDefect]
  simp only [Matrix.mul_assoc, hGr, mul_one]

theorem period_model_error_tendsto :
    Tendsto (fun n : ℕ => periodMatrix n - limitMatrix (phase n)) atTop (𝓝 0) := by
  simpa only [← constant_power_defect_model] using period_asymptotic_tendsto

/-- Phase convergence determines the asymptotic period matrix. -/
theorem period_phase_limit {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) {θ : Real.Angle}
    (hθ : Tendsto (fun i => phase (n i)) atTop (𝓝 θ)) :
    Tendsto (fun i => periodMatrix (n i)) atTop (𝓝 (limitMatrix θ)) := by
  have he := period_model_error_tendsto.comp hn
  have hm := (limitMatrix_continuous.tendsto θ).comp hθ
  have hs := he.add hm
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hs

def Admissible (n : ℕ) : Prop := Elliptic (periodMatrix n)

theorem elliptic_isOpen : IsOpen {A : Mat2 | Elliptic A} := by
  have hcont : Continuous (fun A : Mat2 => |A 0 0 + A 1 1|) := by fun_prop
  exact isOpen_Iio.preimage hcont

theorem eventually_admissible_of_phase_limit {n : ℕ → ℕ} (hn : Tendsto n atTop atTop)
    {θ : Real.Angle} (hθ : Tendsto (fun i => phase (n i)) atTop (𝓝 θ))
    (hell : Elliptic (limitMatrix θ)) : ∀ᶠ i in atTop, Admissible (n i) :=
  (period_phase_limit hn hθ).eventually (elliptic_isOpen.mem_nhds hell)

theorem admissible_approximating_sequence (θ : Real.Angle) (hell : Elliptic (limitMatrix θ)) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ Tendsto (fun i => phase (n i)) atTop (𝓝 θ) ∧
      ∀ᶠ i in atTop, Admissible (n i) := by
  obtain ⟨n, hn, hθ⟩ := phase_approximating_sequence θ
  exact ⟨n, hn, hθ, eventually_admissible_of_phase_limit hn.tendsto_atTop hθ hell⟩

end HallRay

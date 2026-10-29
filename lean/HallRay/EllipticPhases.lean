module

public import HallRay.CircularFibers
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

@[expose] public section
noncomputable section
namespace HallRay

def traceSum (B : Mat2) : ℝ := B 0 0 + B 1 1

def traceSkew (B : Mat2) : ℝ := B 0 1 - B 1 0

def traceAmplitudeSq (B : Mat2) : ℝ := traceSum B ^ 2 + traceSkew B ^ 2

/-- A unit complex phase at which the rotated matrix has a prescribed trace. -/
def tracePhaseComplex (B : Mat2) (v : ℝ) : ℂ :=
  ⟨(traceSum B * v - traceSkew B * Real.sqrt (traceAmplitudeSq B - v ^ 2)) / traceAmplitudeSq B,
   (traceSkew B * v + traceSum B * Real.sqrt (traceAmplitudeSq B - v ^ 2)) / traceAmplitudeSq B⟩

def tracePhase (B : Mat2) (v : ℝ) : Real.Angle := (Complex.arg (tracePhaseComplex B v) : Real.Angle)

theorem tracePhaseComplex_normSq {B : Mat2} (hB : 4 < traceAmplitudeSq B) {v : ℝ}
    (hv : v ∈ Set.Icc (-2) 2) : Complex.normSq (tracePhaseComplex B v) = 1 := by
  have hrad : 0 ≤ traceAmplitudeSq B - v ^ 2 := by nlinarith [hv.1, hv.2]
  have hs := Real.sq_sqrt hrad
  have hden : traceAmplitudeSq B ≠ 0 := by linarith
  simp only [Complex.normSq_apply, tracePhaseComplex]
  rw [← pow_two, ← pow_two, div_pow, div_pow, ← add_div]
  have hnum :
      (traceSum B * v - traceSkew B * Real.sqrt (traceAmplitudeSq B - v ^ 2)) ^ 2 +
        (traceSkew B * v + traceSum B * Real.sqrt (traceAmplitudeSq B - v ^ 2)) ^ 2 =
        traceAmplitudeSq B ^ 2 := by
    calc
      _ = traceAmplitudeSq B * (v ^ 2 + Real.sqrt (traceAmplitudeSq B - v ^ 2) ^ 2) := by
        dsimp [traceAmplitudeSq]
        ring
      _ = traceAmplitudeSq B * traceAmplitudeSq B := by rw [hs]; congr 1; ring
      _ = _ := by ring
  rw [hnum, div_self (pow_ne_zero 2 hden)]

theorem tracePhaseComplex_norm {B : Mat2} (hB : 4 < traceAmplitudeSq B) {v : ℝ}
    (hv : v ∈ Set.Icc (-2) 2) : ‖tracePhaseComplex B v‖ = 1 := by
  have hs := tracePhaseComplex_normSq hB hv
  rw [Complex.normSq_eq_norm_sq] at hs
  have hn := norm_nonneg (tracePhaseComplex B v)
  nlinarith

theorem tracePhaseComplex_ne_zero {B : Mat2} (hB : 4 < traceAmplitudeSq B) {v : ℝ}
    (hv : v ∈ Set.Icc (-2) 2) : tracePhaseComplex B v ≠ 0 := by
  intro he
  have hn := tracePhaseComplex_norm hB hv
  rw [he, norm_zero] at hn
  norm_num at hn

theorem tracePhase_cos {B : Mat2} (hB : 4 < traceAmplitudeSq B) {v : ℝ}
    (hv : v ∈ Set.Icc (-2) 2) : (tracePhase B v).cos = (tracePhaseComplex B v).re := by
  change Real.cos (Complex.arg (tracePhaseComplex B v)) = _
  rw [Complex.cos_arg (tracePhaseComplex_ne_zero hB hv), tracePhaseComplex_norm hB hv, div_one]

theorem tracePhase_sin {B : Mat2} (hB : 4 < traceAmplitudeSq B) {v : ℝ}
    (hv : v ∈ Set.Icc (-2) 2) : (tracePhase B v).sin = (tracePhaseComplex B v).im := by
  change Real.sin (Complex.arg (tracePhaseComplex B v)) = _
  rw [Complex.sin_arg, tracePhaseComplex_norm hB hv, div_one]

theorem rotated_trace (B : Mat2) (θ : Real.Angle) :
    (angleRotation θ * B).trace = traceSum B * θ.cos + traceSkew B * θ.sin := by
  simp [Matrix.trace_fin_two, angleRotation, traceSum, traceSkew, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  ring

theorem tracePhase_trace {B : Mat2} (hB : 4 < traceAmplitudeSq B) {v : ℝ}
    (hv : v ∈ Set.Icc (-2) 2) : (angleRotation (tracePhase B v) * B).trace = v := by
  rw [rotated_trace, tracePhase_cos hB hv, tracePhase_sin hB hv]
  dsimp [tracePhaseComplex]
  have hden : traceAmplitudeSq B ≠ 0 := by linarith
  field_simp
  dsimp [traceAmplitudeSq]
  ring

theorem tracePhaseComplex_continuous (B : Mat2) : Continuous (tracePhaseComplex B) := by
  let f : ℝ → ℝ := fun v =>
    (traceSum B * v - traceSkew B * Real.sqrt (traceAmplitudeSq B - v ^ 2)) / traceAmplitudeSq B
  let g : ℝ → ℝ := fun v =>
    (traceSkew B * v + traceSum B * Real.sqrt (traceAmplitudeSq B - v ^ 2)) / traceAmplitudeSq B
  have he : tracePhaseComplex B = fun v => (f v : ℂ) + (g v : ℂ) * Complex.I := by
    funext v
    apply Complex.ext <;> simp [tracePhaseComplex, f, g]
  rw [he]
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hg : Continuous g := by dsimp [g]; fun_prop
  exact (Complex.continuous_ofReal.comp hf).add ((Complex.continuous_ofReal.comp hg).mul continuous_const)

theorem tracePhase_continuousOn {B : Mat2} (hB : 4 < traceAmplitudeSq B) :
    ContinuousOn (tracePhase B) (Set.Icc (-2) 2) := by
  intro v hv
  have harg := Complex.continuousAt_arg_coe_angle (tracePhaseComplex_ne_zero hB hv)
  exact (harg.comp (tracePhaseComplex_continuous B).continuousAt).continuousWithinAt

theorem limitMatrix_trace (θ : Real.Angle) :
    (limitMatrix θ).trace = (angleRotation θ * rotationDefect).trace := by
  have hG : constantConjugator⁻¹ * constantConjugator = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr constantConjugator_det_ne_zero)
  unfold limitMatrix
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hG, one_mul]

def ellipticTracePath (v : ℝ) : Mat2 := limitMatrix (tracePhase rotationDefect v)

theorem ellipticTracePath_det (v : ℝ) : (ellipticTracePath v).det = 1 := limitMatrix_det _

theorem ellipticTracePath_trace {v : ℝ} (hv : v ∈ Set.Icc (-2) 2) : (ellipticTracePath v).trace = v := by
  rw [ellipticTracePath, limitMatrix_trace]
  exact tracePhase_trace rotationDefect_trace_amplitude hv

theorem ellipticTracePath_elliptic {v : ℝ} (hv : v ∈ Set.Ioo (-2) 2) : Elliptic (ellipticTracePath v) := by
  change |(ellipticTracePath v) 0 0 + (ellipticTracePath v) 1 1| < 2
  rw [← Matrix.trace_fin_two, ellipticTracePath_trace ⟨hv.1.le, hv.2.le⟩]
  exact abs_lt.mpr hv

theorem ellipticTracePath_continuousOn : ContinuousOn ellipticTracePath (Set.Icc (-2) 2) :=
  limitMatrix_continuous.continuousOn.comp
    (tracePhase_continuousOn rotationDefect_trace_amplitude) (fun _ _ => Set.mem_univ _)

@[simp] theorem angleRotation_zero : angleRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [angleRotation]

theorem angleRotation_rotationForm (θ : Real.Angle) : RotationForm (angleRotation θ) := by
  constructor <;> simp [angleRotation]

/-- A rotated non-rotation cannot be the identity. -/
theorem rotated_ne_one {B : Mat2} (hB : ¬RotationForm B) (θ : Real.Angle) :
    angleRotation θ * B ≠ 1 := by
  intro he
  have hl : angleRotation (-θ) * angleRotation θ = 1 := by
    rw [← angleRotation_add, neg_add_cancel, angleRotation_zero]
  have hb : B = angleRotation (-θ) := by
    calc
      B = (angleRotation (-θ) * angleRotation θ) * B := by rw [hl, one_mul]
      _ = angleRotation (-θ) := by rw [Matrix.mul_assoc, he, mul_one]
  exact hB (hb ▸ angleRotation_rotationForm (-θ))

theorem limitMatrix_ne_one (θ : Real.Angle) : limitMatrix θ ≠ 1 := by
  have hGl : constantConjugator⁻¹ * constantConjugator = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr constantConjugator_det_ne_zero)
  intro he
  apply rotated_ne_one rotationDefect_not_rotationForm θ
  have hh := congrArg (fun A : Mat2 => constantConjugator⁻¹ * A * constantConjugator) he
  simp only [limitMatrix, ← Matrix.mul_assoc, hGl, one_mul, mul_one] at hh
  simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc constantConjugator⁻¹ constantConjugator,
    hGl, one_mul, mul_one] using hh

/-- The trace-two endpoint is genuinely parabolic, rather than the identity. -/
theorem ellipticTracePath_endpoint :
    (ellipticTracePath 2).det = 1 ∧ (ellipticTracePath 2).trace = 2 ∧
      ellipticTracePath 2 ≠ 1 := by
  exact ⟨ellipticTracePath_det 2, ellipticTracePath_trace ⟨by norm_num, le_rfl⟩,
    limitMatrix_ne_one _⟩

end HallRay

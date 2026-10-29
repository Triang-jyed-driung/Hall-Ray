module

public import HallRay.EllipticPhases

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- The elementary two-dimensional Cayley–Hamilton identity at trace two. -/
theorem parabolic_nilpotent {A : Mat2} (hdet : A.det = 1) (htr : A.trace = 2) :
    (A - 1) ^ 2 = 0 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  have hd : A 1 1 = 2 - A 0 0 := by linarith
  rw [hd] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.sub_apply, Matrix.one_apply, hd] <;>
    nlinarith [hdet]

def endpointNilpotent : Mat2 := ellipticTracePath 2 - 1

theorem endpointNilpotent_ne_zero : endpointNilpotent ≠ 0 := by
  intro h
  exact ellipticTracePath_endpoint.2.2 (sub_eq_zero.mp h)

theorem endpointNilpotent_sq : endpointNilpotent ^ 2 = 0 :=
  parabolic_nilpotent ellipticTracePath_endpoint.1 ellipticTracePath_endpoint.2.1

/-- Centering a determinant-one matrix at half its trace gives a scalar square. -/
theorem centered_matrix_sq {A : Mat2} (hdet : A.det = 1) :
    (A - (A.trace / 2) • (1 : Mat2)) ^ 2 = ((A.trace / 2) ^ 2 - 1) • (1 : Mat2) := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.sub_apply,
      Matrix.trace_fin_two, Matrix.one_apply] <;> nlinarith

/-- The unnormalized complex structure along the trace path. -/
def centeredTracePath (v : ℝ) : Mat2 := ellipticTracePath v - (v / 2) • (1 : Mat2)

theorem centeredTracePath_sq {v : ℝ} (hv : v ∈ Set.Icc (-2) 2) :
    centeredTracePath v ^ 2 = ((v / 2) ^ 2 - 1) • (1 : Mat2) := by
  simpa only [ellipticTracePath_trace hv, centeredTracePath] using centered_matrix_sq (ellipticTracePath_det v)

theorem centeredTracePath_continuousOn : ContinuousOn centeredTracePath (Set.Icc (-2) 2) := by
  exact ellipticTracePath_continuousOn.sub ((continuous_id.div_const 2).smul continuous_const).continuousOn

@[simp] theorem centeredTracePath_endpoint : centeredTracePath 2 = endpointNilpotent := by
  simp [centeredTracePath, endpointNilpotent]

/-- The scalar which vanishes when the trace reaches the parabolic boundary. -/
def traceSine (v : ℝ) : ℝ := Real.sqrt (1 - (v / 2) ^ 2)

@[fun_prop] theorem traceSine_continuous : Continuous traceSine := by
  unfold traceSine
  fun_prop

theorem traceSine_pos {v : ℝ} (hv : v ∈ Set.Ioo (-2) 2) : 0 < traceSine v := by
  apply Real.sqrt_pos.mpr
  nlinarith [hv.1, hv.2]

@[simp] theorem traceSine_endpoint : traceSine 2 = 0 := by norm_num [traceSine]

/-- The complex structure whose circle is the compact subgroup of the return. -/
def traceComplexStructure (v : ℝ) : Mat2 := (traceSine v)⁻¹ • centeredTracePath v

theorem traceComplexStructure_sq {v : ℝ} (hv : v ∈ Set.Ioo (-2) 2) :
    traceComplexStructure v ^ 2 = -(1 : Mat2) := by
  have hs0 := ne_of_gt (traceSine_pos hv)
  have hs : traceSine v ^ 2 = 1 - (v / 2) ^ 2 := Real.sq_sqrt (by
    have := traceSine_pos hv
    nlinarith [hv.1, hv.2])
  rw [traceComplexStructure, pow_two, smul_mul_assoc, mul_smul_comm, smul_smul,
    ← pow_two (centeredTracePath v), centeredTracePath_sq ⟨hv.1.le, hv.2.le⟩, smul_smul]
  have hc : ((traceSine v)⁻¹ * (traceSine v)⁻¹) * ((v / 2) ^ 2 - 1) = -1 := by
    rw [← mul_inv, ← pow_two, hs]
    have h : 1 - (v / 2) ^ 2 ≠ 0 := by rw [← hs]; exact pow_ne_zero 2 hs0
    rw [show (v / 2) ^ 2 - 1 = -(1 - (v / 2) ^ 2) by ring,
      mul_neg, inv_mul_cancel₀ h]
  rw [hc, neg_one_smul]

/-- A quarter turn of the elliptic circle is the normalized centered matrix. -/
theorem ellipticCircle_quarter {A : Mat2} (hdet : A.det = 1) (hell : Elliptic A) :
    ellipticCircle A ((Real.pi / 2 : ℝ) : Real.Angle) =
      (Real.sin (ellipticAngle A))⁻¹ •
        (A - Real.cos (ellipticAngle A) • (1 : Mat2)) := by
  let G := ellipticConjugator A
  let β := ellipticAngle A
  have hG : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ellipticConjugator_det hdet hell))
  have hR : rotation β - Real.cos β • (1 : Mat2) =
      Real.sin β • rotation (Real.pi / 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [rotation, Matrix.one_apply]
  have hcenter : A - Real.cos β • (1 : Mat2) =
      Real.sin β • (G * rotation (Real.pi / 2) * G⁻¹) := by
    calc
      _ = G * (rotation β - Real.cos β • (1 : Mat2)) * G⁻¹ := by
        rw [Matrix.mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hG]
        rw [← elliptic_conjugate_rotation hdet hell]
      _ = _ := by rw [hR, mul_smul_comm, smul_mul_assoc]
  rw [hcenter, smul_smul, inv_mul_cancel₀ (ne_of_gt (elliptic_sin_pos hell)), one_smul]
  exact congrArg (fun R => G * R * G⁻¹) (angleRotation_coe (Real.pi / 2))

theorem traceComplexStructure_mem_circle {v : ℝ} (hv : v ∈ Set.Ioo (-2) 2) :
    ellipticCircle (ellipticTracePath v) ((Real.pi / 2 : ℝ) : Real.Angle) =
      traceComplexStructure v := by
  have ht := ellipticTracePath_trace ⟨hv.1.le, hv.2.le⟩
  have he := ellipticTracePath_elliptic hv
  rw [ellipticCircle_quarter (ellipticTracePath_det v) he, elliptic_cos he,
    ← Matrix.trace_fin_two, ht]
  have hs : Real.sin (ellipticAngle (ellipticTracePath v)) = traceSine v := by
    rw [ellipticAngle, ← Matrix.trace_fin_two, ht, Real.sin_arccos]
    rfl
  rw [hs]
  rfl

/-- The limiting compact subgroups become unbounded at the parabolic endpoint.
This is the matrix mechanism behind the degeneration of their shortest vectors. -/
theorem traceComplexStructure_norm_tendsto :
    Tendsto (fun v => ‖traceComplexStructure v‖) (𝓝[Set.Ioo (-2) 2] 2) atTop := by
  have hn : Tendsto (fun v => ‖centeredTracePath v‖) (𝓝[Set.Ioo (-2) 2] 2)
      (𝓝 ‖endpointNilpotent‖) := by
    simpa only [centeredTracePath_endpoint] using
      ((centeredTracePath_continuousOn 2 ⟨by norm_num, le_rfl⟩).mono
        Set.Ioo_subset_Icc_self).norm.tendsto
  have hs : Tendsto traceSine (𝓝[Set.Ioo (-2) 2] 2) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [traceSine_endpoint] using
        (traceSine_continuous.continuousAt (x := (2 : ℝ))).continuousWithinAt.tendsto
          (s := Set.Ioo (-2) 2)
    · filter_upwards [self_mem_nhdsWithin] with v hv
      exact traceSine_pos hv
  have hprod := hn.pos_mul_atTop (norm_pos_iff.mpr endpointNilpotent_ne_zero)
    hs.inv_tendsto_nhdsGT_zero
  convert hprod using 1
  funext v
  rw [traceComplexStructure, norm_smul, Real.norm_eq_abs, abs_of_nonneg
    (inv_nonneg.mpr (show 0 ≤ traceSine v from Real.sqrt_nonneg _)), Pi.inv_apply, mul_comm]

/-- In particular, actual elements of the limiting elliptic circles escape every norm bound. -/
theorem ellipticTracePath_circle_unbounded :
    Tendsto (fun v => ‖ellipticCircle (ellipticTracePath v)
      ((Real.pi / 2 : ℝ) : Real.Angle)‖) (𝓝[Set.Ioo (-2) 2] 2) atTop := by
  apply traceComplexStructure_norm_tendsto.congr'
  filter_upwards [self_mem_nhdsWithin] with v hv
  rw [traceComplexStructure_mem_circle hv]

end HallRay

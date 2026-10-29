module

public import HallRay.FrameSystole

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal
namespace HallRay
namespace PlaneNorm

def frameOperator (N : PlaneNorm) (A : Mat3) : N.FrameSpace →L[ℝ] N.FrameSpace :=
  N.frameCoordinatesContinuous.toContinuousLinearMap.comp
    ((LinearMap.toContinuousLinearMap (Matrix.toLin' A)).comp
      N.frameCoordinatesContinuous.symm.toContinuousLinearMap)

theorem frameOperator_integerPoint (N : PlaneNorm) (A : Mat3) (w : ℤ × (ℤ × ℤ)) :
    N.frameOperator A (N.frameIntegerPoint w) = N.frameVector A w := by rfl

def frameOperatorLinear (N : PlaneNorm) : Mat3 →ₗ[ℝ] (N.FrameSpace →L[ℝ] N.FrameSpace) where
  toFun := N.frameOperator
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro x
    change N.frameCoordinates ((A + B).mulVec (N.frameCoordinates.symm x)) =
      N.frameCoordinates (A.mulVec (N.frameCoordinates.symm x)) +
      N.frameCoordinates (B.mulVec (N.frameCoordinates.symm x))
    rw [Matrix.add_mulVec, map_add]
  map_smul' r A := by
    apply ContinuousLinearMap.ext
    intro x
    change N.frameCoordinates ((r • A).mulVec (N.frameCoordinates.symm x)) =
      r • N.frameCoordinates (A.mulVec (N.frameCoordinates.symm x))
    rw [Matrix.smul_mulVec, map_smul]

@[fun_prop] theorem frameOperator_continuous (N : PlaneNorm) : Continuous N.frameOperator :=
  N.frameOperatorLinear.continuous_of_finiteDimensional

/-- Uniform relative length control for every integer vector near an invertible frame. -/
theorem frameVector_perturbation (N : PlaneNorm) (A B : Mat3) (hA : A.det ≠ 0)
    (w : ℤ × (ℤ × ℤ)) :
    |‖N.frameVector B w‖ - ‖N.frameVector A w‖| ≤
      (‖N.frameOperator B - N.frameOperator A‖ *
        ‖(N.frameChange A hA).symm.toContinuousLinearMap‖) * ‖N.frameVector A w‖ := by
  have hinv : (N.frameChange A hA).symm (N.frameVector A w) = N.frameIntegerPoint w := by
    rw [← N.frameChange_integerPoint A hA w, ContinuousLinearEquiv.symm_apply_apply]
  have hb := (N.frameChange A hA).symm.toContinuousLinearMap.le_opNorm (N.frameVector A w)
  rw [ContinuousLinearEquiv.coe_apply, hinv] at hb
  calc
    _ ≤ ‖N.frameVector B w - N.frameVector A w‖ := abs_norm_sub_norm_le _ _
    _ = ‖(N.frameOperator B - N.frameOperator A) (N.frameIntegerPoint w)‖ := by
      rw [sub_apply, frameOperator_integerPoint, frameOperator_integerPoint]
    _ ≤ ‖N.frameOperator B - N.frameOperator A‖ * ‖N.frameIntegerPoint w‖ :=
      (N.frameOperator B - N.frameOperator A).le_opNorm _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb
        (norm_nonneg (N.frameOperator B - N.frameOperator A))

end PlaneNorm
/-- Systole is continuous at every invertible frame, for any chosen plane norm. -/
theorem frameSystole_continuousAt (N : PlaneNorm) (A : Mat3) (hA : A.det ≠ 0) :
    ContinuousAt (frameSystole N) A := by
  obtain ⟨w, hw, hs, hmin⟩ := N.shortest_matrix_vector A hA
  let s := ‖N.frameVector A w‖
  let η := fun B : Mat3 => ‖N.frameOperator B - N.frameOperator A‖ *
    ‖(N.frameChange A hA).symm.toContinuousLinearMap‖
  have hη : Continuous η := by
    exact ((N.frameOperator_continuous.sub continuous_const).norm).mul_const _
  have hηA : η A = 0 := by simp [η]
  have hval : frameSystole N A = ENNReal.ofReal s := by
    apply le_antisymm
    · exact iInf_le (fun v : {v : ℤ × (ℤ × ℤ) // v ≠ 0} =>
        ENNReal.ofReal ‖N.frameVector A v.val‖) ⟨w, hw⟩
    · exact le_iInf (fun v => ENNReal.ofReal_le_ofReal (hmin v.val v.property))
  have hupper (B : Mat3) : frameSystole N B ≤ ENNReal.ofReal ((1 + η B) * s) := by
    apply (iInf_le (fun v : {v : ℤ × (ℤ × ℤ) // v ≠ 0} =>
      ENNReal.ofReal ‖N.frameVector B v.val‖) ⟨w, hw⟩).trans
    apply ENNReal.ofReal_le_ofReal
    have hh := (abs_le.mp (N.frameVector_perturbation A B hA w)).2
    change ‖N.frameVector B w‖ ≤ (1 + η B) * ‖N.frameVector A w‖
    change ‖N.frameVector B w‖ - ‖N.frameVector A w‖ ≤ η B * ‖N.frameVector A w‖ at hh
    linarith
  have hlower (B : Mat3) (hsmall : η B < 1) :
      ENNReal.ofReal ((1 - η B) * s) ≤ frameSystole N B := by
    apply le_iInf
    intro v
    apply ENNReal.ofReal_le_ofReal
    have hm := mul_le_mul_of_nonneg_left (hmin v.val v.property) (by linarith : 0 ≤ 1 - η B)
    have hh := (abs_le.mp (N.frameVector_perturbation A B hA v.val)).1
    change -(η B * ‖N.frameVector A v.val‖) ≤
      ‖N.frameVector B v.val‖ - ‖N.frameVector A v.val‖ at hh
    dsimp only [s]
    nlinarith
  have hleft : Tendsto (fun B => ENNReal.ofReal ((1 - η B) * s)) (𝓝 A) (𝓝 (ENNReal.ofReal s)) := by
    have hc : Continuous (fun B => ENNReal.ofReal ((1 - η B) * s)) :=
      ENNReal.continuous_ofReal.comp ((continuous_const.sub hη).mul_const s)
    simpa only [hηA, sub_zero, one_mul] using hc.continuousAt.tendsto (x := A)
  have hright : Tendsto (fun B => ENNReal.ofReal ((1 + η B) * s)) (𝓝 A) (𝓝 (ENNReal.ofReal s)) := by
    have hc : Continuous (fun B => ENNReal.ofReal ((1 + η B) * s)) :=
      ENNReal.continuous_ofReal.comp ((continuous_const.add hη).mul_const s)
    simpa only [hηA, add_zero, one_mul] using hc.continuousAt.tendsto (x := A)
  change Tendsto (frameSystole N) (𝓝 A) (𝓝 (frameSystole N A))
  rw [hval]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
  · have he : ∀ᶠ B in 𝓝 A, η B < 1 := hη.continuousAt.eventually (gt_mem_nhds (by rw [hηA]; norm_num))
    exact he.mono hlower
  · exact Eventually.of_forall hupper

def frameHeight (N : PlaneNorm) (A : Mat3) : ℝ≥0∞ := (frameSystole N A)⁻¹

theorem frameHeight_continuousAt (N : PlaneNorm) (A : Mat3) (hA : A.det ≠ 0) :
    ContinuousAt (frameHeight N) A := (frameSystole_continuousAt N A hA).fun_inv

theorem frameHeight_ne_top (N : PlaneNorm) (A : Mat3) (hA : A.det ≠ 0) :
    frameHeight N A ≠ ⊤ := ENNReal.inv_ne_top.mpr (ne_of_gt (frameSystole_pos N A hA))

theorem frameHeight_pos (N : PlaneNorm) (A : Mat3) : 0 < frameHeight N A :=
  ENNReal.inv_pos.mpr (frameSystole_ne_top N A)

end HallRay

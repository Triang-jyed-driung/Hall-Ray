module

public import HallRay.CodedHallRay

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal
namespace HallRay
namespace PlaneNorm

@[simp] theorem frameOperator_one (N : PlaneNorm) : N.frameOperator 1 = ContinuousLinearMap.id ℝ N.FrameSpace := by
  apply ContinuousLinearMap.ext
  intro x
  change N.frameCoordinates ((1 : Mat3).mulVec (N.frameCoordinates.symm x)) = x
  rw [Matrix.one_mulVec, LinearEquiv.apply_symm_apply]

theorem frameVector_left (N : PlaneNorm) (H A : Mat3) (w : ℤ × (ℤ × ℤ)) :
    N.frameVector (H * A) w = N.frameOperator H (N.frameVector A w) := by
  change N.frameCoordinates ((H * A).mulVec ![(w.1 : ℝ), (w.2.1 : ℝ), (w.2.2 : ℝ)]) =
    N.frameCoordinates (H.mulVec (N.frameCoordinates.symm
      (N.frameCoordinates (A.mulVec ![(w.1 : ℝ), (w.2.1 : ℝ), (w.2.2 : ℝ)]))))
  rw [LinearEquiv.symm_apply_apply, Matrix.mulVec_mulVec]

/-- Relative length distortion depends only on the left multiplier, not on the lattice frame. -/
theorem frameVector_left_distortion (N : PlaneNorm) (H A : Mat3) (w : ℤ × (ℤ × ℤ)) :
    |‖N.frameVector (H * A) w‖ - ‖N.frameVector A w‖| ≤
      ‖N.frameOperator H - N.frameOperator 1‖ * ‖N.frameVector A w‖ := by
  have hh := (N.frameOperator H - N.frameOperator 1).le_opNorm (N.frameVector A w)
  rw [sub_apply, frameOperator_one, ContinuousLinearMap.id_apply, ← frameVector_left] at hh
  simpa only [frameOperator_one] using (abs_norm_sub_norm_le _ _).trans hh

end PlaneNorm

def leftDistortion (N : PlaneNorm) (H : Mat3) : ℝ := ‖N.frameOperator H - N.frameOperator 1‖

/-- Uniform multiplicative bounds for the systole under a near-identity left multiplication. -/
theorem frameSystole_left_bounds (N : PlaneNorm) (H A : Mat3) (hA : A.det ≠ 0)
    (hsmall : leftDistortion N H < 1) :
    ENNReal.ofReal (1 - leftDistortion N H) * frameSystole N A ≤ frameSystole N (H * A) ∧
      frameSystole N (H * A) ≤ ENNReal.ofReal (1 + leftDistortion N H) * frameSystole N A := by
  obtain ⟨w, hw, hs, hmin⟩ := N.shortest_matrix_vector A hA
  let s := ‖N.frameVector A w‖
  let η := leftDistortion N H
  have hη : 0 ≤ η := norm_nonneg _
  have hminus : 0 ≤ 1 - η := by linarith
  have hval : frameSystole N A = ENNReal.ofReal s := by
    apply le_antisymm
    · exact iInf_le (fun v : {v : ℤ × (ℤ × ℤ) // v ≠ 0} => ENNReal.ofReal ‖N.frameVector A v.val‖) ⟨w, hw⟩
    · exact le_iInf (fun v => ENNReal.ofReal_le_ofReal (hmin v.val v.property))
  rw [hval, ← ENNReal.ofReal_mul hminus, ← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + η)]
  constructor
  · apply le_iInf
    intro v
    apply ENNReal.ofReal_le_ofReal
    have hm := mul_le_mul_of_nonneg_left (hmin v.val v.property) hminus
    have hh := (abs_le.mp (N.frameVector_left_distortion H A v.val)).1
    change -(η * ‖N.frameVector A v.val‖) ≤ ‖N.frameVector (H * A) v.val‖ - ‖N.frameVector A v.val‖ at hh
    dsimp only [s]
    nlinarith
  · apply (iInf_le (fun v : {v : ℤ × (ℤ × ℤ) // v ≠ 0} => ENNReal.ofReal ‖N.frameVector (H * A) v.val‖) ⟨w, hw⟩).trans
    apply ENNReal.ofReal_le_ofReal
    have hh := (abs_le.mp (N.frameVector_left_distortion H A w)).2
    change ‖N.frameVector (H * A) w‖ - ‖N.frameVector A w‖ ≤ η * ‖N.frameVector A w‖ at hh
    dsimp only [s]
    linarith

theorem frameHeight_left_bounds (N : PlaneNorm) (H A : Mat3) (hA : A.det ≠ 0)
    (hsmall : leftDistortion N H < 1) :
    frameHeight N A * (ENNReal.ofReal (1 + leftDistortion N H))⁻¹ ≤ frameHeight N (H * A) ∧
      frameHeight N (H * A) ≤ frameHeight N A * (ENNReal.ofReal (1 - leftDistortion N H))⁻¹ := by
  have hb := frameSystole_left_bounds N H A hA hsmall
  have hη : 0 ≤ leftDistortion N H := norm_nonneg _
  have hp : ENNReal.ofReal (1 + leftDistortion N H) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hm : ENNReal.ofReal (1 - leftDistortion N H) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  constructor
  · have hh := ENNReal.inv_le_inv.mpr hb.2
    rw [ENNReal.mul_inv (Or.inl hp) (Or.inl ENNReal.ofReal_ne_top), mul_comm] at hh
    exact hh
  · have hh := ENNReal.inv_le_inv.mpr hb.1
    rw [ENNReal.mul_inv (Or.inl hm) (Or.inl ENNReal.ofReal_ne_top), mul_comm] at hh
    exact hh

/-- Asymptotically trivial left multipliers preserve height limsups, even at zero or infinity. -/
theorem asymptotic_left_height_limsup (N : PlaneNorm) {G H : ℝ → Mat3}
    (hG : ∀ t, (G t).det ≠ 0) (hH : Tendsto H atTop (𝓝 1)) :
    limsup (fun t => frameHeight N (H t * G t)) atTop = limsup (fun t => frameHeight N (G t)) atTop := by
  let η := fun t => leftDistortion N (H t)
  have hη : Tendsto η atTop (𝓝 0) := by
    have hh := ((N.frameOperator_continuous.continuousAt.tendsto.comp hH).sub_const (N.frameOperator 1)).norm
    simpa only [η, leftDistortion, Function.comp_def, sub_self, norm_zero] using hh
  let f := fun t => frameHeight N (G t)
  let g := fun t => frameHeight N (H t * G t)
  let p := fun t => (ENNReal.ofReal (1 + η t))⁻¹
  let m := fun t => (ENNReal.ofReal (1 - η t))⁻¹
  have hp : Tendsto p atTop (𝓝 1) := by
    have hr := hη.const_add 1
    simp only [add_zero] at hr
    have hh := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr).inv
    simpa only [p, Function.comp_def, ENNReal.ofReal_one, inv_one] using hh
  have hm : Tendsto m atTop (𝓝 1) := by
    have hr := hη.const_sub 1
    simp only [sub_zero] at hr
    have hh := (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr).inv
    simpa only [m, Function.comp_def, ENNReal.ofReal_one, inv_one] using hh
  have hb : ∀ᶠ t in atTop, f t * p t ≤ g t ∧ g t ≤ f t * m t := by
    filter_upwards [hη.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht
    exact frameHeight_left_bounds N (H t) (G t) (hG t) ht
  have hlower := ENNReal.le_limsup_mul (u := f) (v := p) (f := atTop)
  rw [hp.liminf_eq, mul_one] at hlower
  have hu := ENNReal.limsup_mul_le' (u := f) (v := m) (f := atTop)
    (Or.inr (by rw [hm.limsup_eq]; norm_num)) (Or.inr (by rw [hm.limsup_eq]; norm_num))
  rw [hm.limsup_eq, mul_one] at hu
  exact le_antisymm ((limsup_le_limsup (hb.mono (fun _ h => h.2))).trans hu)
    (hlower.trans (limsup_le_limsup (hb.mono (fun _ h => h.1))))

end HallRay

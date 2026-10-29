module

public import HallRay.FrameNorm
public import HallRay.DaniSeparation

@[expose] public section
noncomputable section
open scoped ENNReal
namespace HallRay

/-- Systole in a marked frame, using the same arbitrary norm as Dani's correspondence. -/
def frameSystole (N : PlaneNorm) (A : Mat3) : ℝ≥0∞ :=
  ⨅ w : {w : ℤ × (ℤ × ℤ) // w ≠ 0}, ENNReal.ofReal ‖N.frameVector A w.val‖

theorem frameSystole_attained (N : PlaneNorm) (A : Mat3) (hA : A.det ≠ 0) :
    ∃ w : {w : ℤ × (ℤ × ℤ) // w ≠ 0},
      frameSystole N A = ENNReal.ofReal ‖N.frameVector A w.val‖ := by
  obtain ⟨w, hw, _, hmin⟩ := N.shortest_matrix_vector A hA
  refine ⟨⟨w, hw⟩, ?_⟩
  unfold frameSystole
  apply le_antisymm
  · exact iInf_le (fun v : {v : ℤ × (ℤ × ℤ) // v ≠ 0} =>
      ENNReal.ofReal ‖N.frameVector A v.val‖) ⟨w, hw⟩
  exact le_iInf (fun v => ENNReal.ofReal_le_ofReal (hmin v.val v.property))

theorem frameSystole_pos (N : PlaneNorm) (A : Mat3) (hA : A.det ≠ 0) :
    0 < frameSystole N A := by
  obtain ⟨w, hw, hpos, hmin⟩ := N.shortest_matrix_vector A hA
  have hle : ENNReal.ofReal ‖N.frameVector A w‖ ≤ frameSystole N A :=
    le_iInf (fun v => ENNReal.ofReal_le_ofReal (hmin v.val v.property))
  exact (ENNReal.ofReal_pos.mpr hpos).trans_le hle

theorem frameSystole_ne_top (N : PlaneNorm) (A : Mat3) : frameSystole N A ≠ ⊤ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  exact iInf_le _ ⟨(1, (0, 0)), by simp⟩

theorem frameVector_norm (N : PlaneNorm) (A : Mat3) (w : ℤ × (ℤ × ℤ)) :
    ‖N.frameVector A w‖ =
      max |(A.mulVec ![(w.1 : ℝ), (w.2.1 : ℝ), (w.2.2 : ℝ)]) 0|
        (N.value ((A.mulVec ![(w.1 : ℝ), (w.2.1 : ℝ), (w.2.2 : ℝ)]) 1,
          (A.mulVec ![(w.1 : ℝ), (w.2.1 : ℝ), (w.2.2 : ℝ)]) 2)) := by
  rw [PlaneNorm.frameVector, Prod.norm_def]
  rfl

/-- The direct-frame systole agrees exactly with the flow formula of Section 2. -/
theorem frameSystole_flow_chart (N : PlaneNorm) (x : Point) (t : ℝ) :
    frameSystole N (flow t * rawChart x 0) = orbitSystole N x t := by
  apply iInf_congr
  intro w
  congr 1
  rw [frameVector_norm]
  have hvec : (flow t * rawChart x 0).mulVec
      ![(w.val.1 : ℝ), (w.val.2.1 : ℝ), (w.val.2.2 : ℝ)] =
      ![Real.exp (-2 * t) * (w.val.1 : ℝ),
        Real.exp t * ((w.val.2.1 : ℝ) - (w.val.1 : ℝ) * x.1),
        Real.exp t * ((w.val.2.2 : ℝ) - (w.val.1 : ℝ) * x.2)] := by
    ext i
    fin_cases i <;> simp [flow, rawChart, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ] <;> ring
  rw [hvec]
  change max |Real.exp (-2 * t) * (w.val.1 : ℝ)|
    (N.value (Real.exp t * ((w.val.2.1 : ℝ) - (w.val.1 : ℝ) * x.1),
      Real.exp t * ((w.val.2.2 : ℝ) - (w.val.1 : ℝ) * x.2))) = _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : (Real.exp t * ((w.val.2.1 : ℝ) - (w.val.1 : ℝ) * x.1),
      Real.exp t * ((w.val.2.2 : ℝ) - (w.val.1 : ℝ) * x.2)) =
      (-Real.exp t) • ((w.val.1 : ℝ) • x - integerPoint w.val.2) := by
    ext <;> simp [integerPoint] <;> ring
  rw [he, N.smul_eq, abs_neg, abs_of_pos (Real.exp_pos _)]

end HallRay

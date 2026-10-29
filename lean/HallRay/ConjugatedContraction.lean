module

public import HallRay.RotationDirections
public import HallRay.BulkFlow

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- The parabolic complex structure in the constant-rotation coordinates. -/
def conjugatedTraceStructure (v : ℝ) : Mat2 :=
  constantConjugator⁻¹ * traceComplexStructure v * constantConjugator

theorem conjugatedTraceStructure_sq {v : ℝ} (hv : v ∈ Set.Ioo (-2) 2) :
    conjugatedTraceStructure v ^ 2 = -1 := by
  have hl : constantConjugator⁻¹ * constantConjugator = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr constantConjugator_det_ne_zero)
  have hr : constantConjugator * constantConjugator⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr constantConjugator_det_ne_zero)
  have hcancel (X : Mat2) : constantConjugator * (constantConjugator⁻¹ * X) = X := by
    rw [← Matrix.mul_assoc, hr, one_mul]
  unfold conjugatedTraceStructure
  rw [pow_two]
  simp only [Matrix.mul_assoc, hcancel]
  rw [← Matrix.mul_assoc (traceComplexStructure v), ← pow_two,
    traceComplexStructure_sq hv, Matrix.neg_mul, one_mul, mul_neg, hl]

theorem conjugatedTraceStructure_norm_tendsto :
    Tendsto (fun v => ‖conjugatedTraceStructure v‖) (𝓝[Set.Ioo (-2) 2] 2) atTop := by
  have hl : constantConjugator⁻¹ * constantConjugator = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr constantConjugator_det_ne_zero)
  have hr : constantConjugator * constantConjugator⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr constantConjugator_det_ne_zero)
  have hG : constantConjugator ≠ 0 := by
    intro h
    have hh := constantConjugator_det_ne_zero
    simp [h] at hh
  have hiG : constantConjugator⁻¹ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hr
    exact zero_ne_one hr
  let K := ‖constantConjugator‖ * ‖constantConjugator⁻¹‖
  have hK : 0 < K := mul_pos (norm_pos_iff.mpr hG) (norm_pos_iff.mpr hiG)
  have hbound (v : ℝ) : ‖traceComplexStructure v‖ / K ≤ ‖conjugatedTraceStructure v‖ := by
    have heq : constantConjugator * conjugatedTraceStructure v * constantConjugator⁻¹ =
        traceComplexStructure v := by
      simp only [conjugatedTraceStructure, ← Matrix.mul_assoc, hr, one_mul]
      rw [Matrix.mul_assoc, hr, mul_one]
    have hn := (norm_mul_le (constantConjugator * conjugatedTraceStructure v) constantConjugator⁻¹).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le constantConjugator (conjugatedTraceStructure v))
        (norm_nonneg _))
    rw [heq] at hn
    apply (div_le_iff₀ hK).mpr
    dsimp [K]
    nlinarith
  exact tendsto_atTop_mono hbound
    (traceComplexStructure_norm_tendsto.atTop_mul_const (inv_pos.mpr hK) |>.congr
      (fun _ => by rw [div_eq_mul_inv]))

/-- A constant-return rotation can place any fixed vector in a contracting direction. -/
theorem trace_structure_rotated_vector (v : TraceParameter) (u : EuclideanSpace ℝ (Fin 2)) :
    ∃ ξ : Real.Angle,
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        (traceComplexStructure v * ellipticCircle constantMatrix ξ) u‖ ≤
      (2 * ‖constantConjugator‖ *
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) constantConjugator⁻¹ u‖) /
          ‖conjugatedTraceStructure v‖ := by
  let G := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) constantConjugator
  let H := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) constantConjugator⁻¹
  let T := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (conjugatedTraceStructure v)
  let x := H u
  obtain ⟨w, hw, hTw⟩ := matrix_complexStructure_contracts (conjugatedTraceStructure_sq v.property)
  have hnorm : ‖x‖ = ‖‖x‖ • w‖ := by simp [norm_smul, hw]
  obtain ⟨ξ, hξ⟩ := exists_rotation_sends hnorm
  refine ⟨(ξ : Real.Angle), ?_⟩
  have hr : constantConjugator * constantConjugator⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr constantConjugator_det_ne_zero)
  have hGD : constantConjugator * conjugatedTraceStructure v = traceComplexStructure v * constantConjugator := by
    simp only [conjugatedTraceStructure, ← Matrix.mul_assoc, hr, one_mul]
  have heq : traceComplexStructure v * ellipticCircle constantMatrix (ξ : Real.Angle) =
      constantConjugator * conjugatedTraceStructure v * rotation ξ * constantConjugator⁻¹ := by
    rw [hGD]
    simp only [ellipticCircle, angleRotation_coe, Matrix.mul_assoc]
  have hvec : Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
      (traceComplexStructure v * ellipticCircle constantMatrix (ξ : Real.Angle)) u = G (T (‖x‖ • w)) := by
    rw [heq]
    simp only [map_mul, mul_apply_eq_comp]
    rw [hξ]
  rw [hvec]
  calc
    _ ≤ ‖G‖ * ‖T (‖x‖ • w)‖ := G.le_opNorm _
    _ = ‖G‖ * (‖x‖ * ‖T w‖) := by
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
    _ ≤ ‖G‖ * (‖x‖ * (2 / ‖conjugatedTraceStructure v‖)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTw.le (norm_nonneg x)) (norm_nonneg G)
    _ = _ := by dsimp only [G, x, H]; rw [Matrix.l2_opNorm_toEuclideanCLM]; ring

/-- Every fixed bulk vector can be made arbitrarily short as the trace approaches two. -/
theorem bulk_vector_arbitrary_contraction (u : EuclideanSpace ℝ (Fin 2)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ v : ℝ in 𝓝[Set.Ioo (-2) 2] 2, ∃ ξ : Real.Angle,
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
        (ellipticCircle (ellipticTracePath v) ((Real.pi / 2 : ℝ) : Real.Angle) *
          ellipticCircle constantMatrix ξ) u‖ < ε := by
  let K := 2 * ‖constantConjugator‖ *
    ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) constantConjugator⁻¹ u‖
  have hlim : Tendsto (fun v => K / ‖conjugatedTraceStructure v‖)
      (𝓝[Set.Ioo (-2) 2] 2) (𝓝 0) :=
    tendsto_const_nhds.div_atTop conjugatedTraceStructure_norm_tendsto
  filter_upwards [self_mem_nhdsWithin, hlim.eventually (gt_mem_nhds hε)] with v hv he
  obtain ⟨ξ, hξ⟩ := trace_structure_rotated_vector ⟨v, hv⟩ u
  refine ⟨ξ, ?_⟩
  rw [traceComplexStructure_mem_circle hv]
  exact hξ.trans_lt he

end HallRay

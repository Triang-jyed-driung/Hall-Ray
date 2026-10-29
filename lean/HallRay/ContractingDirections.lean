module

public import HallRay.ParabolicEndpoint

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- A complex structure with large norm has a strongly contracted unit vector.
An approximate operator-norm maximizer suffices; no singular-value decomposition is needed. -/
theorem complexStructure_contracts {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (J : E →L[ℝ] E) (hJ : ∀ x, J (J x) = -x) (hpos : 0 < ‖J‖) :
    ∃ w : E, ‖w‖ = 1 ∧ ‖J w‖ < 2 / ‖J‖ := by
  obtain ⟨x, hx, hJx⟩ := J.exists_lt_apply_of_lt_opNorm (show ‖J‖ / 2 < ‖J‖ by linarith)
  have hn : 0 < ‖J x‖ := by linarith
  let w := ‖J x‖⁻¹ • J x
  refine ⟨w, ?_, ?_⟩
  · simp [w, norm_smul, inv_mul_cancel₀ hn.ne']
  · dsimp [w]
    rw [map_smul, hJ, norm_smul, norm_neg, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), mul_comm, ← div_eq_mul_inv]
    apply (div_lt_div_iff₀ hn hpos).mpr
    have hm := mul_lt_mul_of_pos_right hx hpos
    nlinarith

/-- Specialized to a matrix whose square is minus the identity. -/
theorem matrix_complexStructure_contracts {J : Mat2} (hJ : J ^ 2 = -1) :
    ∃ w : EuclideanSpace ℝ (Fin 2), ‖w‖ = 1 ∧
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J w‖ < 2 / ‖J‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) J
  have hJJ : ∀ x, T (T x) = -x := by
    intro x
    have hh := congrArg (fun A : Mat2 => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A x) hJ
    simpa [pow_two, map_mul, T] using hh
  have hne : J ≠ 0 := by
    intro he
    rw [he, zero_pow (by norm_num)] at hJ
    have hh := congrArg (fun A : Mat2 => A 0 0) hJ
    norm_num [Matrix.one_apply] at hh
  have hpos : 0 < ‖T‖ := by
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact norm_pos_iff.mpr hne
  simpa only [T, Matrix.l2_opNorm_toEuclideanCLM] using complexStructure_contracts T hJJ hpos

theorem traceComplexStructure_contracts {v : ℝ} (hv : v ∈ Set.Ioo (-2) 2) :
    ∃ w : EuclideanSpace ℝ (Fin 2), ‖w‖ = 1 ∧
      ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (traceComplexStructure v) w‖ <
        2 / ‖traceComplexStructure v‖ :=
  matrix_complexStructure_contracts (traceComplexStructure_sq hv)

/-- Arbitrarily strong contraction occurs in the limiting circles near the endpoint. -/
theorem parabolic_arbitrary_contraction {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ v : ℝ in 𝓝[Set.Ioo (-2) 2] 2,
      ∃ w : EuclideanSpace ℝ (Fin 2), ‖w‖ = 1 ∧
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
          (ellipticCircle (ellipticTracePath v) ((Real.pi / 2 : ℝ) : Real.Angle)) w‖ < ε := by
  have ht : Tendsto (fun v => 2 / ‖traceComplexStructure v‖)
      (𝓝[Set.Ioo (-2) 2] 2) (𝓝 0) :=
    tendsto_const_nhds.div_atTop traceComplexStructure_norm_tendsto
  filter_upwards [self_mem_nhdsWithin, ht.eventually (gt_mem_nhds hε)] with v hv he
  obtain ⟨w, hw, hcon⟩ := traceComplexStructure_contracts hv
  refine ⟨w, hw, ?_⟩
  rw [traceComplexStructure_mem_circle hv]
  exact hcon.trans he

end HallRay

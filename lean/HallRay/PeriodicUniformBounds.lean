module

public import HallRay.PeriodicMaximaConvergence

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

@[simp] theorem angleRotation_norm (θ : Real.Angle) : ‖angleRotation θ‖ = 1 := by
  induction θ using Real.Angle.induction_on
  rw [angleRotation_coe, rotation_norm]

def ellipticPowerConstant (A : Mat2) : ℝ := ‖ellipticConjugator A‖ * ‖(ellipticConjugator A)⁻¹‖

theorem ellipticCircle_norm_le (A : Mat2) (θ : Real.Angle) :
    ‖ellipticCircle A θ‖ ≤ ellipticPowerConstant A := by
  unfold ellipticCircle ellipticPowerConstant
  exact (norm_mul_le _ _).trans (by
    have h := norm_mul_le (ellipticConjugator A) (angleRotation θ)
    rw [angleRotation_norm, mul_one] at h
    exact mul_le_mul_of_nonneg_right h (norm_nonneg _))

theorem ellipticPowerConstant_continuousAt {A : Mat2} (hA : A.det = 1) (hell : Elliptic A) :
    ContinuousAt ellipticPowerConstant A :=
  (ellipticConjugator_continuousAt hell).norm.mul
    (ellipticConjugator_inverse_continuousAt hA hell).norm

/-- One common bound controls every partial return, not just a single period. -/
theorem periodic_all_partial_bound (n : ℕ) (h : Admissible n) {K : ℝ}
    (hK : ellipticPowerConstant (periodMatrix n) ≤ K) (m : ℕ) :
    ‖cocycle fiberMap (periodicWord n) m‖ ≤ K * (2 * constantPowerBound) ∧
      ‖(cocycle fiberMap (periodicWord n) m)⁻¹‖ ≤ K * (2 * constantPowerBound) := by
  let k := m / (n + 1)
  let j := m % (n + 1)
  have hj : j ≤ n := by dsimp [j]; have := Nat.mod_lt m (by omega : 0 < n + 1); omega
  have hm : m = k * (n + 1) + j := by
    simpa only [k, j, Nat.mul_comm] using (Nat.div_add_mod m (n + 1)).symm
  have hp : ‖periodMatrix n ^ k‖ ≤ K :=
    (elliptic_power_norm_le (periodMatrix_det n) h k).trans hK
  have hbound : ‖cocycle fiberMap (periodicWord n) m‖ ≤ K * (2 * constantPowerBound) := by
    rw [hm, cocycle_periods_remainder _ _ _ (periodicWord_period n)]
    change ‖periodMatrix n ^ k * cocycle fiberMap (periodicWord n) j‖ ≤ _
    exact (norm_mul_le _ _).trans
      (mul_le_mul hp (periodic_partial_norm n j hj) (norm_nonneg _) (by
        have hpos : 0 ≤ ellipticPowerConstant (periodMatrix n) := mul_nonneg (norm_nonneg _) (norm_nonneg _)
        exact hpos.trans hK))
  exact ⟨hbound, by rw [determinant_one_inverse_norm (fiberProduct_det _ _)]; exact hbound⟩

/-- The elliptic trace family has a common power bound on each compact parameter set. -/
theorem trace_compact_power_bound {J : Set TraceParameter} (hJ : IsCompact J) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ v ∈ J, ellipticPowerConstant (ellipticTracePath v) < K := by
  have hc : Continuous (fun v : TraceParameter => ellipticPowerConstant (ellipticTracePath v)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    exact ContinuousAt.comp (f := fun v : TraceParameter => ellipticTracePath v)
      (g := ellipticPowerConstant)
      (ellipticPowerConstant_continuousAt (ellipticTracePath_det v)
        (ellipticTracePath_elliptic v.property)) traceReturn_continuous.continuousAt
  obtain ⟨K, hK⟩ := (hJ.image hc).bddAbove
  refine ⟨max K 0 + 1, by linarith [le_max_right K 0], ?_⟩
  intro v hv
  have hh := hK (Set.mem_image_of_mem _ hv)
  linarith [le_max_left K 0]

end HallRay

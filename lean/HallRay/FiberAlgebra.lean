module

public import HallRay.FiberAdjustment

@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace HallRay

theorem blockFiber_flow_commute (E : Mat2) (t : ℝ) : blockFiber E * flow t = flow t * blockFiber E := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockFiber, flow, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem codedChart_left (z : Word) (E F : Mat2) :
    blockFiber E * codedChart z F = codedChart z (E * F) := by
  unfold codedChart chart
  rw [mul_smul_comm, ← Matrix.mul_assoc, blockFiber_mul]

theorem flightChart_left (a : ℝ) (z : Word) (E F : Mat2) :
    blockFiber E * flightChart a (z, F) = flightChart a (z, E * F) := by
  unfold flightChart
  rw [← Matrix.mul_assoc, blockFiber_flow_commute, Matrix.mul_assoc, codedChart_left]

/-- Stage selection with a fixed neighborhood and a uniform partial-return bound. -/
theorem uniform_adjusted_periodic_choices (N : PlaneNorm) :
    ∃ T : ℝ, 0 < T ∧ ∀ A : ℝ, T < A →
      ∃ δ K : ℝ, 0 < δ ∧ δ < 1 ∧ 1 ≤ K ∧
        ∀ E : FiberParameter, ‖E.val - 1‖ ≤ δ → ∀ ε : ℝ, 0 < ε → ∀ M : ℕ,
          ∃ n : ℕ, M < n ∧ Admissible n ∧ |(periodicDepth N n E).toReal - A| < ε ∧
            ∀ m : ℕ, ‖cocycle fiberMap (periodicWord n) m‖ ≤ K ∧
              ‖(cocycle fiberMap (periodicWord n) m)⁻¹‖ ≤ K := by
  obtain ⟨T, hT, hchoice⟩ := fiber_adjustment N
  refine ⟨T, hT, ?_⟩
  intro A hA
  obtain ⟨δ, K, hδ, hδ1, hK, hadjust⟩ := hchoice A hA
  let K' := K * (2 * constantPowerBound)
  have hK' : 1 ≤ K' := by
    have hc := constantPowerBound_ge_one
    dsimp [K']
    nlinarith
  refine ⟨δ, K', hδ, hδ1, hK', ?_⟩
  intro E hE ε hε M
  obtain ⟨v, htarget, hv⟩ := hadjust E hE
  obtain ⟨n, hn, ha, hclose, hbound⟩ := adjusted_periodic_choice N E v htarget hv hε M
  exact ⟨n, hn, ha, hclose, fun m => periodic_all_partial_bound n ha hbound.le m⟩

end HallRay

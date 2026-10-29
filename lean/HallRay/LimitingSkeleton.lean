module

public import HallRay.PeriodicOrbitHeight
public import HallRay.ParabolicEndpoint

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- The phase-independent beginning and end data for the limiting orbit model. -/
def beginningSkeleton (r : ℕ) : Word × Mat2 :=
  (shift ((r : ℤ) + 1) defectWord, constantMatrix ^ r)

def endSkeleton (r : ℕ) : Word × Mat2 :=
  (shift (-(r : ℤ)) defectWord,
    (cocycle fiberMap (shift (-(r : ℤ)) defectWord) (r + 1))⁻¹)

def limitingSkeleton : Set (Word × Mat2) :=
  closure (Set.range beginningSkeleton ∪ Set.range endSkeleton)

def skeletonBound : ℝ := constantPowerBound * (‖defectMatrix‖ + 2) + constantPowerBound

theorem defectApprox_norm (r : ℕ) : ‖defectApprox r‖ ≤ ‖defectMatrix‖ + 2 := by
  have hp : (1 / 400 : ℝ) ^ r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have he := defectApprox_error r
  have htri : ‖defectApprox r‖ ≤ ‖defectApprox r - defectMatrix‖ + ‖defectMatrix‖ := by
    simpa only [sub_add_cancel] using norm_add_le (defectApprox r - defectMatrix) defectMatrix
  linarith

theorem endSkeleton_norm (r : ℕ) : ‖(endSkeleton r).2‖ ≤ constantPowerBound * (‖defectMatrix‖ + 2) := by
  rw [endSkeleton, determinant_one_inverse_norm (fiberProduct_det _ _), ← defectApprox_unscale]
  exact (norm_mul_le _ _).trans
    (mul_le_mul (constant_power_norm r) (defectApprox_norm r) (norm_nonneg _) (by
      have h := constantPowerBound_ge_one
      linarith))

theorem limitingSkeleton_bounded {p : Word × Mat2} (hp : p ∈ limitingSkeleton) : ‖p.2‖ ≤ skeletonBound := by
  have hclosed : IsClosed {p : Word × Mat2 | ‖p.2‖ ≤ skeletonBound} :=
    isClosed_le continuous_snd.norm continuous_const
  apply closure_minimal ?_ hclosed hp
  rintro p (⟨r, rfl⟩ | ⟨r, rfl⟩)
  · have hK := constantPowerBound_ge_one
    have hn := norm_nonneg defectMatrix
    have hb := constant_power_norm r
    change ‖constantMatrix ^ r‖ ≤ skeletonBound
    dsimp [skeletonBound]
    nlinarith
  · have hb := endSkeleton_norm r
    have hK := constantPowerBound_ge_one
    exact hb.trans (by dsimp [skeletonBound]; linarith)

theorem limitingSkeleton_compact : IsCompact limitingSkeleton := by
  have hcontainer : IsCompact (Set.univ ×ˢ Metric.closedBall (0 : Mat2) skeletonBound) :=
    (isCompact_univ : IsCompact (Set.univ : Set Word)).prod (isCompact_closedBall _ _)
  apply hcontainer.of_isClosed_subset isClosed_closure
  intro p hp
  exact ⟨Set.mem_univ _, by simpa only [Metric.mem_closedBall, dist_zero_right] using limitingSkeleton_bounded hp⟩

theorem limitingSkeleton_nonempty : limitingSkeleton.Nonempty :=
  ⟨beginningSkeleton 0, subset_closure (Or.inl ⟨0, rfl⟩)⟩

theorem limitingSkeleton_det {p : Word × Mat2} (hp : p ∈ limitingSkeleton) : p.2.det = 1 := by
  have hclosed : IsClosed {p : Word × Mat2 | p.2.det = 1} :=
    isClosed_eq (continuous_snd.matrix_det) continuous_const
  apply closure_minimal ?_ hclosed hp
  rintro p (⟨r, rfl⟩ | ⟨r, rfl⟩)
  · change (constantMatrix ^ r).det = 1
    rw [Matrix.det_pow, fiberMap_det, one_pow]
  · change ((cocycle fiberMap (shift (-(r : ℤ)) defectWord) (r + 1))⁻¹).det = 1
    rw [Matrix.det_nonsing_inv, fiberProduct_det]
    simp

end HallRay

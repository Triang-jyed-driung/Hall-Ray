module

public import HallRay.PlaneNorm
public import Mathlib.Topology.Instances.Int

@[expose] public section
noncomputable section
namespace HallRay
namespace PlaneNorm

/-- A separate copy of the plane carrying the specified arbitrary norm. -/
def Space (_N : PlaneNorm) : Type := Point

instance (N : PlaneNorm) : AddCommGroup N.Space := inferInstanceAs (AddCommGroup Point)
instance (N : PlaneNorm) : Module ℝ N.Space := inferInstanceAs (Module ℝ Point)
instance (N : PlaneNorm) : FiniteDimensional ℝ N.Space := inferInstanceAs (FiniteDimensional ℝ Point)
instance (N : PlaneNorm) : Norm N.Space := ⟨N.value⟩

theorem spaceCore (N : PlaneNorm) : NormedSpace.Core ℝ N.Space where
  norm_nonneg := N.nonneg
  norm_smul r u := by exact (Real.norm_eq_abs r) ▸ N.smul_eq r u
  norm_triangle := N.add_le
  norm_eq_zero_iff := N.eq_zero_iff

instance (N : PlaneNorm) : NormedAddCommGroup N.Space := NormedAddCommGroup.ofCore (N.spaceCore)
instance (N : PlaneNorm) : NormedSpace ℝ N.Space := NormedSpace.ofCore (N.spaceCore)

theorem space_dist (N : PlaneNorm) (u v : N.Space) : dist u v = N.value (u - v) := by
  rw [dist_eq_norm]
  rfl

def spaceEquiv (N : PlaneNorm) : Point ≃ₗ[ℝ] N.Space := LinearEquiv.refl ℝ Point

def spaceHomeomorph (N : PlaneNorm) : Point ≃ₜ N.Space := N.spaceEquiv.toContinuousLinearEquiv.toHomeomorph

theorem integerPoint_closedEmbedding : Topology.IsClosedEmbedding integerPoint :=
  Int.isClosedEmbedding_coe_real.prodMap Int.isClosedEmbedding_coe_real

def spaceIntegerPoint (N : PlaneNorm) : ℤ × ℤ → N.Space := fun p => integerPoint p

theorem spaceIntegerPoint_closed (N : PlaneNorm) :
    IsClosed (Set.range N.spaceIntegerPoint) := by
  have h := N.spaceHomeomorph.isClosedEmbedding.comp integerPoint_closedEmbedding
  exact h.isClosed_range

/-- A nearest integer vector exists for every plane norm, including nonsmooth ones. -/
theorem nearest_integer (N : PlaneNorm) (x : Point) :
    ∃ p : ℤ × ℤ, ∀ p' : ℤ × ℤ, N.value (x - integerPoint p) ≤ N.value (x - integerPoint p') := by
  let S : Set N.Space := Set.range N.spaceIntegerPoint
  have hS : IsClosed S := N.spaceIntegerPoint_closed
  obtain ⟨y, ⟨p, hp⟩, hy⟩ := hS.exists_infDist_eq_dist (show S.Nonempty from ⟨N.spaceIntegerPoint (0, 0), ⟨(0, 0), rfl⟩⟩)
    (N.spaceEquiv x)
  refine ⟨p, fun p' => ?_⟩
  have h := Metric.infDist_le_dist_of_mem (x := (N.spaceEquiv x)) (show N.spaceIntegerPoint p' ∈ S from ⟨p', rfl⟩)
  rw [hy] at h
  rw [← hp] at h
  rw [N.space_dist, N.space_dist] at h
  exact h

end PlaneNorm

open scoped ENNReal

theorem torusError_attained (N : PlaneNorm) (x : Point) (q : ℕ) :
    ∃ p : ℤ × ℤ, torusError N x q = ENNReal.ofReal (N.value ((q : ℝ) • x - integerPoint p)) := by
  obtain ⟨p, hp⟩ := N.nearest_integer ((q : ℝ) • x)
  refine ⟨p, le_antisymm (iInf_le _ p) ?_⟩
  exact le_iInf fun p' => ENNReal.ofReal_le_ofReal (hp p')

theorem torusError_pos (N : PlaneNorm) {x : Point} (hx : ¬RationalPair x) {q : ℕ} (hq : 0 < q) :
    0 < torusError N x q := by
  obtain ⟨p, hp⟩ := torusError_attained N x q
  rw [hp, ENNReal.ofReal_pos]
  apply lt_of_le_of_ne (N.nonneg _)
  intro he
  have hz := (N.eq_zero_iff _).mp he.symm
  exact hx ⟨q, hq, p, sub_eq_zero.mp hz⟩

theorem torusError_ne_top (N : PlaneNorm) (x : Point) (q : ℕ) : torusError N x q ≠ ⊤ := by
  obtain ⟨p, hp⟩ := torusError_attained N x q
  rw [hp]
  exact ENNReal.ofReal_ne_top

end HallRay

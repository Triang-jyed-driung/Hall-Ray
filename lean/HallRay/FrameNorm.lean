module

public import HallRay.NearestInteger
public import HallRay.Suspension

@[expose] public section
noncomputable section
namespace HallRay
namespace PlaneNorm

/-- The ambient three-dimensional norm is max(|first coordinate|, plane norm). -/
abbrev FrameSpace (N : PlaneNorm) := ℝ × N.Space

def frameIntegerPoint (N : PlaneNorm) (w : ℤ × (ℤ × ℤ)) : N.FrameSpace :=
  ((w.1 : ℝ), N.spaceIntegerPoint w.2)

theorem spaceIntegerPoint_closedEmbedding (N : PlaneNorm) :
    Topology.IsClosedEmbedding N.spaceIntegerPoint :=
  N.spaceHomeomorph.isClosedEmbedding.comp integerPoint_closedEmbedding

theorem frameIntegerPoint_closedEmbedding (N : PlaneNorm) :
    Topology.IsClosedEmbedding N.frameIntegerPoint :=
  Int.isClosedEmbedding_coe_real.prodMap N.spaceIntegerPoint_closedEmbedding

@[simp] theorem frameIntegerPoint_zero (N : PlaneNorm) : N.frameIntegerPoint 0 = 0 := by
  apply Prod.ext
  · simp [frameIntegerPoint]
  · simp [frameIntegerPoint, spaceIntegerPoint, integerPoint]
    change N.spaceEquiv ((0, 0) : Point) = 0
    rw [Prod.mk_zero_zero]
    exact map_zero _

theorem frameIntegerPoint_ne_zero (N : PlaneNorm) {w : ℤ × (ℤ × ℤ)} (hw : w ≠ 0) :
    N.frameIntegerPoint w ≠ 0 := by
  rw [← frameIntegerPoint_zero N]
  exact fun h => hw (N.frameIntegerPoint_closedEmbedding.injective h)

/-- Linear coordinates identify matrices with operators for the product norm. -/
def frameCoordinates (N : PlaneNorm) : (Fin 3 → ℝ) ≃ₗ[ℝ] N.FrameSpace where
  toFun x := (x 0, N.spaceEquiv (x 1, x 2))
  invFun x := ![x.1, x.2.1, x.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv x := by rcases x with ⟨a, b⟩; rfl
  map_add' x y := by
    apply Prod.ext
    · rfl
    · exact map_add N.spaceEquiv (x 1, x 2) (y 1, y 2)
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · exact map_smul N.spaceEquiv r (x 1, x 2)

def frameCoordinatesContinuous (N : PlaneNorm) : (Fin 3 → ℝ) ≃L[ℝ] N.FrameSpace :=
  N.frameCoordinates.toContinuousLinearEquiv

/-- An invertible matrix acting on the normed three-dimensional space. -/
def frameChange (N : PlaneNorm) (A : Mat3) (hA : A.det ≠ 0) : N.FrameSpace ≃L[ℝ] N.FrameSpace :=
  ((N.frameCoordinates.symm.trans
    (A.toLinearEquiv' (A.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hA)))).trans
      N.frameCoordinates).toContinuousLinearEquiv

/-- Removing the zero vector leaves a closed set, also after any invertible frame change. -/
theorem nonzero_frame_lattice_closed (N : PlaneNorm) (e : N.FrameSpace ≃L[ℝ] N.FrameSpace) :
    IsClosed ((fun w => e (N.frameIntegerPoint w)) '' {w | w ≠ 0}) := by
  have he := e.toHomeomorph.isClosedEmbedding.comp N.frameIntegerPoint_closedEmbedding
  exact he.isClosedMap _ (isClosed_discrete _)

/-- Every invertible frame has a shortest nonzero lattice vector for the chosen norm. -/
theorem shortest_frame_vector (N : PlaneNorm) (e : N.FrameSpace ≃L[ℝ] N.FrameSpace) :
    ∃ w : ℤ × (ℤ × ℤ), w ≠ 0 ∧ 0 < ‖e (N.frameIntegerPoint w)‖ ∧
      ∀ v : ℤ × (ℤ × ℤ), v ≠ 0 → ‖e (N.frameIntegerPoint w)‖ ≤ ‖e (N.frameIntegerPoint v)‖ := by
  let S : Set N.FrameSpace := (fun w => e (N.frameIntegerPoint w)) '' {w | w ≠ 0}
  have hS : IsClosed S := N.nonzero_frame_lattice_closed e
  have hne : S.Nonempty := ⟨e (N.frameIntegerPoint (1, (0, 0))),
    ⟨(1, (0, 0)), by simp, rfl⟩⟩
  obtain ⟨y, ⟨w, hw, hy⟩, hmin⟩ := hS.exists_infDist_eq_dist hne 0
  refine ⟨w, hw, norm_pos_iff.mpr ?_, fun v hv => ?_⟩
  · exact fun h => N.frameIntegerPoint_ne_zero hw (e.injective (by simpa using h))
  · have h := Metric.infDist_le_dist_of_mem (x := (0 : N.FrameSpace))
      (show e (N.frameIntegerPoint v) ∈ S from ⟨v, hv, rfl⟩)
    rw [hmin, ← hy, dist_zero_left, dist_zero_left] at h
    exact h

def frameVector (N : PlaneNorm) (A : Mat3) (w : ℤ × (ℤ × ℤ)) : N.FrameSpace :=
  N.frameCoordinates (A.mulVec ![(w.1 : ℝ), (w.2.1 : ℝ), (w.2.2 : ℝ)])

theorem frameChange_integerPoint (N : PlaneNorm) (A : Mat3) (hA : A.det ≠ 0)
    (w : ℤ × (ℤ × ℤ)) :
    N.frameChange A hA (N.frameIntegerPoint w) = N.frameVector A w := by
  simp only [frameChange]
  rfl

/-- The shortest-vector assertion in the matrix coordinates used by the paper. -/
theorem shortest_matrix_vector (N : PlaneNorm) (A : Mat3) (hA : A.det ≠ 0) :
    ∃ w : ℤ × (ℤ × ℤ), w ≠ 0 ∧ 0 < ‖N.frameVector A w‖ ∧
      ∀ v : ℤ × (ℤ × ℤ), v ≠ 0 → ‖N.frameVector A w‖ ≤ ‖N.frameVector A v‖ := by
  simpa only [frameChange_integerPoint] using N.shortest_frame_vector (N.frameChange A hA)

end PlaneNorm
end HallRay

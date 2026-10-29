module

public import HallRay.ReturnContinuity
public import HallRay.CircularFibers
public import HallRay.SystoleContinuity

@[expose] public section
noncomputable section
namespace HallRay

/-- A compact parameter interval for one flight between consecutive returns. -/
abbrev FlightParameter := Set.Icc (0 : ℝ) 1

/-- Marked representatives of a periodic-code orbit closure, one return position at a time. -/
def periodicFrame (n : ℕ) (j : Fin (n + 1)) (p : Real.Angle × FlightParameter) : Mat3 :=
  let z := shift (j.val : ℤ) (periodicWord n)
  flow ((p.2 : ℝ) * roof z) * codedChart z
    (ellipticCircle (periodMatrix n) p.1 * cocycle fiberMap (periodicWord n) j.val)

@[fun_prop] theorem periodicFrame_continuous (n : ℕ) (j : Fin (n + 1)) :
    Continuous (periodicFrame n j) := by
  have ht : Continuous (fun p : Real.Angle × FlightParameter => (p.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hc := (ellipticCircle_continuous (periodMatrix n)).comp
    (continuous_fst : Continuous (fun p : Real.Angle × FlightParameter => p.1))
  unfold periodicFrame
  apply Continuous.mul
  · exact flow_continuous.comp (ht.mul_const _)
  · exact (codedChart_fixed_continuous _).comp (hc.mul continuous_const)

def periodicFrames (n : ℕ) : Set Mat3 := ⋃ j : Fin (n + 1), Set.range (periodicFrame n j)

theorem periodicFrames_compact (n : ℕ) : IsCompact (periodicFrames n) :=
  isCompact_iUnion (fun j => isCompact_range (periodicFrame_continuous n j))

theorem periodicFrames_nonempty (n : ℕ) : (periodicFrames n).Nonempty := by
  have hf : Nonempty FlightParameter := ⟨⟨0, by norm_num⟩⟩
  exact Set.nonempty_iUnion.mpr ⟨⟨0, by omega⟩, Set.range_nonempty _⟩

theorem periodicFrame_det (n : ℕ) (h : Admissible n) (j : Fin (n + 1))
    (p : Real.Angle × FlightParameter) : (periodicFrame n j p).det = 1 := by
  unfold periodicFrame
  rw [Matrix.det_mul, flow_det, one_mul]
  apply codedChart_det
  rw [Matrix.det_mul, ellipticCircle_det (periodMatrix_det n) h,
    fiberProduct_det, one_mul]

theorem periodicFrames_det (n : ℕ) (h : Admissible n) {A : Mat3}
    (hA : A ∈ periodicFrames n) : A.det = 1 := by
  obtain ⟨j, p, rfl⟩ := Set.mem_iUnion.mp hA
  exact periodicFrame_det n h j p

/-- The inverse systole has a finite attained maximum on every admissible periodic family. -/
theorem periodic_height_maximum (N : PlaneNorm) (n : ℕ) (h : Admissible n) :
    ∃ A ∈ periodicFrames n, frameHeight N A ≠ ⊤ ∧
      ∀ B ∈ periodicFrames n, frameHeight N B ≤ frameHeight N A := by
  have hcont : ContinuousOn (frameHeight N) (periodicFrames n) := by
    intro A hA
    exact (frameHeight_continuousAt N A (by rw [periodicFrames_det n h hA]; norm_num)).continuousWithinAt
  obtain ⟨A, hA, hmax⟩ := (periodicFrames_compact n).exists_isMaxOn
    (periodicFrames_nonempty n) hcont
  exact ⟨A, hA, frameHeight_ne_top N A (by rw [periodicFrames_det n h hA]; norm_num), hmax⟩

end HallRay

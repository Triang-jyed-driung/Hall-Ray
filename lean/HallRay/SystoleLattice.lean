module

public import HallRay.SystoleContinuity
public import HallRay.Lattices

@[expose] public section
noncomputable section
namespace HallRay
namespace PlaneNorm

@[simp] theorem frameVector_zero (N : PlaneNorm) (A : Mat3) : N.frameVector A 0 = 0 := by
  have hz : (![((0 : ℤ) : ℝ), ((0 : ℤ) : ℝ), ((0 : ℤ) : ℝ)] : Fin 3 → ℝ) = 0 := by
    ext i
    fin_cases i <;> simp
  simp only [frameVector, Prod.fst_zero, Prod.snd_zero, hz, Matrix.mulVec_zero, map_zero]

theorem frameVector_ne_zero (N : PlaneNorm) (A : Mat3) (hA : A.det ≠ 0)
    {w : ℤ × (ℤ × ℤ)} (hw : w ≠ 0) : N.frameVector A w ≠ 0 := by
  rw [← N.frameChange_integerPoint A hA w]
  intro h
  apply N.frameIntegerPoint_ne_zero hw
  exact (N.frameChange A hA).injective (by simpa using h)

/-- Equality of unmarked lattices transports every nonzero marked vector. -/
theorem frameVector_transport (N : PlaneNorm) (A B : Mat3) (hA : A.det ≠ 0)
    (hAB : frameLattice A = frameLattice B) {w : ℤ × (ℤ × ℤ)} (hw : w ≠ 0) :
    ∃ v : ℤ × (ℤ × ℤ), v ≠ 0 ∧ N.frameVector B v = N.frameVector A w := by
  let wi : Fin 3 → ℤ := ![w.1, w.2.1, w.2.2]
  have hcast : castVector wi = ![(w.1 : ℝ), (w.2.1 : ℝ), (w.2.2 : ℝ)] := by
    ext i
    fin_cases i <;> rfl
  have hmem : A.mulVec (castVector wi) ∈ frameLattice B := by
    rw [← hAB]
    exact ⟨wi, rfl⟩
  obtain ⟨vi, hvi⟩ := hmem
  let v : ℤ × (ℤ × ℤ) := (vi 0, (vi 1, vi 2))
  have hcastv : castVector vi = ![(v.1 : ℝ), (v.2.1 : ℝ), (v.2.2 : ℝ)] := by
    ext i
    fin_cases i <;> rfl
  have heq : N.frameVector B v = N.frameVector A w := by
    have hh := congrArg N.frameCoordinates hvi
    simpa only [hcast, hcastv, frameVector] using hh
  refine ⟨v, ?_, heq⟩
  intro hv
  rw [hv, frameVector_zero] at heq
  exact N.frameVector_ne_zero A hA hw heq.symm

end PlaneNorm

/-- Systole is independent of the chosen integral marking. -/
theorem frameSystole_of_lattice_eq (N : PlaneNorm) (A B : Mat3)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hAB : frameLattice A = frameLattice B) :
    frameSystole N A = frameSystole N B := by
  have hle (X Y : Mat3) (hX : X.det ≠ 0) (hXY : frameLattice X = frameLattice Y) :
      frameSystole N Y ≤ frameSystole N X := by
    apply le_iInf
    intro w
    obtain ⟨v, hv, heq⟩ := N.frameVector_transport X Y hX hXY w.property
    have hh := iInf_le (fun v : {v : ℤ × (ℤ × ℤ) // v ≠ 0} =>
      ENNReal.ofReal ‖N.frameVector Y v.val‖) ⟨v, hv⟩
    simpa only [heq, frameSystole] using hh
  exact le_antisymm (hle B A hB hAB.symm) (hle A B hA hAB)

theorem frameHeight_of_lattice_eq (N : PlaneNorm) (A B : Mat3)
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (hAB : frameLattice A = frameLattice B) :
    frameHeight N A = frameHeight N B := by
  unfold frameHeight
  rw [frameSystole_of_lattice_eq N A B hA hB hAB]

end HallRay

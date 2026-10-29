module

public import HallRay.Suspension
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
noncomputable section
open scoped Matrix
namespace HallRay

def castVector (w : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (w i : ℝ)

/-- The lattice specified by the columns of a marked frame. -/
def frameLattice (G : Mat3) : Set (Fin 3 → ℝ) :=
  Set.range (fun w : Fin 3 → ℤ => G *ᵥ castVector w)

theorem castVector_mulVec (A : Matrix (Fin 3) (Fin 3) ℤ) (w : Fin 3 → ℤ) :
    castVector (A *ᵥ w) = A.map (Int.castRingHom ℝ) *ᵥ castVector w := by
  ext i
  simp [castVector, Matrix.mulVec, dotProduct]

theorem frameLattice_marking (G : Mat3) (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.det = 1) :
    frameLattice (G * A.map (Int.castRingHom ℝ)) = frameLattice G := by
  have hs : Function.Surjective A.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det A).mpr (by rw [hA]; exact isUnit_one))
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨A *ᵥ w, ?_⟩
    dsimp only
    rw [castVector_mulVec, Matrix.mulVec_mulVec]
  · rintro ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := hs w
    refine ⟨v, ?_⟩
    dsimp only
    rw [← Matrix.mulVec_mulVec, ← castVector_mulVec, hv]

theorem frameLattice_mul_image (G A : Mat3) :
    frameLattice (G * A) = G.mulVec '' frameLattice A := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨A *ᵥ castVector w, ⟨w, rfl⟩, Matrix.mulVec_mulVec _ _ _⟩
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, (Matrix.mulVec_mulVec _ _ _).symm⟩

def integerMarking (z : Word) : Matrix (Fin 3) (Fin 3) ℤ := gamma (z 0)

theorem markingProduct_map (z : Word) (n : ℕ) :
    cocycle realMarking z n = (cocycle integerMarking z n).map (Int.castRingHom ℝ) := by
  induction n with
  | zero => simp [Matrix.map_one]
  | succ n ih => simp only [cocycle_succ, ih, Matrix.map_mul]; rfl

theorem integerMarkingProduct_det (z : Word) (n : ℕ) :
    (cocycle integerMarking z n).det = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [cocycle_succ, Matrix.det_mul, ih, integerMarking, gamma_det]

/-- Integral changes of marking do not change the represented lattice. -/
theorem symbolic_lattice_return (z : Word) (E : Mat2) (n : ℕ) :
    frameLattice (flow (timeSum z n) * codedChart z E) =
      frameLattice (codedChart (shift (n : ℤ) z) (E * cocycle fiberMap z n)) := by
  calc
    _ = frameLattice (flow (timeSum z n) * codedChart z E * cocycle realMarking z n) := by
      rw [markingProduct_map, frameLattice_marking _ _ (integerMarkingProduct_det z n)]
    _ = _ := by rw [symbolic_iterated_return]

/-- The forward suspension factor formula, including the complete flow segment. -/
theorem symbolic_lattice_factor (z : Word) (E : Mat2) (n : ℕ) (r : ℝ) :
    frameLattice (flow (timeSum z n + r) * codedChart z E) =
      frameLattice (flow r * codedChart (shift (n : ℤ) z) (E * cocycle fiberMap z n)) := by
  rw [add_comm (timeSum z n), flow_add, Matrix.mul_assoc, frameLattice_mul_image,
    symbolic_lattice_return, ← frameLattice_mul_image]

end HallRay

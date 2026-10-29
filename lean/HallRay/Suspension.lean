module

public import HallRay.ReturnMap

@[expose] public section
noncomputable section
open scoped BigOperators
namespace HallRay

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℝ

def codedChart (z : Word) (E : Mat2) : Mat3 := chart (futureCode z) (pastCode z) E

def fiberMap (z : Word) : Mat2 := fiber (z 0) (futureCode (shift 1 z))

def roof (z : Word) : ℝ := returnTime (z 0) (futureCode (shift 1 z)) (pastCode z)

def realMarking (z : Word) : Mat3 := (gamma (z 0)).map (Int.castRingHom ℝ)

theorem roof_gt_one (z : Word) : 1 < roof z :=
  returnTime_gt_one _ (futureCode_mem _) (pastCode_mem _)

theorem fiberMap_det (z : Word) : (fiberMap z).det = 1 := fiber_det _ (futureCode_mem _)

theorem codedChart_det (z : Word) {E : Mat2} (hE : E.det = 1) : (codedChart z E).det = 1 :=
  chart_det (futureCode_mem _) (pastCode_mem _) hE

/-- The symbolic marked return formula, with both coding coordinates constructed. -/
theorem symbolic_marked_return (z : Word) (E : Mat2) :
    flow (roof z) * codedChart z E * realMarking z =
      codedChart (shift 1 z) (E * fiberMap z) := by
  have h := marked_return (z 0) (futureCode_mem (shift 1 z)) (pastCode_mem z) E
  simpa only [roof, codedChart, realMarking, fiberMap,
    ← futureCode_recurrence z, ← pastCode_recurrence z] using h

def timeSum (z : Word) (n : ℕ) : ℝ := ∑ j ∈ Finset.range n, roof (shift (j : ℤ) z)

@[simp] theorem timeSum_zero (z : Word) : timeSum z 0 = 0 := by simp [timeSum]

@[simp] theorem timeSum_succ (z : Word) (n : ℕ) :
    timeSum z (n + 1) = timeSum z n + roof (shift (n : ℤ) z) := by
  simp [timeSum, Finset.sum_range_succ]

theorem timeSum_ge (z : Word) (n : ℕ) : (n : ℝ) ≤ timeSum z n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [timeSum_succ, Nat.cast_add, Nat.cast_one]
    have := roof_gt_one (shift (n : ℤ) z)
    linarith

theorem timeSum_add (z : Word) (k l : ℕ) :
    timeSum z (k + l) = timeSum z k + timeSum (shift (k : ℤ) z) l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Nat.add_succ, timeSum_succ, timeSum_succ, ih]
    simp only [shift_add, Nat.cast_add]
    rw [add_comm (l : ℤ) (k : ℤ)]
    ring

theorem markingProduct_det (z : Word) (n : ℕ) : (cocycle realMarking z n).det = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cocycle_succ, Matrix.det_mul, ih, one_mul]
    unfold realMarking
    have h := (Int.castRingHom ℝ).map_det (gamma (shift (n : ℤ) z 0))
    simpa only [RingHom.mapMatrix_apply, gamma_det, map_one] using h.symm

theorem fiberProduct_det (z : Word) (n : ℕ) : (cocycle fiberMap z n).det = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [cocycle_succ, Matrix.det_mul, ih, fiberMap_det, one_mul]

/-- Iterating the actual matrix identity gives the suspension factor formula.
The integral product on the left represents the accumulated marking changes. -/
theorem symbolic_iterated_return (z : Word) (E : Mat2) (n : ℕ) :
    flow (timeSum z n) * codedChart z E * cocycle realMarking z n =
      codedChart (shift (n : ℤ) z) (E * cocycle fiberMap z n) := by
  induction n with
  | zero => simp [flow_zero]
  | succ n ih =>
    rw [timeSum_succ, cocycle_succ, cocycle_succ, Nat.cast_add, Nat.cast_one]
    calc
      _ = flow (roof (shift (n : ℤ) z)) *
          (flow (timeSum z n) * codedChart z E * cocycle realMarking z n) *
            realMarking (shift (n : ℤ) z) := by
        rw [add_comm (timeSum z n), flow_add]
        simp only [Matrix.mul_assoc]
      _ = flow (roof (shift (n : ℤ) z)) *
          codedChart (shift (n : ℤ) z) (E * cocycle fiberMap z n) *
            realMarking (shift (n : ℤ) z) := by rw [ih]
      _ = codedChart (shift (1 : ℤ) (shift (n : ℤ) z))
          ((E * cocycle fiberMap z n) * fiberMap (shift (n : ℤ) z)) :=
        symbolic_marked_return _ _
      _ = _ := by rw [shift_add, add_comm (1 : ℤ)]; simp only [Matrix.mul_assoc]

end HallRay

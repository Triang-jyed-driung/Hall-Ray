module

public import HallRay.ReturnAlgebra
public import HallRay.Coding
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section
noncomputable section
namespace HallRay

def chartScale (u v : Point) : ℝ := Real.exp (-(Real.log (1 + dot v u)) / 3)

def blockFiber (E : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, E 0 0, E 0 1; 0, E 1 0, E 1 1]

def chart (u v : Point) (E : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  chartScale u v • (blockFiber E * rawChart u v)

def flow (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.exp (-2 * t), 0, 0; 0, Real.exp t, 0; 0, 0, Real.exp t]

/-- A simplified expression for the return time from Proposition 3.1. -/
def returnTime (s : Symbol) (u v : Point) : ℝ := Real.log (d s u) / 6 + Real.log (e s v) / 3

theorem chartScale_pos (u v : Point) : 0 < chartScale u v := Real.exp_pos _

theorem chartScale_cube {u v : Point} (hu : U u) (hv : V v) :
    chartScale u v ^ 3 * (1 + dot v u) = 1 := by
  have hA : 0 < 1 + dot v u := by have := chart_positive hu hv; linarith
  have hp : chartScale u v ^ 3 = Real.exp (-Real.log (1 + dot v u)) := by
    unfold chartScale
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hp, Real.exp_neg, Real.exp_log hA, inv_mul_cancel₀ (ne_of_gt hA)]

theorem blockFiber_det (E : Matrix (Fin 2) (Fin 2) ℝ) : (blockFiber E).det = E.det := by
  simp [blockFiber, Matrix.det_fin_three, Matrix.det_fin_two]

theorem chart_det {u v : Point} (hu : U u) (hv : V v)
    {E : Matrix (Fin 2) (Fin 2) ℝ} (hE : E.det = 1) : (chart u v E).det = 1 := by
  simp only [chart, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, blockFiber_det,
    rawChart_det, hE, one_mul]
  exact chartScale_cube hu hv

theorem flow_det (t : ℝ) : (flow t).det = 1 := by
  simp [flow, Matrix.det_fin_three]
  rw [← Real.exp_add, ← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

theorem flow_add (t r : ℝ) : flow (t + r) = flow t * flow r := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flow, Matrix.mul_apply, Fin.sum_univ_succ, Real.exp_add, mul_add]

theorem flow_zero : flow 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [flow]

theorem returnTime_gt_one (s : Symbol) {u v : Point} (hu : U u) (hv : V v) :
    1 < returnTime s u v := by
  have hexp : Real.exp 2 < 9 := by
    have := Real.exp_one_lt_three
    have hp := Real.exp_pos 1
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hd : 2 < Real.log (d s u) := by
    apply (Real.lt_log_iff_exp_lt (d_pos s hu)).mpr
    linarith [(d_bounds s hu).1]
  have he : 2 < Real.log (e s v) := by
    apply (Real.lt_log_iff_exp_lt (e_pos s hv)).mpr
    linarith [(e_bounds s hv).1]
  dsimp [returnTime]
  linarith

theorem cross_denominator_identity (s : Symbol) {u v : Point} (hu : U u) (hv : V v) :
    e s v * (1 + dot (psi s v) u) = d s u * (1 + dot v (phi s u)) := by
  have hd : d s u ≠ 0 := ne_of_gt (d_pos s hu)
  have he : e s v ≠ 0 := ne_of_gt (e_pos s hv)
  dsimp [dot, phi, psi]
  field_simp
  dsimp [d, e]
  ring

theorem return_log_relation (s : Symbol) {u v : Point} (hu : U u) (hv : V v) :
    Real.log (e s v) + Real.log (1 + dot (psi s v) u) =
      Real.log (d s u) + Real.log (1 + dot v (phi s u)) := by
  have hA : 0 < 1 + dot v (phi s u) := by
    have := chart_positive (phi_mem s hu) hv
    linarith
  have hB : 0 < 1 + dot (psi s v) u := by
    have := chart_positive hu (psi_mem s hv)
    linarith
  have h := congrArg Real.log (cross_denominator_identity s hu hv)
  rwa [Real.log_mul (ne_of_gt (e_pos s hv)) (ne_of_gt hB),
    Real.log_mul (ne_of_gt (d_pos s hu)) (ne_of_gt hA)] at h

theorem return_upper_scalar (s : Symbol) {u v : Point} (hu : U u) (hv : V v) :
    Real.exp (-2 * returnTime s u v) * chartScale (phi s u) v * e s v =
      chartScale u (psi s v) := by
  have hl := return_log_relation s hu hv
  nth_rw 1 [← Real.exp_log (e_pos s hv)]
  unfold chartScale
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  dsimp [returnTime]
  linarith

theorem return_lower_scalar (s : Symbol) {u v : Point} (hu : U u) (hv : V v) :
    Real.exp (returnTime s u v) * chartScale (phi s u) v =
      chartScale u (psi s v) * Real.sqrt (d s u) := by
  have hl := return_log_relation s hu hv
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (d_pos s hu)]
  unfold chartScale
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  dsimp [returnTime]
  linarith

@[simp] theorem blockFiber_one : blockFiber (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [blockFiber]

theorem blockFiber_mul (E F : Matrix (Fin 2) (Fin 2) ℝ) :
    blockFiber (E * F) = blockFiber E * blockFiber F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockFiber, Matrix.mul_apply, Fin.sum_univ_succ]

theorem flow_commutes_block (t : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    flow t * blockFiber E = blockFiber E * flow t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockFiber, flow, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The exact normalized marked return, first with identity fiber. -/
theorem marked_return_one (s : Symbol) {u v : Point} (hu : U u) (hv : V v) :
    flow (returnTime s u v) * chart (phi s u) v 1 * (gamma s).map (Int.castRingHom ℝ) =
      chart u (psi s v) (fiber s u) := by
  have hup := return_upper_scalar s hu hv
  simp only [neg_mul] at hup
  have hlo := return_lower_scalar s hu hv
  have hd : d s u ≠ 0 := ne_of_gt (d_pos s hu)
  have hs : Real.sqrt (d s u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (d_pos s hu))
  have hsq : Real.sqrt (d s u) ^ 2 = d s u := Real.sq_sqrt (d_pos s hu).le
  have hlod : chartScale (phi s u) v * Real.exp (returnTime s u v) * Real.sqrt (d s u) =
      chartScale u (psi s v) * d s u := by
    calc
      _ = (Real.exp (returnTime s u v) * chartScale (phi s u) v) * Real.sqrt (d s u) := by ring
      _ = (chartScale u (psi s v) * Real.sqrt (d s u)) * Real.sqrt (d s u) := by rw [hlo]
      _ = chartScale u (psi s v) * Real.sqrt (d s u) ^ 2 := by ring
      _ = _ := by rw [hsq]
  simp only [chart, blockFiber_one, one_mul, Matrix.mul_smul, smul_mul_assoc]
  rw [Matrix.mul_assoc, raw_marked_return s hu hv]
  have hblock : chartScale (phi s u) v • (flow (returnTime s u v) * rawReturn s u v) =
      chartScale u (psi s v) • blockFiber (fiber s u) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [flow, rawReturn, blockFiber, fiber, fiberNumerator] <;>
      field_simp
    all_goals first
      | linear_combination hup
      | linear_combination (10 - sign s * u.2) * hlod
      | linear_combination (sign s * (u.1 - 1)) * hlod
      | linear_combination sign s * hlod
      | linear_combination hlod
  simpa only [smul_mul_assoc, Matrix.mul_assoc] using
    congrArg (fun B => B * rawChart u (psi s v)) hblock

/-- Proposition 3.1's marked return identity for an arbitrary fiber matrix. -/
theorem marked_return (s : Symbol) {u v : Point} (hu : U u) (hv : V v)
    (E : Matrix (Fin 2) (Fin 2) ℝ) :
    flow (returnTime s u v) * chart (phi s u) v E * (gamma s).map (Int.castRingHom ℝ) =
      chart u (psi s v) (E * fiber s u) := by
  have hf (u v : Point) : chart u v E = blockFiber E * chart u v 1 := by
    simp [chart]
  rw [hf]
  calc
    _ = blockFiber E * (flow (returnTime s u v) * chart (phi s u) v 1 *
        (gamma s).map (Int.castRingHom ℝ)) := by
      rw [← Matrix.mul_assoc (flow _) (blockFiber E), flow_commutes_block]
      simp only [Matrix.mul_assoc]
    _ = blockFiber E * chart u (psi s v) (fiber s u) := by rw [marked_return_one s hu hv]
    _ = chart u (psi s v) (E * fiber s u) := by
      simp [chart, blockFiber_mul, Matrix.mul_assoc]

end HallRay

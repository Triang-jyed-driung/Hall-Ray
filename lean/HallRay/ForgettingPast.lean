module

public import HallRay.NearIdentityHeight

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal
namespace HallRay

/-- The stable upper-unipotent factor of a chart. -/
def upperFrame (v : Point) : Mat3 := !![1, v.1, v.2; 0, 1, 0; 0, 0, 1]

def chartTime (u v : Point) : ℝ := -Real.log (1 + dot v u) / 3

def stableRow (u v : Point) : Point := (1 + dot v u)⁻¹ • v

@[simp] theorem upperFrame_zero : upperFrame 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperFrame]

@[fun_prop] theorem upperFrame_continuous : Continuous upperFrame := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp [upperFrame] <;> fun_prop

theorem chart_stable_factor {u v : Point} (hu : U u) (hv : V v) :
    chart u v 1 = flow (chartTime u v) * upperFrame (stableRow u v) * rawChart u 0 := by
  have hpos : 0 < 1 + dot v u := by have h := chart_positive hu hv; linarith
  have hne : 1 + (v.1 * u.1 + v.2 * u.2) ≠ 0 := ne_of_gt hpos
  have he : Real.exp (chartTime u v) = chartScale u v := rfl
  have htop : Real.exp (-2 * chartTime u v) = chartScale u v * (1 + dot v u) := by
    calc
      _ = Real.exp (chartTime u v + Real.log (1 + dot v u)) := by congr 1; unfold chartTime; ring
      _ = _ := by rw [Real.exp_add, he, Real.exp_log hpos]
  have htop' : Real.exp (-(2 * chartTime u v)) = chartScale u v * (1 + dot v u) := by
    simpa only [neg_mul] using htop
  rw [chart, blockFiber_one, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flow, upperFrame, stableRow, rawChart, Matrix.mul_apply, Fin.sum_univ_succ, he, htop', dot] <;>
    field_simp
  ring

theorem flow_upperFrame (t : ℝ) (v : Point) :
    flow t * upperFrame v = upperFrame (Real.exp (-3 * t) • v) * flow t := by
  have hex : Real.exp (-3 * t) * Real.exp t = Real.exp (-2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm (x : ℝ) : Real.exp (-2 * t) * x = (Real.exp (-3 * t) * x) * Real.exp t := by rw [← hex]; ring
  simp only [neg_mul] at hm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flow, upperFrame, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith [hm v.1, hm v.2]

def forgettingMultiplier (z : Word) (t : ℝ) : Mat3 :=
  upperFrame (Real.exp (-3 * (t + chartTime (futureCode z) (pastCode z))) •
    stableRow (futureCode z) (pastCode z))

theorem forgettingMultiplier_tendsto (z : Word) : Tendsto (forgettingMultiplier z) atTop (𝓝 1) := by
  have ht : Tendsto (fun t : ℝ => 3 * (t + chartTime (futureCode z) (pastCode z))) atTop atTop :=
    (tendsto_atTop_add_const_right atTop _ tendsto_id).const_mul_atTop (by norm_num)
  have he : Tendsto (fun t : ℝ => Real.exp (-3 * (t + chartTime (futureCode z) (pastCode z)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hv := he.smul_const (stableRow (futureCode z) (pastCode z))
  simp only [zero_smul] at hv
  have hh := upperFrame_continuous.continuousAt.tendsto.comp hv
  unfold forgettingMultiplier
  simpa only [Function.comp_def, upperFrame_zero] using hh

theorem coded_flow_forgetting_factor (z : Word) (t : ℝ) :
    flow t * codedChart z 1 = forgettingMultiplier z t *
      (flow (t + chartTime (futureCode z) (pastCode z)) * rawChart (futureCode z) 0) := by
  unfold codedChart
  rw [chart_stable_factor (futureCode_mem z) (pastCode_mem z)]
  calc
    _ = flow (t + chartTime (futureCode z) (pastCode z)) *
        upperFrame (stableRow (futureCode z) (pastCode z)) * rawChart (futureCode z) 0 := by
      rw [flow_add]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [flow_upperFrame]; simp only [Matrix.mul_assoc, forgettingMultiplier]

/-- Forgetting the stable coordinate preserves the complete height limsup. -/
theorem codedOrbitHeight_eq_orbitHeight (N : PlaneNorm) (z : Word) :
    codedOrbitHeight N z = orbitHeight N (futureCode z) := by
  let c := chartTime (futureCode z) (pastCode z)
  have hdet (t : ℝ) : (flow (t + c) * rawChart (futureCode z) 0).det ≠ 0 := by
    rw [Matrix.det_mul, flow_det, rawChart_det]
    simp [dot]
  have hh := asymptotic_left_height_limsup N hdet (forgettingMultiplier_tendsto z)
  have hfactor : (fun t : ℝ => frameHeight N
      (forgettingMultiplier z t * (flow (t + c) * rawChart (futureCode z) 0))) =
      fun t : ℝ => frameHeight N (flow t * codedChart z 1) := by
    funext t
    rw [coded_flow_forgetting_factor]
  rw [hfactor] at hh
  change codedOrbitHeight N z = _ at hh
  have hshift : limsup (fun t : ℝ => frameHeight N (flow (t + c) * rawChart (futureCode z) 0)) atTop =
      limsup (fun t : ℝ => frameHeight N (flow t * rawChart (futureCode z) 0)) atTop := by
    have he := limsup_comp (fun t : ℝ => frameHeight N (flow t * rawChart (futureCode z) 0))
      (fun t : ℝ => t + c) atTop
    rw [map_add_atTop_eq c] at he
    exact he
  rw [hshift] at hh
  exact hh.trans (by simp only [frameHeight, frameSystole_flow_chart, orbitHeight])

end HallRay

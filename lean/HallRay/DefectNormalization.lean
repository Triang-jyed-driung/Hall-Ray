module

public import HallRay.DefectAlgebra
public import HallRay.OperatorEntries

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace HallRay

def defectTriple (u : Point) : Mat2 :=
  fiber .a (phi .a (phi .b u)) * fiber .a (phi .b u) * fiber .b u

def defectTripleScale (u : Point) : ℝ :=
  (Real.sqrt (d .a (phi .a (phi .b u))))⁻¹ *
    (Real.sqrt (d .a (phi .b u)))⁻¹ * (Real.sqrt (d .b u))⁻¹

def defectDenominator (u : Point) : ℝ :=
  Real.sqrt (d .a u) ^ 3 * Real.sqrt (d .a (phi .a (phi .b u))) *
    Real.sqrt (d .a (phi .b u)) * Real.sqrt (d .b u)

theorem adj2_smul (c : ℝ) (A : Mat2) : adj2 (c • A) = c • adj2 A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj2]

theorem smul_sq_matrix (c : ℝ) (A : Mat2) : (c • A) ^ 2 = c ^ 2 • A ^ 2 := by
  simp only [pow_two, smul_mul_assoc, Matrix.mul_smul, smul_smul]

theorem fiber_inverse_formula (s : Symbol) {u : Point} (hu : U u) :
    (fiber s u)⁻¹ = (Real.sqrt (d s u))⁻¹ • adj2 (fiberNumerator s u) := by
  rw [inv_eq_adj2 (fiber_det s hu), fiber, adj2_smul]

theorem defectTriple_factor {u : Point} (hu : U u) :
    defectTriple u = defectTripleScale u • defectNumerator u := by
  unfold defectTriple defectTripleScale fiber
  simp only [smul_mul_assoc, Matrix.mul_smul, smul_smul]
  rw [defect_numerator_product hu]

theorem commutator_smul (a b : ℝ) (A B : Mat2) :
    commutator (a • A) (b • B) = (a * b) • commutator A B := by
  simp only [commutator, smul_mul_assoc, Matrix.mul_smul, smul_smul, smul_sub]
  rw [mul_comm b a]

theorem defect_commutator_factor {u : Point} (hu : U u) :
    commutator (fiber .a u) ((fiber .a u)⁻¹ ^ 2 * defectTriple u) =
      ((Real.sqrt (d .a u))⁻¹ ^ 3 * defectTripleScale u) •
        commutator (fiberNumerator .a u) ((adj2 (fiberNumerator .a u)) ^ 2 * defectNumerator u) := by
  rw [fiber_inverse_formula .a hu, smul_sq_matrix, defectTriple_factor hu]
  simp only [smul_mul_assoc, Matrix.mul_smul, smul_smul]
  change commutator ((Real.sqrt (d .a u))⁻¹ • fiberNumerator .a u)
    (((Real.sqrt (d .a u))⁻¹ ^ 2 * defectTripleScale u) •
      ((adj2 (fiberNumerator .a u)) ^ 2 * defectNumerator u)) = _
  rw [commutator_smul]
  congr 1
  ring

theorem defect_commutator_scaled_entry {u : Point} (hu : U u) :
    defectDenominator u * commutator (fiber .a u) ((fiber .a u)⁻¹ ^ 2 * defectTriple u) 1 0 =
      commutator (fiberNumerator .a u) ((adj2 (fiberNumerator .a u)) ^ 2 * defectNumerator u) 1 0 := by
  rw [defect_commutator_factor hu]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have h₀ : Real.sqrt (d .a u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (d_pos .a hu))
  have h₁ : Real.sqrt (d .b u) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (d_pos .b hu))
  have h₂ : Real.sqrt (d .a (phi .b u)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (d_pos .a (phi_mem .b hu)))
  have h₃ : Real.sqrt (d .a (phi .a (phi .b u))) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (d_pos .a (phi_mem .a (phi_mem .b hu))))
  unfold defectDenominator defectTripleScale
  field_simp

theorem sqrt_d_le_eleven (s : Symbol) {u : Point} (hu : U u) : Real.sqrt (d s u) ≤ 11 := by
  have hsq := Real.sq_sqrt (d_pos s hu).le
  have hnonneg := Real.sqrt_nonneg (d s u)
  have hbound := (d_bounds s hu).2
  nlinarith

theorem defectDenominator_bounds {u : Point} (hu : U u) :
    0 < defectDenominator u ∧ defectDenominator u ≤ 11 ^ 6 := by
  have hp0 := Real.sqrt_pos.mpr (d_pos .a hu)
  have hp1 := Real.sqrt_pos.mpr (d_pos .b hu)
  have hp2 := Real.sqrt_pos.mpr (d_pos .a (phi_mem .b hu))
  have hp3 := Real.sqrt_pos.mpr (d_pos .a (phi_mem .a (phi_mem .b hu)))
  constructor
  · unfold defectDenominator
    positivity
  · unfold defectDenominator
    calc
      _ ≤ (11 : ℝ) ^ 3 * 11 * 11 * 11 := by
        gcongr
        · exact sqrt_d_le_eleven .a hu
        · exact sqrt_d_le_eleven .a (phi_mem .a (phi_mem .b hu))
        · exact sqrt_d_le_eleven .a (phi_mem .b hu)
        · exact sqrt_d_le_eleven .b hu
      _ = _ := by norm_num

theorem fixed_commutator_entry_gt {u : Point} (hu : U u) (hfix : phi .a u = u) :
    1 / 10000 < commutator (fiber .a u) ((fiber .a u)⁻¹ ^ 2 * defectTriple u) 1 0 := by
  have hnum := fixed_numerator_commutator_gt hu hfix
  have he := defect_commutator_scaled_entry hu
  have hd := defectDenominator_bounds hu
  by_contra! h
  have hm := mul_le_mul_of_nonneg_left h hd.1.le
  nlinarith

theorem defectApprox_commutator_entry_gt :
    1 / 10000 < commutator constantMatrix (defectApprox 2) 1 0 := by
  have hc : constantMatrix = fiber .a (futureCode constantWord) := by
    simp [constantMatrix, fiberMap, constantWord_shift, constantWord]
  rw [hc, defectApprox_two]
  exact fixed_commutator_entry_gt (futureCode_mem _) constantCode_fixed

end HallRay

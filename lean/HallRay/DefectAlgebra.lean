module

public import HallRay.DefectLimit

@[expose] public section
noncomputable section
open scoped Matrix Matrix.Norms.L2Operator
namespace HallRay

def defectNumerator (u : Point) : Mat2 :=
  !![99 * u.2 + 1009, -99 * u.1 - 81; 20 * u.2 + 101, 1011 - 20 * u.1]

/-- Exact polynomial simplification of the three unnormalized defect factors. -/
theorem defect_numerator_product {u : Point} (hu : U u) :
    fiberNumerator .a (phi .a (phi .b u)) * fiberNumerator .a (phi .b u) * fiberNumerator .b u =
      defectNumerator u := by
  have hd₁ : d .b u ≠ 0 := ne_of_gt (d_pos .b hu)
  have hd₂ : d .a (phi .b u) ≠ 0 := ne_of_gt (d_pos .a (phi_mem .b hu))
  have hdc : 101 - u.2 / (101 - u.1 + 10 * u.2) ≠ 0 := by
    convert hd₂ using 1
    dsimp [d, phi, sign]
    ring
  have hpoly : 10201 + u.2 * 1009 - u.1 * 101 ≠ 0 := by
    have hl := (abs_le.mp hu.2).1
    have hr := (abs_le.mp hu.1).2
    linarith
  have hpoly' : 10201 - u.1 * 101 + u.2 * 1009 ≠ 0 := by
    convert hpoly using 1
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiberNumerator, defectNumerator, Matrix.mul_apply,
      Fin.sum_univ_succ, phi, sign] <;>
    field_simp <;> simp_all [d, phi, sign] <;> field_simp <;> ring_nf <;> field_simp <;> ring

def commutator (A B : Mat2) : Mat2 := A * B - B * A

theorem numerator_commutator_entry (u : Point) :
    commutator (fiberNumerator .a u) ((adj2 (fiberNumerator .a u)) ^ 2 * defectNumerator u) 1 0 =
      2 * (10 * u.1 ^ 2 + 30 * u.1 * u.2 ^ 2 - 200 * u.1 * u.2 - 1011 * u.1 +
        10 * u.2 ^ 4 - 100 * u.2 ^ 3 - 1021 * u.2 ^ 2 + 10110 * u.2 + 101) := by
  simp [commutator, fiberNumerator, defectNumerator, adj2, sign, pow_two,
    ]
  ring

/-- Substituting the constant-code fixed point removes the large cancelling terms. -/
theorem fixed_numerator_commutator_entry {u : Point} (hu : U u) (hfix : phi .a u = u) :
    commutator (fiberNumerator .a u) ((adj2 (fiberNumerator .a u)) ^ 2 * defectNumerator u) 1 0 =
      2 * (101 * (d .a u) ^ 4 - 1010 * (d .a u) ^ 2 + 200 * d .a u - 10) / (d .a u) ^ 4 := by
  rw [numerator_commutator_entry]
  have hc := fixed_point_coordinates hu hfix
  have hd : d .a u ≠ 0 := ne_of_gt (d_pos .a hu)
  have hx := congrArg Prod.fst hc
  have hy := congrArg Prod.snd hc
  dsimp only at hx hy
  rw [hx, hy]
  field_simp
  ring

theorem fixed_numerator_commutator_gt {u : Point} (hu : U u) (hfix : phi .a u = u) :
    200 < commutator (fiberNumerator .a u)
      ((adj2 (fiberNumerator .a u)) ^ 2 * defectNumerator u) 1 0 := by
  rw [fixed_numerator_commutator_entry hu hfix]
  have ha := (fixed_point_alpha_bounds hu hfix).1
  have ha0 : 0 < d .a u := by linarith
  apply (lt_div_iff₀ (pow_pos ha0 4)).mpr
  have ha2 : 1010 < (d .a u) ^ 2 := by nlinarith
  have hp := mul_pos (sq_pos_of_pos ha0) (sub_pos.mpr ha2)
  nlinarith

/-- The future after the single b is the constant a future. -/
theorem defect_future_after : futureCode (shift 1 defectWord) = futureCode constantWord := by
  apply futureCode_congr
  intro n
  simp [shift, defectWord, constantWord, show (n : ℤ) + 1 ≠ 0 by omega]

theorem defect_future : futureCode defectWord = phi .b (futureCode constantWord) := by
  rw [futureCode_recurrence, defect_future_after]
  simp [defectWord]

theorem defect_future_before : futureCode (shift (-1) defectWord) =
    phi .a (phi .b (futureCode constantWord)) := by
  rw [futureCode_recurrence, shift_add]
  norm_num
  rw [defect_future]
  simp [shift, defectWord]

theorem defect_factor_zero : fiberMap defectWord = fiber .b (futureCode constantWord) := by
  simp only [fiberMap, defect_future_after]
  simp [defectWord]

theorem defect_factor_one : fiberMap (shift (-1) defectWord) =
    fiber .a (phi .b (futureCode constantWord)) := by
  unfold fiberMap
  rw [shift_add]
  norm_num
  rw [defect_future]
  simp [shift, defectWord]

theorem defect_factor_two : fiberMap (shift (-2) defectWord) =
    fiber .a (phi .a (phi .b (futureCode constantWord))) := by
  unfold fiberMap
  rw [shift_add]
  norm_num
  rw [defect_future_before]
  simp [shift, defectWord]

theorem defectApprox_two : defectApprox 2 =
    (fiber .a (futureCode constantWord))⁻¹ ^ 2 *
      (fiber .a (phi .a (phi .b (futureCode constantWord))) *
        fiber .a (phi .b (futureCode constantWord)) * fiber .b (futureCode constantWord)) := by
  have hc : constantMatrix = fiber .a (futureCode constantWord) := by
    simp [constantMatrix, fiberMap, constantWord_shift, constantWord]
  simp only [defectApprox, hc]
  norm_num
  rw [defect_factor_two, defect_factor_one, defect_factor_zero]

end HallRay

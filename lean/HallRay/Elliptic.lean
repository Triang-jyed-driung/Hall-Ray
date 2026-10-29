module

public import HallRay.Rotations
public import HallRay.ConstantBranch

@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace HallRay

def ellipticAngle (A : Matrix2) : ℝ := Real.arccos ((A 0 0 + A 1 1) / 2)

/-- A convenient GL_2 conjugator. Its determinant is not normalized to one;
all uses are conjugations, so this scalar normalization is unnecessary. -/
def ellipticConjugator (A : Matrix2) : Matrix2 :=
  !![1, (A 0 0 - A 1 1) / (2 * Real.sin (ellipticAngle A));
     0, A 1 0 / Real.sin (ellipticAngle A)]

theorem elliptic_halfTrace_bounds {A : Matrix2} (hell : Elliptic A) :
    -1 < (A 0 0 + A 1 1) / 2 ∧ (A 0 0 + A 1 1) / 2 < 1 := by
  obtain ⟨hl, hr⟩ := abs_lt.mp hell
  constructor <;> linarith

theorem elliptic_sin_pos {A : Matrix2} (hell : Elliptic A) : 0 < Real.sin (ellipticAngle A) := by
  have hb := elliptic_halfTrace_bounds hell
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact Real.arccos_pos.mpr hb.2
  · exact Real.arccos_lt_pi.mpr hb.1

theorem elliptic_cos {A : Matrix2} (hell : Elliptic A) :
    Real.cos (ellipticAngle A) = (A 0 0 + A 1 1) / 2 :=
  Real.cos_arccos (elliptic_halfTrace_bounds hell).1.le (elliptic_halfTrace_bounds hell).2.le

theorem elliptic_lowerLeft_ne_zero {A : Matrix2} (hA : A.det = 1) (hell : Elliptic A) :
    A 1 0 ≠ 0 := by
  intro hc
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hA
  obtain ⟨hl, hr⟩ := abs_lt.mp hell
  nlinarith [sq_nonneg (A 0 0 - A 1 1)]

theorem ellipticConjugator_det {A : Matrix2} (hA : A.det = 1) (hell : Elliptic A) :
    (ellipticConjugator A).det ≠ 0 := by
  simp only [ellipticConjugator, Matrix.det_fin_two]
  simpa using div_ne_zero (elliptic_lowerLeft_ne_zero hA hell) (ne_of_gt (elliptic_sin_pos hell))

theorem elliptic_intertwining {A : Matrix2} (hA : A.det = 1) (hell : Elliptic A) :
    A * ellipticConjugator A = ellipticConjugator A * rotation (ellipticAngle A) := by
  have hs0 := ne_of_gt (elliptic_sin_pos hell)
  have hc := elliptic_cos hell
  have hs := Real.sin_sq_add_cos_sq (ellipticAngle A)
  rw [hc] at hs
  rw [Matrix.det_fin_two] at hA
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ellipticConjugator, rotation, Matrix.mul_apply,
      Fin.sum_univ_succ, hc] <;>
    field_simp <;> nlinarith [hA, hs]

theorem elliptic_conjugate_rotation {A : Matrix2} (hA : A.det = 1) (hell : Elliptic A) :
    A = ellipticConjugator A * rotation (ellipticAngle A) * (ellipticConjugator A)⁻¹ := by
  have hG := ellipticConjugator_det hA hell
  have hinv : ellipticConjugator A * (ellipticConjugator A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG)
  calc
    A = (A * ellipticConjugator A) * (ellipticConjugator A)⁻¹ := by
      rw [Matrix.mul_assoc, hinv, mul_one]
    _ = _ := by rw [elliptic_intertwining hA hell]

theorem elliptic_power_norm_le {A : Matrix2} (hA : A.det = 1) (hell : Elliptic A) (n : ℕ) :
    ‖A ^ n‖ ≤ ‖ellipticConjugator A‖ * ‖(ellipticConjugator A)⁻¹‖ :=
  conjugate_rotation_power_norm_le (ellipticConjugator_det hA hell)
    (elliptic_conjugate_rotation hA hell) n

theorem elliptic_inverse_power_norm_le {A : Matrix2} (hA : A.det = 1) (hell : Elliptic A) (n : ℕ) :
    ‖(A ^ n)⁻¹‖ ≤ ‖ellipticConjugator A‖ * ‖(ellipticConjugator A)⁻¹‖ := by
  rw [determinant_one_inverse_norm (by rw [Matrix.det_pow, hA, one_pow])]
  exact elliptic_power_norm_le hA hell n

theorem elliptic_powers_bounded {A : Matrix2} (hA : A.det = 1) (hell : Elliptic A) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, ‖A ^ n‖ ≤ K ∧ ‖(A ^ n)⁻¹‖ ≤ K := by
  refine ⟨‖ellipticConjugator A‖ * ‖(ellipticConjugator A)⁻¹‖ + 1, by
    have := mul_nonneg (norm_nonneg (ellipticConjugator A)) (norm_nonneg ((ellipticConjugator A)⁻¹))
    linarith, ?_⟩
  intro n
  constructor
  · exact (elliptic_power_norm_le hA hell n).trans (by linarith)
  · exact (elliptic_inverse_power_norm_le hA hell n).trans (by linarith)

theorem periodic_angle_irrational (n : ℕ) (hell : Elliptic (periodMatrix n)) :
    Irrational (ellipticAngle (periodMatrix n) / Real.pi) :=
  irrational_of_infinite_order (ellipticConjugator_det (periodMatrix_det n) hell)
    (elliptic_conjugate_rotation (periodMatrix_det n) hell)
    (fun _ hk => periodMatrix_infinite_order n hk)

theorem constant_angle_irrational : Irrational (ellipticAngle (fiberMap constantWord) / Real.pi) := by
  have hell : Elliptic (fiberMap constantWord) := by
    simpa [fiberMap, constantWord_shift, constantWord] using constantCode_elliptic
  exact irrational_of_infinite_order (ellipticConjugator_det (fiberMap_det _) hell)
    (elliptic_conjugate_rotation (fiberMap_det _) hell) (fun _ hk => constantFiber_infinite_order hk)

end HallRay

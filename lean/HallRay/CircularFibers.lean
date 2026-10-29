module

public import HallRay.PhaseModel

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

theorem irrational_phase_cluster {ω : ℝ} (hω : Irrational (ω / Real.pi)) (θ : Real.Angle) :
    MapClusterPt θ atTop (fun n : ℕ => n • (ω : Real.Angle)) := by
  have hω' : Irrational (ω / (2 * Real.pi)) := by
    have h := hω.div_ratCast (q := 2) (by norm_num)
    convert h using 1
    norm_num
    ring
  have hd : DenseRange (fun n : ℤ => n • (ω : Real.Angle)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr hω'
  rw [mapClusterPt_atTop_nsmul_iff_mem_topologicalClosure_zmultiples]
  change θ ∈ closure (Set.range (fun n : ℤ => n • (ω : Real.Angle)))
  rw [hd.closure_range]
  trivial

theorem angleRotation_add (θ φ : Real.Angle) :
    angleRotation (θ + φ) = angleRotation θ * angleRotation φ := by
  induction θ using Real.Angle.induction_on
  induction φ using Real.Angle.induction_on
  simp only [← Real.Angle.coe_add, angleRotation_coe]
  exact rotation_add _ _

/-- The compact circle of matrices associated to an elliptic return. -/
def ellipticCircle (A : Mat2) (θ : Real.Angle) : Mat2 :=
  ellipticConjugator A * angleRotation θ * (ellipticConjugator A)⁻¹

@[fun_prop] theorem ellipticCircle_continuous (A : Mat2) : Continuous (ellipticCircle A) := by
  unfold ellipticCircle
  fun_prop

theorem ellipticCircle_det {A : Mat2} (hA : A.det = 1) (hell : Elliptic A) (θ : Real.Angle) :
    (ellipticCircle A θ).det = 1 := by
  have hG := ellipticConjugator_det hA hell
  simp [ellipticCircle, Matrix.det_mul, Matrix.det_nonsing_inv, angleRotation_det,
    Ring.inverse_eq_inv, mul_inv_cancel₀ hG]

theorem ellipticCircle_phase {A : Mat2} (hA : A.det = 1) (hell : Elliptic A) (n : ℕ) :
    ellipticCircle A (n • (ellipticAngle A : Real.Angle)) = A ^ n := by
  unfold ellipticCircle
  simp only [← Real.Angle.coe_nsmul, nsmul_eq_mul, angleRotation_coe]
  exact (conjugate_rotation_pow (ellipticConjugator_det hA hell)
    (elliptic_conjugate_rotation hA hell) n).symm

theorem ellipticCircle_compact (A : Mat2) : IsCompact (Set.range (ellipticCircle A)) :=
  isCompact_range (ellipticCircle_continuous A)

/-- Each point of the circle is approached arbitrarily late by positive powers. -/
theorem elliptic_power_cluster {A : Mat2} (hA : A.det = 1) (hell : Elliptic A)
    (hirr : Irrational (ellipticAngle A / Real.pi)) (θ : Real.Angle) :
    MapClusterPt (ellipticCircle A θ) atTop (fun n : ℕ => A ^ n) := by
  have hc := irrational_phase_cluster hirr θ
  have hf : ContinuousAt (ellipticCircle A) θ := (ellipticCircle_continuous A).continuousAt
  have h := MapClusterPt.continuousAt_comp hf hc
  simpa only [Function.comp_def, ellipticCircle_phase hA hell] using h

theorem elliptic_power_closure {A : Mat2} (hA : A.det = 1) (hell : Elliptic A)
    (hirr : Irrational (ellipticAngle A / Real.pi)) :
    closure (Set.range (fun n : ℕ => A ^ n)) = Set.range (ellipticCircle A) := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (ellipticCircle_compact A).isClosed
    rintro _ ⟨n, rfl⟩
    exact ⟨n • (ellipticAngle A : Real.Angle), ellipticCircle_phase hA hell n⟩
  · rintro _ ⟨θ, rfl⟩
    obtain ⟨n, hn, ht⟩ := (elliptic_power_cluster hA hell hirr θ).tendsto_subseq
    exact mem_closure_of_tendsto ht (Eventually.of_forall (fun i => ⟨n i, rfl⟩))

theorem ellipticAngle_continuous : Continuous ellipticAngle := by
  unfold ellipticAngle
  exact Real.continuous_arccos.comp (by fun_prop)

theorem ellipticConjugator_continuousAt {A : Mat2} (hell : Elliptic A) :
    ContinuousAt ellipticConjugator A := by
  have hs : Continuous (fun B : Mat2 => Real.sin (ellipticAngle B)) :=
    Real.continuous_sin.comp ellipticAngle_continuous
  have hs0 := ne_of_gt (elliptic_sin_pos hell)
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact continuousAt_const
  · change ContinuousAt (fun B : Mat2 => (B 0 0 - B 1 1) / (2 * Real.sin (ellipticAngle B))) A
    exact ((continuous_id.matrix_elem (0 : Fin 2) (0 : Fin 2)).continuousAt.sub
      (continuous_id.matrix_elem (1 : Fin 2) (1 : Fin 2)).continuousAt).div
      ((continuousAt_const.mul hs.continuousAt)) (mul_ne_zero (by norm_num) hs0)
  · exact continuousAt_const
  · change ContinuousAt (fun B : Mat2 => B 1 0 / Real.sin (ellipticAngle B)) A
    exact (continuous_id.matrix_elem (1 : Fin 2) (0 : Fin 2)).continuousAt.div hs.continuousAt hs0

theorem ellipticConjugator_inverse_continuousAt {A : Mat2} (hA : A.det = 1) (hell : Elliptic A) :
    ContinuousAt (fun B : Mat2 => (ellipticConjugator B)⁻¹) A := by
  have hG := ellipticConjugator_det hA hell
  have hinv : ContinuousAt (Inv.inv : Mat2 → Mat2) (ellipticConjugator A) :=
    continuousAt_matrix_inv _ (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hG)
  exact hinv.comp (ellipticConjugator_continuousAt hell)

/-- The circle parametrization varies continuously in the elliptic matrix. -/
theorem ellipticCircle_joint_continuousAt {A : Mat2} (hA : A.det = 1) (hell : Elliptic A)
    (θ : Real.Angle) : ContinuousAt (fun p : Mat2 × Real.Angle => ellipticCircle p.1 p.2) (A, θ) := by
  have hf : ContinuousAt (fun p : Mat2 × Real.Angle => p.1) (A, θ) := continuous_fst.continuousAt
  have hg : ContinuousAt (fun p : Mat2 × Real.Angle => p.2) (A, θ) := continuous_snd.continuousAt
  have hG : ContinuousAt (fun p : Mat2 × Real.Angle => ellipticConjugator p.1) (A, θ) :=
    ContinuousAt.comp (g := ellipticConjugator) (f := fun p : Mat2 × Real.Angle => p.1)
      (ellipticConjugator_continuousAt hell) hf
  have hR : ContinuousAt (fun p : Mat2 × Real.Angle => angleRotation p.2) (A, θ) :=
    ContinuousAt.comp (g := angleRotation) (f := fun p : Mat2 × Real.Angle => p.2)
      angleRotation_continuous.continuousAt hg
  have hI : ContinuousAt (fun p : Mat2 × Real.Angle => (ellipticConjugator p.1)⁻¹) (A, θ) :=
    ContinuousAt.comp (g := fun C : Mat2 => (ellipticConjugator C)⁻¹)
      (f := fun p : Mat2 × Real.Angle => p.1)
      (ellipticConjugator_inverse_continuousAt hA hell) hf
  exact (hG.mul hR).mul hI

/-- Convergence to an elliptic return supplies a uniform bound for all powers. -/
theorem uniform_elliptic_power_bound {A : ℕ → Mat2} {B : Mat2}
    (hlim : Tendsto A atTop (𝓝 B)) (hdet : ∀ n, (A n).det = 1)
    (hB : B.det = 1) (hell : Elliptic B) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ k : ℕ, ‖A n ^ k‖ ≤ K ∧ ‖(A n ^ k)⁻¹‖ ≤ K := by
  let K := ‖ellipticConjugator B‖ * ‖(ellipticConjugator B)⁻¹‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hcont : ContinuousAt (fun C : Mat2 => ‖ellipticConjugator C‖ * ‖(ellipticConjugator C)⁻¹‖) B :=
    (ellipticConjugator_continuousAt hell).norm.mul
      (ellipticConjugator_inverse_continuousAt hB hell).norm
  have hbound := (hcont.tendsto.comp hlim).eventually_lt_const (show
      ‖ellipticConjugator B‖ * ‖(ellipticConjugator B)⁻¹‖ < K by dsimp [K]; linarith)
  have hells : ∀ᶠ n in atTop, Elliptic (A n) := hlim.eventually (elliptic_isOpen.mem_nhds hell)
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, hells] with n hn he
  intro k
  exact ⟨(elliptic_power_norm_le (hdet n) he k).trans hn.le,
    (elliptic_inverse_power_norm_le (hdet n) he k).trans hn.le⟩

end HallRay

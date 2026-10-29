module

public import HallRay.LimitingMaxima

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- Moving forward away from the single defect leaves only the constant code. -/
theorem defect_forward_constant_limit :
    Tendsto (fun r : ℕ => shift ((r : ℤ) + 1) defectWord) atTop (𝓝 constantWord) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have he : ∀ᶠ r : ℕ in atTop, shift ((r : ℤ) + 1) defectWord i = constantWord i := by
    filter_upwards [eventually_ge_atTop (i.natAbs + 1)] with r hr
    have hi : -i ≤ (i.natAbs : ℤ) := by
      have h : -i ≤ ((-i).natAbs : ℤ) := Int.le_natAbs
      simpa using h
    simp [shift, defectWord, constantWord, show i + ((r : ℤ) + 1) ≠ 0 by omega]
  exact tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm))

/-- The entire constant-return circle occurs in the bulk of the limiting skeleton. -/
theorem bulk_mem_limitingSkeleton (θ : Real.Angle) :
    (constantWord, ellipticCircle constantMatrix θ) ∈ limitingSkeleton := by
  obtain ⟨r, hr, hp⟩ := (elliptic_power_cluster (fiberMap_det constantWord)
    constantMatrix_elliptic constant_angle_irrational θ).tendsto_subseq
  have hw := defect_forward_constant_limit.comp hr.tendsto_atTop
  have hb : Tendsto (fun i => beginningSkeleton (r i)) atTop
      (𝓝 (constantWord, ellipticCircle constantMatrix θ)) := hw.prodMk_nhds hp
  exact mem_closure_of_tendsto hb (Eventually.of_forall (fun i => Or.inl ⟨r i, rfl⟩))

theorem defect_positive_future (r : ℕ) :
    futureCode (shift ((r : ℤ) + 1) defectWord) = futureCode constantWord := by
  apply futureCode_congr
  intro m
  simp [shift, defectWord, constantWord, show (m : ℤ) + ((r : ℤ) + 1) ≠ 0 by omega]

theorem defect_positive_fiber (r : ℕ) :
    fiberMap (shift ((r : ℤ) + 1) defectWord) = constantMatrix := by
  have hshift : 1 + ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
  unfold fiberMap
  rw [shift_add, hshift, defect_positive_future]
  simp [constantMatrix, fiberMap, constantWord_shift, constantWord, shift, defectWord,
    show (r : ℤ) + 1 ≠ 0 by omega]

/-- The fixed beginning products in the paper are exactly constant-return powers. -/
theorem defect_beginning_product (r m : ℕ) :
    cocycle fiberMap (shift ((r : ℤ) + 1) defectWord) m = constantMatrix ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [cocycle_succ, ih, shift_add]
    have he : (m : ℤ) + ((r : ℤ) + 1) = ((m + r : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [he, defect_positive_fiber, pow_succ]

end HallRay

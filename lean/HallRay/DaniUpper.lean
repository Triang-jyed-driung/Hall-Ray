module

public import HallRay.DaniBounds

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal
namespace HallRay

/-- A large denominator cannot achieve a short balanced vector too early. -/
theorem balanceTime_ge_of_short {q δ c T : ℝ} (hq : 0 < q) (_hδ : 0 < δ)
    (hbound : c * Real.exp (2 * T) ≤ q)
    (hshort : vectorLength q δ (balanceTime q δ) < c) : T ≤ balanceTime q δ := by
  have hcancel : (c * Real.exp (2 * T)) * Real.exp (-2 * T) = c := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  have hfirst : c ≤ q * Real.exp (-2 * T) := by
    have h := mul_le_mul_of_nonneg_right hbound (Real.exp_pos (-2 * T)).le
    rwa [hcancel] at h
  by_contra! ht
  have hExp : Real.exp (-2 * T) ≤ Real.exp (-2 * balanceTime q δ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_left hExp hq.le
  have hmax : q * Real.exp (-2 * balanceTime q δ) ≤ vectorLength q δ (balanceTime q δ) := le_max_left _ _
  linarith

/-- One sufficiently late good approximation yields a late short lattice vector. -/
theorem small_approximation_late_vector (N : PlaneNorm) {x : Point} (hx : ¬RationalPair x)
    {c T : ℝ} (hc : 0 < c) {q : ℕ} (hq : 0 < q)
    (hbound : c * Real.exp (2 * T) ≤ (q : ℝ))
    (happrox : approximationTerm N x q < ENNReal.ofReal c ^ (3 / 2 : ℝ)) :
    ∃ t : ℝ, T ≤ t ∧ orbitSystole N x t < ENNReal.ofReal c := by
  obtain ⟨p, hp⟩ := approximationTerm_attained N x q
  let δ := N.value ((q : ℝ) • x - integerPoint p)
  have hδ : 0 < δ := by
    apply lt_of_le_of_ne (N.nonneg _)
    intro he
    have hz := (N.eq_zero_iff _).mp he.symm
    exact hx ⟨q, hq, p, sub_eq_zero.mp hz⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hpow := (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2 / 3)).mpr happrox
  rw [← ENNReal.rpow_mul] at hpow
  norm_num at hpow
  rw [hp, ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hδ.le) (by norm_num)] at hpow
  have hshort : vectorLength (q : ℝ) δ (balanceTime (q : ℝ) δ) < c := by
    rw [vectorLength_balanced hqR hδ]
    exact (ENNReal.ofReal_lt_ofReal_iff hc).mp hpow
  have ht := balanceTime_ge_of_short hqR hδ hbound hshort
  refine ⟨balanceTime (q : ℝ) δ, ht, ?_⟩
  have hw : ((q : ℤ), p) ≠ (0 : ℤ × (ℤ × ℤ)) := by
    intro he
    have h := congrArg Prod.fst he
    have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hq
    exact hqZ h
  calc
    _ ≤ ENNReal.ofReal (latticeLength N x (q : ℤ) p (balanceTime (q : ℝ) δ)) :=
      systole_le_latticeLength N x _ _ hw _
    _ = ENNReal.ofReal (vectorLength (q : ℝ) δ (balanceTime (q : ℝ) δ)) := by
      rw [latticeLength_eq_vectorLength]
      simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))]
      rfl
    _ < _ := (ENNReal.ofReal_lt_ofReal_iff hc).mpr hshort

/-- Infinitely many good denominators produce short vectors arbitrarily far along the flow. -/
theorem frequently_systole_lt_of_approximation (N : PlaneNorm) {x : Point} (hx : ¬RationalPair x)
    {c : ℝ} (hc : 0 < c)
    (happrox : ∃ᶠ q : ℕ in atTop, approximationTerm N x q < ENNReal.ofReal c ^ (3 / 2 : ℝ)) :
    ∃ᶠ t : ℝ in atTop, orbitSystole N x t < ENNReal.ofReal c := by
  rw [frequently_atTop] at happrox ⊢
  intro T
  obtain ⟨K, hK⟩ := exists_nat_gt (max 1 (c * Real.exp (2 * T)))
  obtain ⟨q, hqK, hq⟩ := happrox K
  have hqKR : (K : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqK
  have hqpos : 0 < q := by
    have : (1 : ℝ) < (q : ℝ) := (le_max_left _ _).trans_lt (hK.trans_le hqKR)
    exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) this)
  have hbound : c * Real.exp (2 * T) ≤ (q : ℝ) := (le_max_right _ _).trans (hK.le.trans hqKR)
  exact small_approximation_late_vector N hx hc hqpos hbound hq

theorem dani_upper (N : PlaneNorm) {x : Point} (hx : ¬RationalPair x) :
    liminf (orbitSystole N x) atTop ≤ approximationConstant N x ^ (2 / 3 : ℝ) := by
  by_contra! h
  obtain ⟨c, hcA, hcL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  have hcpos : 0 < (c : ℝ) := by
    have hp : (0 : ℝ≥0∞) < (c : ℝ≥0∞) := zero_le.trans_lt hcA
    exact_mod_cast hp
  have hpow : approximationConstant N x < (c : ℝ≥0∞) ^ (3 / 2 : ℝ) := by
    have hp := (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr hcA
    rw [← ENNReal.rpow_mul] at hp
    norm_num at hp
    exact hp
  have hfreq : ∃ᶠ q : ℕ in atTop,
      approximationTerm N x q < ENNReal.ofReal (c : ℝ) ^ (3 / 2 : ℝ) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using (frequently_lt_of_liminf_lt (h := hpow))
  have hshort := frequently_systole_lt_of_approximation N hx hcpos hfreq
  have hlong : ∀ᶠ t : ℝ in atTop, ENNReal.ofReal (c : ℝ) < orbitSystole N x t := by
    simpa only [ENNReal.ofReal_coe_nnreal] using eventually_lt_of_lt_liminf hcL
  obtain ⟨t, ht, ht'⟩ := (hshort.and_eventually hlong).exists
  exact lt_asymm ht ht'

end HallRay

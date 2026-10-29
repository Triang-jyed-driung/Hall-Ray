module

public import HallRay.DaniSeparation

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal
namespace HallRay

theorem approximationTerm_attained (N : PlaneNorm) (x : Point) (q : ℕ) :
    ∃ p : ℤ × ℤ, approximationTerm N x q =
      ENNReal.ofReal (Real.sqrt (q : ℝ) * N.value ((q : ℝ) • x - integerPoint p)) := by
  obtain ⟨p, hp⟩ := torusError_attained N x q
  refine ⟨p, ?_⟩
  rw [approximationTerm, hp, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

theorem approximationTerm_le_error (N : PlaneNorm) (x : Point) (q : ℕ) (p : ℤ × ℤ) :
    approximationTerm N x q ≤
      ENNReal.ofReal (Real.sqrt (q : ℝ) * N.value ((q : ℝ) • x - integerPoint p)) := by
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  exact mul_le_mul_right (iInf_le _ p) _

theorem systole_le_latticeLength (N : PlaneNorm) (x : Point) (q : ℤ) (p : ℤ × ℤ)
    (hw : (q, p) ≠ 0) (t : ℝ) :
    orbitSystole N x t ≤ ENNReal.ofReal (latticeLength N x q p t) := by
  unfold orbitSystole latticeLength
  exact iInf_le _ (⟨(q, p), hw⟩ : {w : ℤ × (ℤ × ℤ) // w ≠ 0})

theorem approximationTerm_root_le_length (N : PlaneNorm) (x : Point) (q : ℤ) (p : ℤ × ℤ) (t : ℝ) :
    approximationTerm N x q.natAbs ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal (latticeLength N x q p t) := by
  obtain ⟨p', he⟩ := natAbs_error N x q p
  have ha : (q.natAbs : ℝ) = |(q : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have h := approximationTerm_le_error N x q.natAbs p'
  rw [he, ha] at h
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt |(q : ℝ)| * N.value ((q : ℝ) • x - integerPoint p)) ^ (2 / 3 : ℝ) :=
      ENNReal.rpow_le_rpow h (by norm_num)
    _ = ENNReal.ofReal ((Real.sqrt |(q : ℝ)| * N.value ((q : ℝ) • x - integerPoint p)) ^ (2 / 3 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (N.nonneg _)) (by norm_num)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [latticeLength_eq_vectorLength]
      exact vectorLength_lower (abs_nonneg _) (N.nonneg _) t

/-- An eventual lower approximation bound gives an eventual systole bound. -/
theorem eventually_systole_lower_of_approximation (N : PlaneNorm) {x : Point} (hx : ¬RationalPair x)
    {c : ℝ} (hc : 0 < c)
    (happrox : ∀ᶠ q : ℕ in atTop, ENNReal.ofReal c ^ (3 / 2 : ℝ) ≤ approximationTerm N x q) :
    ∀ᶠ t : ℝ in atTop, ENNReal.ofReal c ≤ orbitSystole N x t := by
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp happrox
  filter_upwards [bounded_denominator_eventual_length N hx Q hc] with t hsmall
  apply le_iInf
  intro w
  change ENNReal.ofReal c ≤ ENNReal.ofReal (latticeLength N x w.val.1 w.val.2 t)
  by_cases hq : w.val.1.natAbs ≤ Q
  · exact ENNReal.ofReal_le_ofReal (hsmall _ hq _ w.property)
  · calc
      ENNReal.ofReal c = (ENNReal.ofReal c ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
        rw [← ENNReal.rpow_mul]
        norm_num
      _ ≤ approximationTerm N x w.val.1.natAbs ^ (2 / 3 : ℝ) :=
        ENNReal.rpow_le_rpow (hQ _ (by omega)) (by norm_num)
      _ ≤ _ := approximationTerm_root_le_length N x _ _ t

theorem dani_lower (N : PlaneNorm) {x : Point} (hx : ¬RationalPair x) :
    approximationConstant N x ^ (2 / 3 : ℝ) ≤ liminf (orbitSystole N x) atTop := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro c hc
  by_cases hcz : c = 0
  · subst c
    exact zero_le
  have hcpos : 0 < (c : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hcz
  have hpow : (c : ℝ≥0∞) ^ (3 / 2 : ℝ) < approximationConstant N x := by
    have hp := (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 3 / 2)).mpr hc
    rw [← ENNReal.rpow_mul] at hp
    norm_num at hp
    exact hp
  have happrox : ∀ᶠ q : ℕ in atTop, ENNReal.ofReal (c : ℝ) ^ (3 / 2 : ℝ) ≤ approximationTerm N x q := by
    have h := eventually_lt_of_lt_liminf hpow
    exact h.mono fun q hq => by simpa using hq.le
  have hs := eventually_systole_lower_of_approximation N hx hcpos happrox
  simpa using (le_liminf_of_le (h := hs))

end HallRay

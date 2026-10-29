module

public import HallRay.NearestInteger
public import HallRay.Balance

@[expose] public section
noncomputable section
open Filter Topology
namespace HallRay

@[simp] theorem integerPoint_neg (p : ℤ × ℤ) : integerPoint (-p) = -integerPoint p := by
  ext <;> simp [integerPoint]

theorem integerPoint_norm_ge_one {p : ℤ × ℤ} (hp : p ≠ 0) : 1 ≤ ‖integerPoint p‖ := by
  by_cases h₁ : p.1 = 0
  · have h₂ : p.2 ≠ 0 := by intro h₂; apply hp; exact Prod.ext h₁ h₂
    have h : (1 : ℤ) ≤ |p.2| := Int.one_le_abs h₂
    have hr : (1 : ℝ) ≤ |(p.2 : ℝ)| := by exact_mod_cast h
    exact hr.trans (by simp only [integerPoint, Prod.norm_def, Real.norm_eq_abs]; exact le_max_right _ _)
  · have h : (1 : ℤ) ≤ |p.1| := Int.one_le_abs h₁
    have hr : (1 : ℝ) ≤ |(p.1 : ℝ)| := by exact_mod_cast h
    exact hr.trans (by simp only [integerPoint, Prod.norm_def, Real.norm_eq_abs]; exact le_max_left _ _)

/-- Finitely many positive denominators have errors uniformly separated from zero. -/
theorem finite_denominator_separation (N : PlaneNorm) {x : Point} (hx : ¬RationalPair x) (Q : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℕ, 0 < q → q ≤ Q → ∀ p : ℤ × ℤ,
      ε ≤ N.value ((q : ℝ) • x - integerPoint p) := by
  induction Q with
  | zero => exact ⟨1, by norm_num, fun q hq hQ => by omega⟩
  | succ Q ih =>
    obtain ⟨ε, hε, hprev⟩ := ih
    obtain ⟨p₀, hmin⟩ := N.nearest_integer (((Q + 1 : ℕ) : ℝ) • x)
    have hδ : 0 < N.value (((Q + 1 : ℕ) : ℝ) • x - integerPoint p₀) := by
      apply lt_of_le_of_ne (N.nonneg _)
      intro he
      have hz := (N.eq_zero_iff _).mp he.symm
      exact hx ⟨Q + 1, by omega, p₀, sub_eq_zero.mp hz⟩
    refine ⟨min ε (N.value (((Q + 1 : ℕ) : ℝ) • x - integerPoint p₀)), lt_min hε hδ, ?_⟩
    intro q hq hQ p
    by_cases hqQ : q ≤ Q
    · exact (min_le_left _ _).trans (hprev q hq hqQ p)
    · have he : q = Q + 1 := by omega
      subst q
      exact (min_le_right _ _).trans (hmin p)

/-- Changing the sign of a denominator can be absorbed into the numerator. -/
theorem natAbs_error (N : PlaneNorm) (x : Point) (q : ℤ) (p : ℤ × ℤ) :
    ∃ p' : ℤ × ℤ, N.value ((q.natAbs : ℝ) • x - integerPoint p') =
      N.value ((q : ℝ) • x - integerPoint p) := by
  have ha : (q.natAbs : ℝ) = |(q : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  by_cases hq : 0 ≤ q
  · refine ⟨p, ?_⟩
    rw [ha, abs_of_nonneg (by exact_mod_cast hq)]
  · refine ⟨-p, ?_⟩
    rw [ha, abs_of_neg (by exact_mod_cast (lt_of_not_ge hq)), integerPoint_neg]
    have he : (-(q : ℝ)) • x - -integerPoint p = -((q : ℝ) • x - integerPoint p) := by module
    rw [he, N.neg]

/-- The zero denominator is controlled by discreteness of the integer plane. -/
theorem bounded_denominator_separation (N : PlaneNorm) {x : Point} (hx : ¬RationalPair x) (Q : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℤ, q.natAbs ≤ Q → ∀ p : ℤ × ℤ, (q, p) ≠ 0 →
      ε ≤ N.value ((q : ℝ) • x - integerPoint p) := by
  obtain ⟨c, hc, hnorm⟩ := N.exists_lower_bound
  obtain ⟨δ, hδ, hsep⟩ := finite_denominator_separation N hx Q
  refine ⟨min c δ, lt_min hc hδ, ?_⟩
  intro q hQ p hw
  by_cases hq : q = 0
  · subst q
    have hp : p ≠ 0 := by intro hp; apply hw; simp [hp]
    have hn := hnorm (integerPoint p)
    have hi := integerPoint_norm_ge_one hp
    have hc' : c ≤ N.value (integerPoint p) := by nlinarith
    simpa only [Int.cast_zero, zero_smul, zero_sub, N.neg] using (min_le_left c δ).trans hc'
  · obtain ⟨p', he⟩ := natAbs_error N x q p
    have hpq : 0 < q.natAbs := Int.natAbs_pos.mpr hq
    rw [← he]
    exact (min_le_right c δ).trans (hsep _ hpq hQ p')

def latticeLength (N : PlaneNorm) (x : Point) (q : ℤ) (p : ℤ × ℤ) (t : ℝ) : ℝ :=
  max (Real.exp (-2 * t) * |(q : ℝ)|) (Real.exp t * N.value ((q : ℝ) • x - integerPoint p))

theorem latticeLength_eq_vectorLength (N : PlaneNorm) (x : Point) (q : ℤ) (p : ℤ × ℤ) (t : ℝ) :
    latticeLength N x q p t = vectorLength |(q : ℝ)| (N.value ((q : ℝ) • x - integerPoint p)) t := by
  unfold latticeLength vectorLength
  congr 1 <;> ring

/-- Every fixed range of denominators eventually contributes only long vectors. -/
theorem bounded_denominator_eventual_length (N : PlaneNorm) {x : Point} (hx : ¬RationalPair x)
    (Q : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, ∀ q : ℤ, q.natAbs ≤ Q → ∀ p : ℤ × ℤ, (q, p) ≠ 0 →
      c ≤ latticeLength N x q p t := by
  obtain ⟨ε, hε, hsep⟩ := bounded_denominator_separation N hx Q
  filter_upwards [eventually_ge_atTop (Real.log (c / ε))] with t ht
  intro q hQ p hw
  have hExp := Real.exp_le_exp.mpr ht
  rw [Real.exp_log (div_pos hc hε)] at hExp
  have hm := mul_le_mul_of_nonneg_right hExp hε.le
  rw [div_mul_cancel₀ c (ne_of_gt hε)] at hm
  calc
    c ≤ Real.exp t * ε := hm
    _ ≤ Real.exp t * N.value ((q : ℝ) • x - integerPoint p) :=
      mul_le_mul_of_nonneg_left (hsep q hQ p hw) (Real.exp_pos _).le
    _ ≤ latticeLength N x q p t := le_max_right _ _

end HallRay

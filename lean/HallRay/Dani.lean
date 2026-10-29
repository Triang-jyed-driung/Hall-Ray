module

public import HallRay.Spectrum
public import HallRay.Balance
public import HallRay.DaniUpper

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal
namespace HallRay

/-- A rational initial plane vector has an exponentially shrinking lattice vector. -/
theorem rational_systole_bound (N : PlaneNorm) {x : Point} (hx : RationalPair x) :
    ∃ q : ℕ, 0 < q ∧ ∀ t : ℝ,
      orbitSystole N x t ≤ ENNReal.ofReal ((q : ℝ) * Real.exp (-2 * t)) := by
  obtain ⟨q, hq, p, hp⟩ := hx
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  let w : {w : ℤ × (ℤ × ℤ) // w ≠ 0} :=
    ⟨((q : ℤ), p), fun hw => hqZ (congrArg Prod.fst hw)⟩
  have hz : N.value (0 : Point) = 0 := (N.eq_zero_iff 0).mpr rfl
  refine ⟨q, hq, fun t => ?_⟩
  calc
    _ ≤ ENNReal.ofReal (max (Real.exp (-2 * t) * |(w.val.1 : ℝ)|)
        (Real.exp t * N.value ((w.val.1 : ℝ) • x - integerPoint w.val.2))) := iInf_le _ w
    _ = _ := by
      dsimp [w]
      simp only [Int.cast_natCast, hp, sub_self, hz, mul_zero,
        abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ (q : ℝ))]
      rw [max_eq_left (by positivity)]
      congr 1
      ring

/-- The rational case of Lemma `lem:dani`, with an actual limit of the systole. -/
theorem rational_systole_tendsto_zero (N : PlaneNorm) {x : Point} (hx : RationalPair x) :
    Tendsto (orbitSystole N x) atTop (𝓝 0) := by
  obtain ⟨q, hq, hbound⟩ := rational_systole_bound N hx
  have ht : Tendsto (fun t : ℝ => 2 * t) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num)
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have hg : Tendsto (fun t : ℝ => ENNReal.ofReal ((q : ℝ) * Real.exp (-2 * t)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (he.const_mul (q : ℝ))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact False.elim (not_lt_of_ge (show (0 : ℝ≥0∞) ≤ a from zero_le) ha)
  · intro b hb
    exact (hg.eventually_lt_const hb).mono fun t ht => lt_of_le_of_lt (hbound t) ht

theorem dani_rational (N : PlaneNorm) {x : Point} (hx : RationalPair x) :
    liminf (orbitSystole N x) atTop = approximationConstant N x ^ (2 / 3 : ℝ) := by
  rw [(rational_systole_tendsto_zero N hx).liminf_eq, rational_approximation_zero N hx]
  exact (ENNReal.zero_rpow_of_pos (by norm_num)).symm

/-- Lemma `lem:dani` for every plane norm and every initial vector. -/
theorem dani_correspondence (N : PlaneNorm) : DaniCorrespondence N := by
  intro x
  by_cases hx : RationalPair x
  · exact dani_rational N hx
  · exact le_antisymm (dani_upper N hx) (dani_lower N hx)

/-- With Dani's correspondence discharged, only the dynamical ray remains. -/
theorem main_of_dynamical_ray (N : PlaneNorm) (hray : DynamicalHallRay N) : HasHallRay N :=
  main_of_dani_and_ray N (dani_correspondence N) hray

end HallRay

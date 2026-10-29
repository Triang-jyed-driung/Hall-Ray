module

public import HallRay.PeriodicRepetitions

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- Replacing a long periodic tail changes the accumulated prefix fiber exponentially little. -/
theorem splice_prefix_error (z : Word) (r n n' : ℕ) (hn : n ≤ n')
    (htail : ∀ m : ℕ, shift (r : ℤ) z (m : ℤ) = periodicWord n (m : ℤ)) :
    ‖cocycle fiberMap (spliceWord z r (periodicWord n')) r - cocycle fiberMap z r‖ ≤
      ‖cocycle fiberMap z r‖ * (1 / 600 : ℝ) ^ n := by
  have he := fiber_product_error r n (spliceWord_periodic_agreement z r n n' hn htail)
  exact (absolute_error_le _ _ (fiberProduct_det z r)).trans
    (mul_le_mul_of_nonneg_left he (norm_nonneg _))

/-- The new complete prefix is close to the old fiber times the chosen full-period multiplier. -/
theorem splice_fiber_increment (z : Word) (r n n' L : ℕ) (hn : n ≤ n')
    (htail : ∀ m : ℕ, shift (r : ℤ) z (m : ℤ) = periodicWord n (m : ℤ)) :
    ‖cocycle fiberMap (spliceWord z r (periodicWord n')) (r + L * (n' + 1)) -
      cocycle fiberMap z r * periodMatrix n' ^ L‖ ≤
      (‖cocycle fiberMap z r‖ * ‖periodMatrix n' ^ L‖) * (1 / 600 : ℝ) ^ n := by
  rw [spliceWord_period_product, ← sub_mul]
  have hb := (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    (splice_prefix_error z r n n' hn htail) (norm_nonneg (periodMatrix n' ^ L)))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hb

theorem spliceWord_periodic_tail_at_end (z : Word) (r n L m : ℕ) :
    shift ((r + L * (n + 1) : ℕ) : ℤ) (spliceWord z r (periodicWord n)) (m : ℤ) =
      periodicWord n (m : ℤ) := by
  unfold shift
  have hpos : 0 ≤ ((L * (n + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
  rw [spliceWord_after z (periodicWord n) r (by push_cast at hpos ⊢; omega)]
  have he : (m : ℤ) + ((r + L * (n + 1) : ℕ) : ℤ) - r = (m : ℤ) + ((L * (n + 1) : ℕ) : ℤ) := by
    push_cast
    ring
  rw [he]
  exact congrArg (fun w : Word => w (m : ℤ)) (shift_nat_mul_of_periodic (periodicWord_period n) L)

/-- The explicit pointwise limit of an expanding sequence of stable prefixes. -/
def prefixLimitWord (z : ℕ → Word) : Word := fun i => z (i.natAbs + 1) i

theorem stable_prefixes_later {r : ℕ → ℕ} (hr : StrictMono r) {z : ℕ → Word}
    (hstable : ∀ k : ℕ, ∀ i : ℤ, i < (r k : ℤ) → z (k + 1) i = z k i)
    {k l : ℕ} (hkl : k ≤ l) {i : ℤ} (hi : i < (r k : ℤ)) : z l i = z k i := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    have hrl : (r k : ℤ) ≤ r l := by exact_mod_cast hr.monotone hkl
    rw [hstable l i (hi.trans_le hrl), ih]

theorem prefixLimitWord_prefix {r : ℕ → ℕ} (hr : StrictMono r) {z : ℕ → Word}
    (hstable : ∀ k : ℕ, ∀ i : ℤ, i < (r k : ℤ) → z (k + 1) i = z k i)
    (k : ℕ) {i : ℤ} (hi : i < (r k : ℤ)) : prefixLimitWord z i = z k i := by
  have hiabs : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
  have hrabs : i.natAbs + 1 ≤ r (i.natAbs + 1) := hr.le_apply
  have hiall : i < (r (i.natAbs + 1) : ℤ) := by omega
  unfold prefixLimitWord
  by_cases hki : k ≤ i.natAbs + 1
  · exact stable_prefixes_later hr hstable hki hi
  · exact (stable_prefixes_later hr hstable (by omega) hiall).symm

theorem stable_prefixes_tendsto {r : ℕ → ℕ} (hr : StrictMono r) {z : ℕ → Word}
    (hstable : ∀ k : ℕ, ∀ i : ℤ, i < (r k : ℤ) → z (k + 1) i = z k i) :
    Tendsto z atTop (𝓝 (prefixLimitWord z)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have hiabs : i ≤ (i.natAbs : ℤ) := Int.le_natAbs
  have hrabs : i.natAbs + 1 ≤ r (i.natAbs + 1) := hr.le_apply
  have hi : i < (r (i.natAbs + 1) : ℤ) := by omega
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (i.natAbs + 1)] with k hk
  exact (prefixLimitWord_prefix hr hstable k
    (hi.trans_le (by exact_mod_cast hr.monotone hk)))

/-- The limit also retains the extra agreement beyond each splice boundary. -/
theorem prefixLimitWord_extra_agreement {r N : ℕ → ℕ} (hr : StrictMono r) {z : ℕ → Word}
    (hstable : ∀ k : ℕ, ∀ i : ℤ, i < (r k : ℤ) → z (k + 1) i = z k i)
    (hextra : ∀ k : ℕ, ∀ i : ℤ, i < ((r k + N k : ℕ) : ℤ) → z (k + 1) i = z k i)
    (hgrowth : ∀ k, r k + N k ≤ r (k + 1)) (k : ℕ) {i : ℤ}
    (hi : i < ((r k + N k : ℕ) : ℤ)) : prefixLimitWord z i = z k i := by
  rw [prefixLimitWord_prefix hr hstable (k + 1) (hi.trans_le (by exact_mod_cast hgrowth k)), hextra k i hi]

end HallRay

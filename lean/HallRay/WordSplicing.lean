module

public import HallRay.PeriodicUniformBounds

@[expose] public section
noncomputable section
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- Retain the old past and prefix, replacing the future starting at return r. -/
def spliceWord (z : Word) (r : ℕ) (w : Word) : Word :=
  fun i => if i < (r : ℤ) then z i else w (i - r)

theorem spliceWord_before (z w : Word) (r : ℕ) {i : ℤ} (hi : i < (r : ℤ)) :
    spliceWord z r w i = z i := by simp [spliceWord, hi]

theorem spliceWord_after (z w : Word) (r : ℕ) {i : ℤ} (hi : (r : ℤ) ≤ i) :
    spliceWord z r w i = w (i - r) := by simp [spliceWord, not_lt.mpr hi]

theorem spliceWord_tail (z w : Word) (r m : ℕ) :
    shift (r : ℤ) (spliceWord z r w) (m : ℤ) = w (m : ℤ) := by
  simp [shift, spliceWord, show ¬ (m : ℤ) + r < (r : ℤ) by omega]

/-- Fibers, unlike roof times, depend only on the future symbols. -/
theorem fiberMap_future_congr {z w : Word} (h : ∀ m : ℕ, z (m : ℤ) = w (m : ℤ)) :
    fiberMap z = fiberMap w := by
  have hf : futureCode (shift 1 z) = futureCode (shift 1 w) := by
    apply futureCode_congr
    intro m
    simpa only [shift, Nat.cast_add, Nat.cast_one] using h (m + 1)
  unfold fiberMap
  rw [hf, show z 0 = w 0 from by simpa using h 0]

theorem fiberProduct_future_congr {z w : Word} (h : ∀ m : ℕ, z (m : ℤ) = w (m : ℤ)) (l : ℕ) :
    cocycle fiberMap z l = cocycle fiberMap w l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [cocycle_succ, cocycle_succ, ih]
    congr 1
    apply fiberMap_future_congr
    intro m
    simpa only [shift, Nat.cast_add] using h (m + l)

theorem spliceWord_tail_product (z w : Word) (r l : ℕ) :
    cocycle fiberMap (shift (r : ℤ) (spliceWord z r w)) l = cocycle fiberMap w l :=
  fiberProduct_future_congr (spliceWord_tail z w r) l

/-- Splicing a periodic tail gives exact whole-period fiber multipliers. -/
theorem spliceWord_period_product (z : Word) (r n L : ℕ) :
    cocycle fiberMap (spliceWord z r (periodicWord n)) (r + L * (n + 1)) =
      cocycle fiberMap (spliceWord z r (periodicWord n)) r * periodMatrix n ^ L := by
  rw [cocycle_add, spliceWord_tail_product,
    cocycle_periods _ _ _ (periodicWord_period n)]
  rfl

/-- Increasing a block length preserves the old prefix and its following a-run. -/
theorem spliceWord_periodic_agreement (z : Word) (r n n' : ℕ) (hn : n ≤ n')
    (htail : ∀ m : ℕ, shift (r : ℤ) z (m : ℤ) = periodicWord n (m : ℤ)) :
    ∀ i : ℕ, i < r + n → z (i : ℤ) = spliceWord z r (periodicWord n') (i : ℤ) := by
  intro i hi
  by_cases hir : i < r
  · exact (spliceWord_before z (periodicWord n') r (by omega)).symm
  · have hsub : ((i - r : ℕ) : ℤ) = (i : ℤ) - r := Nat.cast_sub (by omega)
    have hz := htail (i - r)
    simp only [shift, hsub, sub_add_cancel] at hz
    rw [spliceWord_after z (periodicWord n') r (by omega), hz,
      ← hsub, periodicWord_a (show i - r < n by omega),
      periodicWord_a (show i - r < n' by omega)]

end HallRay

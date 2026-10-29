module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section
noncomputable section
namespace HallRay

/-- Length of one nonzero-denominator lattice vector along the diagonal flow. -/
def vectorLength (q δ t : ℝ) : ℝ := max (q * Real.exp (-2 * t)) (δ * Real.exp t)

def balanceTime (q δ : ℝ) : ℝ := Real.log (q / δ) / 3

theorem balance_exp {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) :
    Real.exp (3 * balanceTime q δ) = q / δ := by
  rw [balanceTime, show 3 * (Real.log (q / δ) / 3) = Real.log (q / δ) by ring]
  exact Real.exp_log (div_pos hq hδ)

theorem balanced_terms {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) :
    q * Real.exp (-2 * balanceTime q δ) = δ * Real.exp (balanceTime q δ) := by
  let t := balanceTime q δ
  have he : Real.exp (3 * t) = q / δ := balance_exp hq hδ
  have hm : Real.exp (-2 * t) * Real.exp (3 * t) = Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hm
  calc
    q * Real.exp (-2 * t) = δ * (Real.exp (-2 * t) * (q / δ)) := by
      field_simp
    _ = δ * Real.exp t := by rw [hm]

theorem vector_product (q δ t : ℝ) :
    (q * Real.exp (-2 * t)) * (δ * Real.exp t) ^ 2 = q * δ ^ 2 := by
  have he : Real.exp (-2 * t) * (Real.exp t) ^ 2 = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    rw [show -2 * t + (t + t) = 0 by ring, Real.exp_zero]
  calc
    _ = (q * δ ^ 2) * (Real.exp (-2 * t) * (Real.exp t) ^ 2) := by ring
    _ = _ := by rw [he, mul_one]

/-- The cube of the minimum length is q δ², avoiding fractional powers. -/
theorem vectorLength_lower_cube {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 ≤ δ) (t : ℝ) :
    q * δ ^ 2 ≤ vectorLength q δ t ^ 3 := by
  have ha : 0 ≤ q * Real.exp (-2 * t) := mul_nonneg hq (Real.exp_pos _).le
  have hb : 0 ≤ δ * Real.exp t := mul_nonneg hδ (Real.exp_pos _).le
  have hL : 0 ≤ vectorLength q δ t := le_trans ha (le_max_left _ _)
  rw [← vector_product q δ t]
  calc
    _ ≤ vectorLength q δ t * vectorLength q δ t ^ 2 := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = _ := by ring

theorem vectorLength_balanced_cube {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) :
    vectorLength q δ (balanceTime q δ) ^ 3 = q * δ ^ 2 := by
  have he := balanced_terms hq hδ
  have hv := vector_product q δ (balanceTime q δ)
  unfold vectorLength
  rw [he, max_self]
  rw [he] at hv
  nlinarith [hv]

/-- The minimizing time in the direct-min formula of Lemma 2.1. -/
theorem vectorLength_min {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) (t : ℝ) :
    vectorLength q δ (balanceTime q δ) ≤ vectorLength q δ t := by
  have hl := vectorLength_lower_cube hq.le hδ.le t
  rw [← vectorLength_balanced_cube hq hδ] at hl
  exact (Odd.strictMono_pow (by decide : Odd 3)).le_iff_le.mp hl

theorem balanced_value_cube {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 ≤ δ) :
    ((Real.sqrt q * δ) ^ (2 / 3 : ℝ)) ^ 3 = q * δ ^ 2 := by
  have hp : 0 ≤ Real.sqrt q * δ := mul_nonneg (Real.sqrt_nonneg _) hδ
  rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul hp]
  norm_num
  rw [mul_pow, Real.sq_sqrt hq]

theorem vectorLength_lower {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 ≤ δ) (t : ℝ) :
    (Real.sqrt q * δ) ^ (2 / 3 : ℝ) ≤ vectorLength q δ t := by
  have h := vectorLength_lower_cube hq hδ t
  rw [← balanced_value_cube hq hδ] at h
  exact (Odd.strictMono_pow (by decide : Odd 3)).le_iff_le.mp h

theorem vectorLength_balanced {q δ : ℝ} (hq : 0 < q) (hδ : 0 < δ) :
    vectorLength q δ (balanceTime q δ) = (Real.sqrt q * δ) ^ (2 / 3 : ℝ) := by
  apply (Odd.strictMono_pow (by decide : Odd 3)).injective
  dsimp only
  rw [vectorLength_balanced_cube hq hδ, balanced_value_cube hq.le hδ.le]

end HallRay

module

public import HallRay.Coding

@[expose] public section
noncomputable section
namespace HallRay

/-- The cubic from (4.5), also the characteristic polynomial of gamma_a. -/
def cubic (x : ℝ) : ℝ := x ^ 3 - 101 * x ^ 2 + 20 * x - 1

/-- The fixed point equations force the cubic, without algebraic-number assumptions. -/
theorem fixed_point_cubic {u : Point} (hu : U u) (hfix : phi .a u = u) :
    cubic (d .a u) = 0 := by
  let α := d .a u
  have hα : α ≠ 0 := ne_of_gt (d_pos .a hu)
  have h₁ := congrArg Prod.fst hfix
  have h₂ := congrArg Prod.snd hfix
  simp only [phi, sign, one_mul] at h₁ h₂
  change (10 - u.2) / α = u.1 at h₁
  change 1 / α = u.2 at h₂
  have h₁' : α * u.1 = 10 - u.2 := by
    have := (div_eq_iff hα).mp h₁
    linarith
  have h₂' : α * u.2 = 1 := by
    have := (div_eq_iff hα).mp h₂
    linarith
  have ha : α = 101 - u.1 - 10 * u.2 := by simp [α, d, sign]
  change α ^ 3 - 101 * α ^ 2 + 20 * α - 1 = 0
  linear_combination α ^ 2 * ha - α * h₁' - (10 * α - 1) * h₂'

theorem fixed_point_coordinates {u : Point} (hu : U u) (hfix : phi .a u = u) :
    u = (10 / d .a u - 1 / (d .a u) ^ 2, 1 / d .a u) := by
  have hd : d .a u ≠ 0 := ne_of_gt (d_pos .a hu)
  have h₁ := congrArg Prod.fst hfix
  have h₂ := congrArg Prod.snd hfix
  simp only [phi, sign, one_mul] at h₁ h₂
  change (10 - u.2) / d .a u = u.1 at h₁
  change 1 / d .a u = u.2 at h₂
  apply Prod.ext
  · rw [← h₁, ← h₂]
    field_simp
  · exact h₂.symm

theorem fixed_point_alpha_bounds {u : Point} (hu : U u) (hfix : phi .a u = u) :
    100 < d .a u ∧ d .a u < 101 := by
  have hd := d_bounds .a hu
  have hc := fixed_point_coordinates hu hfix
  have hy : 0 < u.2 := by
    rw [hc]
    exact one_div_pos.mpr (d_pos .a hu)
  have hx : 0 < u.1 := by
    have hh := congrArg Prod.fst hfix
    simp only [phi, sign, one_mul] at hh
    rw [← hh]
    apply div_pos _ (d_pos .a hu)
    have := (abs_le.mp hu.2).2
    linarith
  dsimp [d, sign] at *
  constructor <;> linarith

/-- Elliptic means the absolute trace is strictly less than two. -/
def Elliptic (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  |A 0 0 + A 1 1| < 2

/-- The elementary ellipticity assertion of Lemma 4.2.
Irrationality of the rotation angle is a separate, currently unformalized claim. -/
theorem fixed_point_elliptic {u : Point} (hu : U u) (hfix : phi .a u = u) :
    Elliptic (fiber .a u) := by
  have hα := fixed_point_alpha_bounds hu hfix
  have hs : 10 < Real.sqrt (d .a u) := by
    exact (Real.lt_sqrt (by norm_num)).2 (by nlinarith [hα.1])
  have hs0 : 0 < Real.sqrt (d .a u) := by linarith
  have hy : 0 < u.2 := by
    have hc := congrArg Prod.snd (fixed_point_coordinates hu hfix)
    dsimp at hc
    rw [hc]
    exact one_div_pos.mpr (d_pos .a hu)
  have hyb := (abs_le.mp hu.2).2
  change |(Real.sqrt (d .a u))⁻¹ * (10 - 1 * u.2) +
    (Real.sqrt (d .a u))⁻¹ * 10| < 2
  rw [show (Real.sqrt (d .a u))⁻¹ * (10 - 1 * u.2) +
      (Real.sqrt (d .a u))⁻¹ * 10 =
      (20 - u.2) / Real.sqrt (d .a u) by ring]
  rw [abs_of_pos (div_pos (by linarith) hs0), div_lt_iff₀ hs0]
  linarith

/-- The constant word supplies the fixed point needed by the preceding lemmas. -/
theorem constantCode_cubic : cubic (d .a (futureCode constantWord)) = 0 :=
  fixed_point_cubic (futureCode_mem _) constantCode_fixed

theorem constantCode_alpha_bounds :
    100 < d .a (futureCode constantWord) ∧ d .a (futureCode constantWord) < 101 :=
  fixed_point_alpha_bounds (futureCode_mem _) constantCode_fixed

theorem constantCode_elliptic : Elliptic (fiber .a (futureCode constantWord)) :=
  fixed_point_elliptic (futureCode_mem _) constantCode_fixed

end HallRay

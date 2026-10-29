module

public import HallRay.Contraction

@[expose] public section
noncomputable section
namespace HallRay

theorem d_difference (s : Symbol) (u v : Point) :
    |d s u - d s v| ≤ 11 * supDist u v := by
  have hs : |sign s| = 1 := by cases s <;> norm_num [sign]
  calc
    _ = |-(u.1 - v.1) + (-10 * sign s * (u.2 - v.2))| := by
      congr 1
      dsimp [d]
      ring
    _ ≤ |-(u.1 - v.1)| + |-10 * sign s * (u.2 - v.2)| := abs_add_le _ _
    _ = |u.1 - v.1| + 10 * |u.2 - v.2| := by rw [abs_neg, abs_mul, abs_mul, hs]; norm_num
    _ ≤ 11 * supDist u v := by
      have hx : |u.1 - v.1| ≤ supDist u v := le_max_left _ _
      have hy : |u.2 - v.2| ≤ supDist u v := le_max_right _ _
      linarith

theorem sqrt_d_ge_ten (s : Symbol) {u : Point} (hu : U u) : 10 ≤ Real.sqrt (d s u) := by
  apply (Real.le_sqrt (by norm_num) (d_pos s hu).le).2
  linarith [(d_bounds s hu).1]

theorem inverse_sqrt_d_le (s : Symbol) {u : Point} (hu : U u) :
    (Real.sqrt (d s u))⁻¹ ≤ 1 / 10 := by
  have h := sqrt_d_ge_ten s hu
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 10) h

/-- The scalar estimate in the proof of the fiber Lipschitz lemma. -/
theorem inverse_sqrt_d_difference (s : Symbol) {u v : Point} (hu : U u) (hv : U v) :
    |(Real.sqrt (d s u))⁻¹ - (Real.sqrt (d s v))⁻¹| ≤ (11 / 2000 : ℝ) * supDist u v := by
  let a := Real.sqrt (d s u)
  let b := Real.sqrt (d s v)
  have ha : 10 ≤ a := sqrt_d_ge_ten s hu
  have hb : 10 ≤ b := sqrt_d_ge_ten s hv
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hab0 : 0 < a + b := by linarith
  have ha2 : a ^ 2 = d s u := Real.sq_sqrt (d_pos s hu).le
  have hb2 : b ^ 2 = d s v := Real.sq_sqrt (d_pos s hv).le
  have he : a⁻¹ - b⁻¹ = (d s v - d s u) / (a * b * (a + b)) := by
    field_simp
    nlinarith
  have hab : 100 ≤ a * b := by nlinarith
  have hden : 2000 ≤ a * b * (a + b) := by nlinarith
  change |a⁻¹ - b⁻¹| ≤ _
  rw [he, abs_div, abs_of_pos (mul_pos (mul_pos ha0 hb0) hab0)]
  calc
    _ ≤ |d s v - d s u| / 2000 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden
    _ = |d s u - d s v| / 2000 := by rw [abs_sub_comm]
    _ ≤ (11 * supDist u v) / 2000 :=
      div_le_div_of_nonneg_right (d_difference s u v) (by norm_num)
    _ = _ := by ring

end HallRay

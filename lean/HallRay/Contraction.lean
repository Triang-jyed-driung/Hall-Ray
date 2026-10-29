module

public import HallRay.Branches

@[expose] public section

/-! The quantitative 1/900 branch contraction in Lemma 3.2.
We use the explicit maximum-coordinate distance to avoid any ambiguity
between the Euclidean and sup norms on pairs. -/
namespace HallRay

def supDist (u v : Point) : ℝ := max |u.1 - v.1| |u.2 - v.2|

private theorem fraction_bound {a b c f A B dx dy r : ℝ}
    (hc : 503 / 5 ≤ c) (hf : 503 / 5 ≤ f)
    (hA : |A| ≤ 501 / 50) (hB : |B| ≤ 6 / 5)
    (hx : |dx| ≤ r) (hy : |dy| ≤ r)
    (hid : a * f - b * c = A * dx + B * dy) :
    |a / c - b / f| ≤ r / 900 := by
  have hc0 : 0 < c := by linarith
  have hf0 : 0 < f := by linarith
  have hr : 0 ≤ r := le_trans (abs_nonneg dx) hx
  have hcf : (503 / 5 : ℝ) * (503 / 5) ≤ c * f :=
    mul_le_mul hc hf (by norm_num) (by linarith)
  rw [div_sub_div _ _ (ne_of_gt hc0) (ne_of_gt hf0), abs_div,
    abs_of_pos (mul_pos hc0 hf0), mul_comm c b, hid]
  have hnum : |A * dx + B * dy| ≤ (561 / 50 : ℝ) * r := by
    calc
      |A * dx + B * dy| ≤ |A * dx| + |B * dy| := abs_add_le _ _
      _ = |A| * |dx| + |B| * |dy| := by rw [abs_mul, abs_mul]
      _ ≤ (501 / 50 : ℝ) * r + (6 / 5 : ℝ) * r := by gcongr
      _ = (561 / 50 : ℝ) * r := by ring
  apply (div_le_iff₀ (mul_pos hc0 hf0)).2
  have hprod := mul_le_mul_of_nonneg_right hcf hr
  nlinarith

/-- Quantitative version of the unstable branch estimate. -/
theorem phi_contraction (s : Symbol) {u u' : Point} (hu : U u) (hu' : U u') :
    supDist (phi s u) (phi s u') ≤ supDist u u' / 900 := by
  have hx : |u.1 - u'.1| ≤ supDist u u' := le_max_left _ _
  have hy : |u.2 - u'.2| ≤ supDist u u' := le_max_right _ _
  have hx' : |u.2 - u'.2| ≤ supDist u u' := hy
  have hy' : |u.1 - u'.1| ≤ supDist u u' := hx
  obtain ⟨hxl, hxr⟩ := abs_le.mp hu.1
  obtain ⟨hyl, hyr⟩ := abs_le.mp hu.2
  have hs := sign_sq s
  change max _ _ ≤ _
  apply max_le
  · apply fraction_bound (d_bounds s hu).1 (d_bounds s hu').1
      (A := 10 - sign s * u.2) (B := sign s * (u.1 - 1)) (hx := hx) (hy := hy)
    · apply abs_le.mpr
      cases s <;> dsimp [sign] <;> constructor <;> linarith
    · apply abs_le.mpr
      cases s <;> dsimp [sign] <;> constructor <;> linarith
    · dsimp [d]
      ring
  · apply fraction_bound (d_bounds s hu).1 (d_bounds s hu').1
      (A := 10) (B := sign s) (hx := hx') (hy := hy')
    · norm_num
    · cases s <;> norm_num [sign]
    · dsimp [d]
      cases s <;> norm_num [sign] <;> ring

/-- Conjugacy exchanging stable and unstable rectangles. -/
def swapSign (s : Symbol) (v : Point) : Point := (-sign s * v.2, -sign s * v.1)

theorem swapSign_mem (s : Symbol) {v : Point} (hv : V v) : U (swapSign s v) := by
  cases s <;> simpa [U, swapSign, sign] using And.intro hv.2 hv.1

theorem supDist_swapSign (s : Symbol) (v v' : Point) :
    supDist (swapSign s v) (swapSign s v') = supDist v v' := by
  cases s <;> dsimp [supDist, swapSign, sign] <;>
    simp only [neg_one_mul, neg_neg, one_mul, neg_sub_neg, abs_sub_comm, max_comm]

theorem psi_conjugate (s : Symbol) (v : Point) :
    psi s v = swapSign s (phi s (swapSign s v)) := by
  cases s <;> ext <;> simp [psi, phi, swapSign, sign, d, e] <;> ring

theorem psi_contraction (s : Symbol) {v v' : Point} (hv : V v) (hv' : V v') :
    supDist (psi s v) (psi s v') ≤ supDist v v' / 900 := by
  rw [psi_conjugate, psi_conjugate, supDist_swapSign]
  have h := phi_contraction s (swapSign_mem s hv) (swapSign_mem s hv')
  rwa [supDist_swapSign] at h

end HallRay

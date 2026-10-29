module

public import HallRay.Branches
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Precise statements and the conditional Section 2 reduction.
`DaniCorrespondence` and `DynamicalHallRay` are propositions, not axioms.
The former is proved in `HallRay.Dani`; the latter is proved in `HallRay.Main`.
Both are explicit arguments to the general reduction `main_of_dani_and_ray`.
Extended nonnegative reals retain zero and infinite constants correctly. -/
@[expose] public section
noncomputable section
open Filter
open scoped ENNReal
namespace HallRay

/-- An arbitrary norm on the real plane, with all norm axioms explicit. -/
structure PlaneNorm where
  value : Point → ℝ
  nonneg : ∀ v, 0 ≤ value v
  eq_zero_iff : ∀ v, value v = 0 ↔ v = 0
  add_le : ∀ v w, value (v + w) ≤ value v + value w
  smul_eq : ∀ (r : ℝ) v, value (r • v) = |r| * value v

def integerPoint (p : ℤ × ℤ) : Point := ((p.1 : ℝ), (p.2 : ℝ))

/-- Equivalent to x belonging to Q²: both coordinates have a common denominator. -/
def RationalPair (x : Point) : Prop :=
  ∃ q : ℕ, 0 < q ∧ ∃ p : ℤ × ℤ, (q : ℝ) • x = integerPoint p

/-- The infimum equals the nearest-integer minimum once attainment is established. -/
def torusError (N : PlaneNorm) (x : Point) (q : ℕ) : ℝ≥0∞ :=
  ⨅ p : ℤ × ℤ, ENNReal.ofReal (N.value ((q : ℝ) • x - integerPoint p))

def approximationTerm (N : PlaneNorm) (x : Point) (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (q : ℝ)) * torusError N x q

def approximationConstant (N : PlaneNorm) (x : Point) : ℝ≥0∞ :=
  liminf (approximationTerm N x) atTop

/-- The lattice is specified by its integer vectors, without a quotient-space API. -/
def orbitSystole (N : PlaneNorm) (x : Point) (t : ℝ) : ℝ≥0∞ :=
  ⨅ w : {w : ℤ × (ℤ × ℤ) // w ≠ 0},
    ENNReal.ofReal (max (Real.exp (-2 * t) * |(w.val.1 : ℝ)|)
      (Real.exp t * N.value ((w.val.1 : ℝ) • x - integerPoint w.val.2)))

def orbitHeight (N : PlaneNorm) (x : Point) : ℝ≥0∞ :=
  limsup (fun t => (orbitSystole N x t)⁻¹) atTop

/-- The statement of Lemma 2.1, proved by `dani_correspondence` in `HallRay.Dani`. -/
def DaniCorrespondence (N : PlaneNorm) : Prop :=
  ∀ x, liminf (orbitSystole N x) atTop = approximationConstant N x ^ (2 / 3 : ℝ)

/-- Theorem `thm:proper-ray` specialized to inverse systole, proved in `HallRay.Main`. -/
def DynamicalHallRay (N : PlaneNorm) : Prop :=
  ∃ T : ℝ, 0 < T ∧ ∀ A : ℝ, T < A → ∃ x, orbitHeight N x = ENNReal.ofReal A

/-- The small-constant formulation of Theorem 1.2, for a specified norm. -/
def HasHallRay (N : PlaneNorm) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
    ∃ x : Point, ¬RationalPair x ∧ approximationConstant N x = ENNReal.ofReal ρ

/-- The paper's main assertion, proved by `HallRay.main_theorem` in `HallRay.Main`. -/
def MainTheorem : Prop := ∀ N : PlaneNorm, HasHallRay N

theorem rational_approximation_zero (N : PlaneNorm) {x : Point} (hx : RationalPair x) :
    approximationConstant N x = 0 := by
  obtain ⟨q₀, hq₀, p, hp⟩ := hx
  apply le_antisymm _ zero_le
  apply liminf_le_of_frequently_le'
  rw [frequently_atTop]
  intro n
  let k : ℕ := n + 1
  let p' : ℤ × ℤ := ((k : ℤ) * p.1, (k : ℤ) * p.2)
  refine ⟨k * q₀, by dsimp [k]; nlinarith, ?_⟩
  have hi : ((k * q₀ : ℕ) : ℝ) • x = integerPoint p' := by
    rw [Nat.cast_mul, mul_smul, hp]
    ext <;> simp [integerPoint, p', Prod.smul_mk]
  have hz : N.value (0 : Point) = 0 := (N.eq_zero_iff 0).2 rfl
  have herr : torusError N x (k * q₀) = 0 := by
    apply le_antisymm _ zero_le
    calc
      _ ≤ ENNReal.ofReal (N.value (((k * q₀ : ℕ) : ℝ) • x - integerPoint p')) :=
        iInf_le _ p'
      _ = 0 := by rw [hi, sub_self, hz, ENNReal.ofReal_zero]
  simp [approximationTerm, herr]

/-- The inversion of the liminf is valid even at 0 and infinity. -/
theorem height_eq_inverse_liminf (N : PlaneNorm) (x : Point) :
    orbitHeight N x = (liminf (orbitSystole N x) atTop)⁻¹ := by
  exact ENNReal.inv_liminf.symm

/-- Extract one exact approximation constant using Dani's correspondence. -/
theorem realize_constant_of_dani (N : PlaneNorm) (hdani : DaniCorrespondence N)
    {ρ : ℝ} (hρ : 0 < ρ) {x : Point}
    (hx : orbitHeight N x = ENNReal.ofReal (ρ ^ (-2 / 3 : ℝ))) :
    ¬RationalPair x ∧ approximationConstant N x = ENNReal.ofReal ρ := by
  have he : (approximationConstant N x ^ (2 / 3 : ℝ))⁻¹ =
      (ENNReal.ofReal ρ ^ (2 / 3 : ℝ))⁻¹ := by
    have hrpow : ENNReal.ofReal (ρ ^ (-2 / 3 : ℝ)) =
        (ENNReal.ofReal ρ ^ (2 / 3 : ℝ))⁻¹ := by
      rw [← ENNReal.ofReal_rpow_of_pos hρ,
        show (-2 / 3 : ℝ) = -(2 / 3 : ℝ) by ring, ENNReal.rpow_neg]
    rw [height_eq_inverse_liminf, hdani x] at hx
    exact hx.trans hrpow
  have hc : approximationConstant N x = ENNReal.ofReal ρ := by
    apply ENNReal.rpow_left_injective (by norm_num : (2 / 3 : ℝ) ≠ 0)
    simpa only [inv_inv] using congrArg (fun a : ℝ≥0∞ => a⁻¹) he
  refine ⟨?_, hc⟩
  intro hr
  have hz := rational_approximation_zero N hr
  have hp := ENNReal.ofReal_pos.mpr hρ
  rw [← hc, hz] at hp
  exact (lt_irrefl _ hp)

/-- The complete Section 2 reduction, with its two substantial inputs explicit.
This theorem does not claim to prove either input. -/
theorem main_of_dani_and_ray (N : PlaneNorm) (hdani : DaniCorrespondence N)
    (hray : DynamicalHallRay N) : HasHallRay N := by
  obtain ⟨T, hT, hray⟩ := hray
  refine ⟨T ^ (-3 / 2 : ℝ), Real.rpow_pos_of_pos hT _, ?_⟩
  intro ρ hρ hρ₀
  have hA : T < ρ ^ (-2 / 3 : ℝ) := by
    have h := Real.rpow_lt_rpow_of_neg hρ hρ₀ (by norm_num : (-2 / 3 : ℝ) < 0)
    rw [← Real.rpow_mul hT.le] at h
    norm_num at h
    convert h using 1
    congr 1
    ring
  obtain ⟨x, hx⟩ := hray _ hA
  exact ⟨x, realize_constant_of_dani N hdani hρ hx⟩

end HallRay

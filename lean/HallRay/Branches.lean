module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Explicit algebra for Section 3 of Cheung–Wang–Zhang.
The sign `1` represents a and `-1` represents b. -/
noncomputable section
namespace HallRay

abbrev Point := ℝ × ℝ

inductive Symbol where
  | a | b
  deriving DecidableEq, Repr

instance : Fintype Symbol where
  elems := {.a, .b}
  complete := by intro s; cases s <;> simp

def sign : Symbol → ℝ
  | .a => 1
  | .b => -1

@[simp] theorem sign_sq (s : Symbol) : sign s ^ 2 = 1 := by cases s <;> norm_num [sign]

def U (u : Point) : Prop := |u.1| ≤ 1 / 5 ∧ |u.2| ≤ 1 / 50

def V (v : Point) : Prop := |v.1| ≤ 1 / 50 ∧ |v.2| ≤ 1 / 5

def d (s : Symbol) (u : Point) : ℝ := 101 - u.1 - 10 * sign s * u.2

def e (s : Symbol) (v : Point) : ℝ := 101 + 10 * v.1 + sign s * v.2

def phi (s : Symbol) (u : Point) : Point :=
  ((10 - sign s * u.2) / d s u, sign s / d s u)

def psi (s : Symbol) (v : Point) : Point :=
  (-1 / e s v, -sign s * (10 + v.1) / e s v)

theorem d_bounds (s : Symbol) {u : Point} (hu : U u) :
    503 / 5 ≤ d s u ∧ d s u ≤ 507 / 5 := by
  obtain ⟨h₁, h₂⟩ := hu
  obtain ⟨h₁l, h₁r⟩ := abs_le.mp h₁
  obtain ⟨h₂l, h₂r⟩ := abs_le.mp h₂
  cases s <;> dsimp [d, sign] <;> constructor <;> linarith

theorem e_bounds (s : Symbol) {v : Point} (hv : V v) :
    503 / 5 ≤ e s v ∧ e s v ≤ 507 / 5 := by
  obtain ⟨h₁, h₂⟩ := hv
  obtain ⟨h₁l, h₁r⟩ := abs_le.mp h₁
  obtain ⟨h₂l, h₂r⟩ := abs_le.mp h₂
  cases s <;> dsimp [e, sign] <;> constructor <;> linarith

theorem d_pos (s : Symbol) {u : Point} (hu : U u) : 0 < d s u := by
  have := (d_bounds s hu).1
  linarith

theorem e_pos (s : Symbol) {v : Point} (hv : V v) : 0 < e s v := by
  have := (e_bounds s hv).1
  linarith

theorem phi_mem (s : Symbol) {u : Point} (hu : U u) : U (phi s u) := by
  have hd := d_pos s hu
  have hb := (d_bounds s hu).1
  obtain ⟨h₁, h₂⟩ := hu
  obtain ⟨h₂l, h₂r⟩ := abs_le.mp h₂
  change |(10 - sign s * u.2) / d s u| ≤ 1 / 5 ∧ |sign s / d s u| ≤ 1 / 50
  constructor <;> rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
  · apply abs_le.mpr
    cases s <;> simp only [sign] <;> constructor <;> linarith
  · cases s <;> norm_num [sign] at * <;> linarith

theorem psi_mem (s : Symbol) {v : Point} (hv : V v) : V (psi s v) := by
  have hd := e_pos s hv
  have hb := (e_bounds s hv).1
  obtain ⟨h₁, h₂⟩ := hv
  obtain ⟨h₁l, h₁r⟩ := abs_le.mp h₁
  change |(-1 : ℝ) / e s v| ≤ 1 / 50 ∧ |-sign s * (10 + v.1) / e s v| ≤ 1 / 5
  constructor <;> rw [abs_div, abs_of_pos hd, div_le_iff₀ hd]
  · norm_num
    linarith
  · apply abs_le.mpr
    cases s <;> simp only [sign] <;> constructor <;> linarith

theorem phi_second_pos {u : Point} (hu : U u) : 0 < (phi .a u).2 := by
  exact div_pos (by norm_num [sign]) (d_pos .a hu)

theorem phi_second_neg {u : Point} (hu : U u) : (phi .b u).2 < 0 := by
  exact div_neg_of_neg_of_pos (by norm_num [sign]) (d_pos .b hu)

theorem phi_disjoint {u u' : Point} (hu : U u) (hu' : U u') :
    phi .a u ≠ phi .b u' := by
  intro h
  have h₂ := congrArg Prod.snd h
  have := phi_second_pos hu
  have := phi_second_neg hu'
  linarith

theorem psi_second_neg {v : Point} (hv : V v) : (psi .a v).2 < 0 := by
  have hb := (abs_le.mp hv.1).1
  apply div_neg_of_neg_of_pos _ (e_pos .a hv)
  dsimp [sign]
  linarith

theorem psi_second_pos {v : Point} (hv : V v) : 0 < (psi .b v).2 := by
  have hb := (abs_le.mp hv.1).1
  apply div_pos _ (e_pos .b hv)
  dsimp [sign]
  linarith

theorem psi_disjoint {v v' : Point} (hv : V v) (hv' : V v') :
    psi .a v ≠ psi .b v' := by
  intro h
  have h₂ := congrArg Prod.snd h
  have := psi_second_neg hv
  have := psi_second_pos hv'
  linarith

/-- Injectivity on the rectangle; no assertion at poles of the rational map. -/
theorem phi_injective (s : Symbol) {u u' : Point} (hu : U u) (hu' : U u')
    (h : phi s u = phi s u') : u = u' := by
  have hd : d s u ≠ 0 := ne_of_gt (d_pos s hu)
  have hd' : d s u' ≠ 0 := ne_of_gt (d_pos s hu')
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [phi] at h₁ h₂
  rw [div_eq_div_iff hd hd'] at h₁ h₂
  have hs := sign_sq s
  have hs0 : sign s ≠ 0 := by cases s <;> norm_num [sign]
  have he : d s u = d s u' := by
    exact (mul_left_cancel₀ hs0 h₂).symm
  have hy : u.2 = u'.2 := by
    rw [he] at h₁
    have := mul_right_cancel₀ hd' h₁
    cases s <;> dsimp [sign] at this <;> linarith
  apply Prod.ext
  · dsimp [d] at he
    rw [hy] at he
    linarith
  · exact hy

theorem psi_injective (s : Symbol) {v v' : Point} (hv : V v) (hv' : V v')
    (h : psi s v = psi s v') : v = v' := by
  have hd : e s v ≠ 0 := ne_of_gt (e_pos s hv)
  have hd' : e s v' ≠ 0 := ne_of_gt (e_pos s hv')
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [psi] at h₁ h₂
  rw [div_eq_div_iff hd hd'] at h₁ h₂
  have he : e s v = e s v' := by linarith
  have hx : v.1 = v'.1 := by
    rw [he] at h₂
    have hh := mul_right_cancel₀ hd' h₂
    cases s <;> dsimp [sign] at hh <;> linarith
  apply Prod.ext hx
  dsimp [e] at he
  rw [hx] at he
  cases s <;> dsimp [sign] at he <;> linarith

/-- The unnormalized fiber numerator in (3.4). -/
def fiberNumerator (s : Symbol) (u : Point) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![10 - sign s * u.2, sign s * (u.1 - 1); sign s, 10]

theorem fiberNumerator_det (s : Symbol) (u : Point) :
    (fiberNumerator s u).det = d s u := by
  rw [Matrix.det_fin_two]
  simp [fiberNumerator, d]
  cases s <;> norm_num [sign] <;> ring

/-- The actual normalized cocycle M_s(u). -/
noncomputable def fiber (s : Symbol) (u : Point) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt (d s u))⁻¹ • fiberNumerator s u

theorem fiber_det (s : Symbol) {u : Point} (hu : U u) : (fiber s u).det = 1 := by
  have hd := d_pos s hu
  have hsq := Real.sq_sqrt (le_of_lt hd)
  have hn : Real.sqrt (d s u) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hd)
  simp only [fiber, Matrix.det_smul, Fintype.card_fin, fiberNumerator_det]
  field_simp
  nlinarith

/-- The two integral changes of marking in (3.1). -/
def gamma (s : Symbol) : Matrix (Fin 3) (Fin 3) ℤ :=
  match s with
  | .a => !![101, -1, -10; 10, 0, -1; 1, 0, 0]
  | .b => !![101, -1, 10; 10, 0, 1; -1, 0, 0]

theorem gamma_det (s : Symbol) : (gamma s).det = 1 := by
  cases s <;> norm_num [gamma, Matrix.det_fin_three]

end HallRay

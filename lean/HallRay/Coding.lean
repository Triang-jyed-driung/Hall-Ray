module

public import HallRay.IteratedSystem

/-! The continuous future/past coordinates of Proposition `prop:suspension-factor`.
Both coordinates are constructed as limits, rather than supplied as hypotheses. -/
@[expose] public section
noncomputable section
open Filter Topology
namespace HallRay

@[simp] theorem dist_eq_supDist (u v : Point) : dist u v = supDist u v := by
  simp [Prod.dist_eq, Real.dist_eq, supDist]

theorem U_zero : U (0, 0) := by norm_num [U]
theorem V_zero : V (0, 0) := by norm_num [V]

theorem U_closed : IsClosed {u : Point | U u} :=
  (isClosed_le (continuous_abs.comp continuous_fst) continuous_const).inter
    (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)

theorem V_closed : IsClosed {v : Point | V v} :=
  (isClosed_le (continuous_abs.comp continuous_fst) continuous_const).inter
    (isClosed_le (continuous_abs.comp continuous_snd) continuous_const)

theorem U_diameter {u v : Point} (hu : U u) (hv : U v) : supDist u v ≤ 2 / 5 := by
  apply max_le
  · calc
      |u.1 - v.1| ≤ |u.1| + |v.1| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le u.1 (-v.1)
      _ ≤ 2 / 5 := by linarith [hu.1, hv.1]
  · calc
      |u.2 - v.2| ≤ |u.2| + |v.2| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le u.2 (-v.2)
      _ ≤ 2 / 5 := by linarith [hu.2, hv.2]

theorem V_diameter {u v : Point} (hu : V u) (hv : V v) : supDist u v ≤ 2 / 5 := by
  apply max_le
  · calc
      |u.1 - v.1| ≤ |u.1| + |v.1| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le u.1 (-v.1)
      _ ≤ 2 / 5 := by linarith [hu.1, hv.1]
  · calc
      |u.2 - v.2| ≤ |u.2| + |v.2| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le u.2 (-v.2)
      _ ≤ 2 / 5 := by linarith [hu.2, hv.2]

theorem phi_continuousAt (s : Symbol) {u : Point} (hu : U u) : ContinuousAt (phi s) u := by
  have hd : d s u ≠ 0 := ne_of_gt (d_pos s hu)
  unfold phi d at *
  fun_prop

theorem psi_continuousAt (s : Symbol) {v : Point} (hv : V v) : ContinuousAt (psi s) v := by
  have he : e s v ≠ 0 := ne_of_gt (e_pos s hv)
  unfold psi e at *
  fun_prop

def futureSystem : IteratedSystem where
  region := {u | U u}
  closed := U_closed
  origin_mem := U_zero
  diameter := U_diameter
  branch := phi
  invariant := phi_mem
  contraction := phi_contraction
  continuousAt := phi_continuousAt

def pastSystem : IteratedSystem where
  region := {v | V v}
  closed := V_closed
  origin_mem := V_zero
  diameter := V_diameter
  branch := psi
  invariant := psi_mem
  contraction := psi_contraction
  continuousAt := psi_continuousAt

abbrev approx := futureSystem.approx
abbrev futureCode := futureSystem.code

theorem approx_mem (z : Word) (n : ℕ) : U (approx z n) := futureSystem.approx_mem z n

theorem approx_step (z : Word) (n : ℕ) :
    dist (approx z n) (approx z (n + 1)) ≤ (2 / 5 : ℝ) * (1 / 900 : ℝ) ^ n :=
  futureSystem.approx_step z n

theorem approx_cauchy (z : Word) : CauchySeq (approx z) := futureSystem.approx_cauchy z

theorem futureCode_tendsto (z : Word) : Tendsto (approx z) atTop (𝓝 (futureCode z)) :=
  futureSystem.code_tendsto z

theorem futureCode_mem (z : Word) : U (futureCode z) := futureSystem.code_mem z

theorem futureCode_recurrence (z : Word) :
    futureCode z = phi (z 0) (futureCode (shift 1 z)) := futureSystem.code_recurrence z

theorem futureCode_continuous : Continuous futureCode := futureSystem.code_continuous

def canonicalCoding : Coding where
  u := futureCode
  mem := futureCode_mem
  recurrence := futureCode_recurrence

theorem futureCode_closeness (N : ℕ) {z z' : Word}
    (h : ∀ i : ℕ, i < N → z (i : ℤ) = z' (i : ℤ)) :
    supDist (futureCode z) (futureCode z') ≤ (2 / 5 : ℝ) * (1 / 900 : ℝ) ^ N :=
  futureSystem.code_closeness N h

theorem futureCode_congr {z z' : Word}
    (h : ∀ i : ℕ, z (i : ℤ) = z' (i : ℤ)) : futureCode z = futureCode z' :=
  futureSystem.code_future_congr h

theorem futureCode_injective_on_futures {z z' : Word} (h : futureCode z = futureCode z') :
    ∀ n : ℕ, z (n : ℤ) = z' (n : ℤ) := canonicalCoding.future_eq h

def pastWord (z : Word) : Word := fun i => z (-i - 1)

def pastCode (z : Word) : Point := pastSystem.code (pastWord z)

theorem pastWord_continuous : Continuous pastWord := by
  apply continuous_pi
  intro i
  exact continuous_apply (-i - 1)

theorem pastCode_continuous : Continuous pastCode :=
  pastSystem.code_continuous.comp pastWord_continuous

theorem pastCode_mem (z : Word) : V (pastCode z) := pastSystem.code_mem _

theorem pastWord_shift (z : Word) : shift 1 (pastWord (shift 1 z)) = pastWord z := by
  funext i
  dsimp [shift, pastWord]
  congr 1
  ring

theorem pastCode_recurrence (z : Word) :
    pastCode (shift 1 z) = psi (z 0) (pastCode z) := by
  unfold pastCode
  rw [pastSystem.code_recurrence, pastWord_shift]
  rfl

theorem pastCode_closeness (N : ℕ) {z z' : Word}
    (h : ∀ i : ℕ, 1 ≤ i → i ≤ N → z (-(i : ℤ)) = z' (-(i : ℤ))) :
    supDist (pastCode z) (pastCode z') ≤ (2 / 5 : ℝ) * (1 / 900 : ℝ) ^ N := by
  apply pastSystem.code_closeness N
  intro i hi
  have hh := h (i + 1) (by omega) (by omega)
  simpa [pastWord, Nat.cast_add, Nat.cast_one, neg_add_rev, sub_eq_add_neg, add_comm] using hh

theorem pastCode_injective_on_pasts {z z' : Word} (h : pastCode z = pastCode z') :
    ∀ n : ℕ, z (-(n : ℤ) - 1) = z' (-(n : ℤ) - 1) := by
  exact pastSystem.code_future_eq
    (fun s _ hu _ hv he => psi_injective s hu hv he)
    (fun _ hu _ hv => psi_disjoint hu hv) h

def baseCode (z : Word) : Point × Point := (futureCode z, pastCode z)

theorem baseCode_continuous : Continuous baseCode :=
  futureCode_continuous.prodMk pastCode_continuous

theorem baseCode_injective : Function.Injective baseCode := by
  intro z z' h
  have hf := futureCode_injective_on_futures (congrArg Prod.fst h)
  have hp := pastCode_injective_on_pasts (congrArg Prod.snd h)
  funext i
  by_cases hi : 0 ≤ i
  · simpa [Int.toNat_of_nonneg hi] using hf i.toNat
  · have hin : 0 ≤ -i - 1 := by omega
    have he : -(((-i - 1).toNat : ℕ) : ℤ) - 1 = i := by
      rw [Int.toNat_of_nonneg hin]
      omega
    simpa only [he] using hp (-i - 1).toNat

/-- The compact horseshoe base, with its full two-sided symbolic parameterization. -/
def horseshoe : Set (Point × Point) := Set.range baseCode

theorem horseshoe_compact : IsCompact horseshoe := isCompact_range baseCode_continuous

theorem baseCode_isClosedEmbedding : Topology.IsClosedEmbedding baseCode :=
  baseCode_continuous.isClosedEmbedding baseCode_injective

def codingHomeomorph : Word ≃ₜ horseshoe := baseCode_isClosedEmbedding.isEmbedding.toHomeomorph

theorem shift_continuous (k : ℤ) : Continuous (shift k) := by
  apply continuous_pi
  intro i
  exact continuous_apply (i + k)

def shiftHomeomorph (k : ℤ) : Word ≃ₜ Word where
  toFun := shift k
  invFun := shift (-k)
  left_inv := by intro z; simp
  right_inv := by intro z; simp
  continuous_toFun := shift_continuous k
  continuous_invFun := shift_continuous (-k)

/-- The return homeomorphism on the horseshoe is conjugate to the full shift. -/
def horseshoeReturn : horseshoe ≃ₜ horseshoe :=
  codingHomeomorph.symm.trans ((shiftHomeomorph 1).trans codingHomeomorph)

theorem horseshoeReturn_code (z : Word) :
    horseshoeReturn (codingHomeomorph z) = codingHomeomorph (shift 1 z) := by
  simp [horseshoeReturn, shiftHomeomorph]

def constantWord : Word := fun _ => .a

theorem constantWord_shift : shift 1 constantWord = constantWord := rfl

theorem constantCode_fixed : phi .a (futureCode constantWord) = futureCode constantWord := by
  have h := futureCode_recurrence constantWord
  simpa [constantWord_shift, constantWord] using h.symm

end HallRay

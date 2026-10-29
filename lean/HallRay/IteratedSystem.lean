module

public import HallRay.Contraction
public import HallRay.Symbolic
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
noncomputable section
open Filter Topology
namespace HallRay

/-- A uniform contracting system on a closed rectangle in the real plane.
The constants match the two systems of Section 3. -/
structure IteratedSystem where
  region : Set Point
  closed : IsClosed region
  origin_mem : (0, 0) ∈ region
  diameter : ∀ {u v}, u ∈ region → v ∈ region → supDist u v ≤ 2 / 5
  branch : Symbol → Point → Point
  invariant : ∀ s {u}, u ∈ region → branch s u ∈ region
  contraction : ∀ s {u v}, u ∈ region → v ∈ region →
    supDist (branch s u) (branch s v) ≤ supDist u v / 900
  continuousAt : ∀ s {u}, u ∈ region → ContinuousAt (branch s) u

namespace IteratedSystem

variable (S : IteratedSystem)

private theorem dist_formula (u v : Point) : dist u v = supDist u v := by
  simp [Prod.dist_eq, Real.dist_eq, supDist]

def approx (S : IteratedSystem) (z : Word) : ℕ → Point
  | 0 => (0, 0)
  | n + 1 => S.branch (z 0) (S.approx (shift 1 z) n)

theorem approx_mem (z : Word) (n : ℕ) : S.approx z n ∈ S.region := by
  induction n generalizing z with
  | zero => exact S.origin_mem
  | succ n ih => exact S.invariant _ (ih _)

theorem approx_step (z : Word) (n : ℕ) :
    dist (S.approx z n) (S.approx z (n + 1)) ≤ (2 / 5 : ℝ) * (1 / 900 : ℝ) ^ n := by
  induction n generalizing z with
  | zero => simpa [dist_formula] using S.diameter (S.approx_mem z 0) (S.approx_mem z 1)
  | succ n ih =>
    change dist (S.branch (z 0) (S.approx (shift 1 z) n))
      (S.branch (z 0) (S.approx (shift 1 z) (n + 1))) ≤ _
    rw [dist_formula]
    calc
      _ ≤ supDist (S.approx (shift 1 z) n) (S.approx (shift 1 z) (n + 1)) / 900 :=
        S.contraction _ (S.approx_mem _ _) (S.approx_mem _ _)
      _ ≤ ((2 / 5 : ℝ) * (1 / 900 : ℝ) ^ n) / 900 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        simpa [dist_formula] using ih (shift 1 z)
      _ = _ := by rw [pow_succ]; ring

theorem approx_cauchy (z : Word) : CauchySeq (S.approx z) :=
  cauchySeq_of_le_geometric (1 / 900) (2 / 5) (by norm_num) (S.approx_step z)

def code (z : Word) : Point :=
  Classical.choose (cauchySeq_tendsto_of_complete (S.approx_cauchy z))

theorem code_tendsto (z : Word) : Tendsto (S.approx z) atTop (𝓝 (S.code z)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (S.approx_cauchy z))

theorem code_mem (z : Word) : S.code z ∈ S.region :=
  S.closed.mem_of_tendsto (S.code_tendsto z) (Eventually.of_forall (S.approx_mem z))

theorem code_recurrence (z : Word) :
    S.code z = S.branch (z 0) (S.code (shift 1 z)) := by
  have h₁ : Tendsto (fun n => S.approx z (n + 1)) atTop (𝓝 (S.code z)) :=
    (S.code_tendsto z).comp (tendsto_add_atTop_nat 1)
  have h₂ : Tendsto (fun n => S.approx z (n + 1)) atTop
      (𝓝 (S.branch (z 0) (S.code (shift 1 z)))) :=
    (S.continuousAt _ (S.code_mem _)).tendsto.comp (S.code_tendsto _)
  exact tendsto_nhds_unique h₁ h₂

theorem code_closeness (N : ℕ) {z z' : Word}
    (h : ∀ i : ℕ, i < N → z (i : ℤ) = z' (i : ℤ)) :
    supDist (S.code z) (S.code z') ≤ (2 / 5 : ℝ) * (1 / 900 : ℝ) ^ N := by
  induction N generalizing z z' with
  | zero => simpa using S.diameter (S.code_mem z) (S.code_mem z')
  | succ N ih =>
    have h₀ := h 0 (Nat.zero_lt_succ N)
    simp only [Nat.cast_zero] at h₀
    have ht : ∀ i : ℕ, i < N → (shift 1 z) (i : ℤ) = (shift 1 z') (i : ℤ) := by
      intro i hi
      simpa [shift, Nat.cast_add, Nat.cast_one] using h (i + 1) (by omega)
    rw [S.code_recurrence z, S.code_recurrence z', h₀]
    calc
      _ ≤ supDist (S.code (shift 1 z)) (S.code (shift 1 z')) / 900 :=
        S.contraction _ (S.code_mem _) (S.code_mem _)
      _ ≤ ((2 / 5 : ℝ) * (1 / 900 : ℝ) ^ N) / 900 :=
        div_le_div_of_nonneg_right (ih ht) (by norm_num)
      _ = _ := by rw [pow_succ]; ring

/-- Continuity for the product topology on the two-sided full shift. -/
theorem code_continuous : Continuous S.code := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => (2 / 5 : ℝ) * (1 / 900 : ℝ) ^ n)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 900)
        (by norm_num : (1 / 900 : ℝ) < 1))
  obtain ⟨N, hN⟩ := (hlim.eventually_lt_const hε).exists
  have hcyl : ∀ᶠ w : Word in 𝓝 z, ∀ i ∈ Finset.range N, w (i : ℤ) = z (i : ℤ) := by
    apply (Finset.eventually_all _).mpr
    intro i hi
    have heval : Continuous (fun w : Word => w (i : ℤ)) := continuous_apply _
    have hopen : IsOpen {w : Word | w (i : ℤ) = z (i : ℤ)} :=
      (isOpen_discrete ({z (i : ℤ)} : Set Symbol)).preimage heval
    exact hopen.mem_nhds rfl
  filter_upwards [hcyl] with w hw
  rw [dist_formula]
  exact lt_of_le_of_lt (S.code_closeness N (fun i hi => hw i (Finset.mem_range.mpr hi))) hN

/-- Only the nonnegative symbols affect this contracting coordinate. -/
theorem code_future_congr {z z' : Word}
    (h : ∀ i : ℕ, z (i : ℤ) = z' (i : ℤ)) : S.code z = S.code z' := by
  have happ : ∀ n : ℕ, S.approx z n = S.approx z' n := by
    intro n
    induction n generalizing z z' with
    | zero => rfl
    | succ n ih =>
      change S.branch (z 0) (S.approx (shift 1 z) n) =
        S.branch (z' 0) (S.approx (shift 1 z') n)
      have h₀ := h 0
      simp only [Nat.cast_zero] at h₀
      rw [h₀]
      congr 1
      apply ih
      intro i
      simpa [shift, Nat.cast_add, Nat.cast_one] using h (i + 1)
  have ht : Tendsto (S.approx z') atTop (𝓝 (S.code z)) := by
    rw [← (funext happ : S.approx z = S.approx z')]
    exact S.code_tendsto z
  exact tendsto_nhds_unique ht (S.code_tendsto z')

/-- Disjoint branch images distinguish the initial symbol. -/
theorem code_symbol_eq
    (hdis : ∀ u ∈ S.region, ∀ v ∈ S.region, S.branch .a u ≠ S.branch .b v)
    {z z' : Word} (h : S.code z = S.code z') : z 0 = z' 0 := by
  rw [S.code_recurrence z, S.code_recurrence z'] at h
  cases hz : z 0 <;> cases hz' : z' 0 <;> try rfl
  · rw [hz, hz'] at h
    exact False.elim (hdis _ (S.code_mem _) _ (S.code_mem _) h)
  · rw [hz, hz'] at h
    exact False.elim (hdis _ (S.code_mem _) _ (S.code_mem _) h.symm)

theorem code_future_eq
    (hinj : ∀ s, ∀ u ∈ S.region, ∀ v ∈ S.region, S.branch s u = S.branch s v → u = v)
    (hdis : ∀ u ∈ S.region, ∀ v ∈ S.region, S.branch .a u ≠ S.branch .b v)
    {z z' : Word} (h : S.code z = S.code z') :
    ∀ n : ℕ, z (n : ℤ) = z' (n : ℤ) := by
  have hnext : ∀ {w w' : Word}, S.code w = S.code w' →
      S.code (shift 1 w) = S.code (shift 1 w') := by
    intro w w' he
    have hs := S.code_symbol_eq hdis he
    rw [S.code_recurrence w, S.code_recurrence w', hs] at he
    exact hinj _ _ (S.code_mem _) _ (S.code_mem _) he
  have hcoords : ∀ n : ℕ, S.code (shift (n : ℤ) z) = S.code (shift (n : ℤ) z') := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have hn := hnext ih
      simpa only [shift_add, Nat.cast_add, Nat.cast_one, add_comm (1 : ℤ)] using hn
  intro n
  have hs := S.code_symbol_eq hdis (hcoords n)
  simpa [shift] using hs

end IteratedSystem
end HallRay

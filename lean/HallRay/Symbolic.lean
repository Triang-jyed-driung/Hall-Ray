module

public import HallRay.Branches

@[expose] public section

/-! The algebraic part of the symbolic coding and finite cocycle arguments.
Existence/continuity of the infinite coding map is NOT assumed globally:
`Coding` is an explicit hypothesis for the results that use it. -/
namespace HallRay

instance : TopologicalSpace Symbol := ⊥
instance : DiscreteTopology Symbol := ⟨rfl⟩

abbrev Word := ℤ → Symbol

def shift (k : ℤ) (z : Word) : Word := fun i => z (i + k)

@[simp] theorem shift_zero (z : Word) : shift 0 z = z := by funext i; simp [shift]

@[simp] theorem shift_add (k l : ℤ) (z : Word) :
    shift k (shift l z) = shift (k + l) z := by
  funext i
  simp [shift, Int.add_assoc]

/-- Products are in increasing time order, as in the paper. -/
def cocycle {G : Type*} [Monoid G] (M : Word → G) (z : Word) : ℕ → G
  | 0 => 1
  | n + 1 => cocycle M z n * M (shift (n : ℤ) z)

@[simp] theorem cocycle_zero {G : Type*} [Monoid G] (M : Word → G) (z : Word) :
    cocycle M z 0 = 1 := rfl

@[simp] theorem cocycle_succ {G : Type*} [Monoid G] (M : Word → G) (z : Word) (n : ℕ) :
    cocycle M z (n + 1) = cocycle M z n * M (shift (n : ℤ) z) := rfl

theorem cocycle_add {G : Type*} [Monoid G] (M : Word → G) (z : Word) (k l : ℕ) :
    cocycle M z (k + l) = cocycle M z k * cocycle M (shift (k : ℤ) z) l := by
  induction l with
  | zero => simp
  | succ l ih =>
    simp only [Nat.add_succ, cocycle_succ, ih, mul_assoc, shift_add, Nat.cast_add]
    rw [add_comm (l : ℤ) (k : ℤ)]

theorem cocycle_head {G : Type*} [Monoid G] (M : Word → G) (z : Word) (n : ℕ) :
    cocycle M z (n + 1) = M z * cocycle M (shift 1 z) n := by
  have h := cocycle_add M z 1 n
  simpa [cocycle_succ, Nat.add_comm 1] using h

/-- Exact repetition of a periodic code gives powers of its period matrix. -/
theorem cocycle_periods {G : Type*} [Monoid G] (M : Word → G) (z : Word)
    (p : ℕ) (hp : shift (p : ℤ) z = z) (k : ℕ) :
    cocycle M z (k * p) = cocycle M z p ^ k := by
  have hshift : ∀ k : ℕ, shift ((k * p : ℕ) : ℤ) z = z := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, Nat.cast_add, ← shift_add, hp, ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, cocycle_add, hshift, ih, pow_succ]

theorem cocycle_periods_remainder {G : Type*} [Monoid G] (M : Word → G) (z : Word)
    (p : ℕ) (hp : shift (p : ℤ) z = z) (k j : ℕ) :
    cocycle M z (k * p + j) = cocycle M z p ^ k * cocycle M z j := by
  have hshift : shift ((k * p : ℕ) : ℤ) z = z := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.succ_mul, Nat.cast_add, ← shift_add, hp, ih]
  rw [cocycle_add, hshift, cocycle_periods M z p hp k]

/-- The hypotheses supplied by the contracting-branch construction. -/
structure Coding where
  u : Word → Point
  mem : ∀ z, U (u z)
  recurrence : ∀ z, u z = phi (z 0) (u (shift 1 z))

/-- The disjoint branches identify the first symbol from its coded coordinate. -/
theorem Coding.symbol_eq (c : Coding) {z z' : Word} (h : c.u z = c.u z') :
    z 0 = z' 0 := by
  rw [c.recurrence z, c.recurrence z'] at h
  cases hz : z 0 <;> cases hz' : z' 0 <;> try rfl
  · rw [hz, hz'] at h
    exact False.elim (phi_disjoint (c.mem _) (c.mem _) h)
  · rw [hz, hz'] at h
    exact False.elim (phi_disjoint (c.mem _) (c.mem _) h.symm)

theorem Coding.next_eq (c : Coding) {z z' : Word} (h : c.u z = c.u z') :
    c.u (shift 1 z) = c.u (shift 1 z') := by
  have hs := c.symbol_eq h
  rw [c.recurrence z, c.recurrence z', hs] at h
  exact phi_injective _ (c.mem _) (c.mem _) h

/-- The last injectivity argument in Section 6: equal coordinates imply equal futures.
This does not assert that past coordinates agree. -/
theorem Coding.future_eq (c : Coding) {z z' : Word} (h : c.u z = c.u z') :
    ∀ n : ℕ, z (n : ℤ) = z' (n : ℤ) := by
  have hcoords : ∀ n : ℕ, c.u (shift (n : ℤ) z) = c.u (shift (n : ℤ) z') := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih =>
      have hn := c.next_eq ih
      simpa only [shift_add, Nat.cast_add, Nat.cast_one, add_comm (1 : ℤ)] using hn
  intro n
  have hs := c.symbol_eq (hcoords n)
  simpa [shift] using hs

end HallRay

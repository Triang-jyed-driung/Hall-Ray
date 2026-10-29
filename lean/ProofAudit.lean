import HallRay.Main

/-!
An independent entry-point check for the paper's main Hall-ray statement.
The final declaration must use only Lean's standard logical axioms:
`propext`, `Classical.choice`, and `Quot.sound`.
-/

#check HallRay.main_theorem
/-- info: 'HallRay.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HallRay.main_theorem

/-- Unfolding the bundled statement exposes the exact small-constant formulation. -/
example (N : HallRay.PlaneNorm) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρ₀ →
      ∃ x : HallRay.Point, ¬HallRay.RationalPair x ∧
        HallRay.approximationConstant N x = ENNReal.ofReal ρ :=
  HallRay.hall_ray N

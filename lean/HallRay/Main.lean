module

public import HallRay.ForgettingPast
public import HallRay.Dani

@[expose] public section
noncomputable section
namespace HallRay

/-- The dynamical Hall ray for inverse systole on the Diophantine initial lattices. -/
theorem dynamical_hall_ray (N : PlaneNorm) : DynamicalHallRay N := by
  obtain ⟨T, hT, hcodes⟩ := coded_hall_ray N
  refine ⟨T, hT, ?_⟩
  intro A hA
  obtain ⟨z, hz⟩ := hcodes A hA
  exact ⟨futureCode z, (codedOrbitHeight_eq_orbitHeight N z).symm.trans hz⟩

/-- The main theorem of the paper: every plane norm has a Hall ray in dimension two. -/
theorem hall_ray (N : PlaneNorm) : HasHallRay N :=
  main_of_dynamical_ray N (dynamical_hall_ray N)

/-- The unconditional, universally quantified main assertion. -/
theorem main_theorem : MainTheorem := hall_ray

end HallRay

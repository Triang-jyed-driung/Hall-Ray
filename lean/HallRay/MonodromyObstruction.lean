module

public import HallRay.ArithmeticObstruction
public import HallRay.Lattices
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section
noncomputable section
namespace HallRay

/-- An integral unimodular cubic cannot split into (X-A)(X-r)^2 for 0<r<1. -/
theorem no_integral_cubic_split (p : Polynomial ℤ) (hp0 : p.coeff 0 = -1)
    {A r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hp : p.map (Int.castRingHom ℝ) =
      (Polynomial.X - Polynomial.C A) * (Polynomial.X - Polynomial.C r) ^ 2) : False := by
  have he : p.map (Int.castRingHom ℝ) =
      Polynomial.X ^ 3 - Polynomial.C (A + 2 * r) * Polynomial.X ^ 2 +
        Polynomial.C (2 * A * r + r ^ 2) * Polynomial.X - Polynomial.C (A * r ^ 2) := by
    rw [hp]
    simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow, map_ofNat]
    ring
  have h0 := congrArg (fun q : Polynomial ℝ => q.coeff 0) he
  have h1 := congrArg (fun q : Polynomial ℝ => q.coeff 1) he
  have h2 := congrArg (fun q : Polynomial ℝ => q.coeff 2) he
  simp only [Polynomial.coeff_map, Polynomial.coeff_sub, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_X, Polynomial.coeff_X_pow, Polynomial.coeff_C, hp0] at h0 h1 h2
  norm_num at h0 h1 h2
  apply no_repeated_contracting_root (-p.coeff 2) (p.coeff 1) (A := A) hr hr1
  · linarith
  · push_cast
    linarith
  · exact h1

/-- No unimodular integer frame change is similar to a diagonal matrix with
one expanding and two equal positive contracting eigenvalues. -/
theorem no_contracting_scalar_monodromy (Γ : Matrix (Fin 3) (Fin 3) ℤ) (hΓ : Γ.det = 1)
    (C : Mat3) (hC : C.det = 1) {A r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hconj : C * Γ.map (Int.castRingHom ℝ) * C⁻¹ = Matrix.diagonal ![A, r, r]) : False := by
  have hCinv : C⁻¹ * C = 1 := Matrix.nonsing_inv_mul C (by rw [hC]; exact isUnit_one)
  have hchar : (C * Γ.map (Int.castRingHom ℝ) * C⁻¹).charpoly =
      (Γ.map (Int.castRingHom ℝ)).charpoly := by
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hCinv, one_mul]
  rw [hconj, Matrix.charpoly_map] at hchar
  have hp0 : Γ.charpoly.coeff 0 = -1 := by
    have h := Matrix.det_eq_sign_charpoly_coeff Γ
    norm_num [hΓ] at h
    linarith
  apply no_integral_cubic_split Γ.charpoly hp0 hr hr1
  rw [← hchar, Matrix.charpoly_diagonal]
  simp [Fin.prod_univ_succ]
  ring

end HallRay

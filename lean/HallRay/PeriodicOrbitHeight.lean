module

public import HallRay.PeriodicCompactSets
public import HallRay.SystoleLattice
public import HallRay.FlightDecomposition

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- Every forward orbit point has a representative in the compact periodic family. -/
theorem periodic_orbit_representative (n : ℕ) (h : Admissible n) {t : ℝ} (ht : 0 ≤ t) :
    ∃ A ∈ periodicFrames n,
      frameLattice (flow t * codedChart (periodicWord n) 1) = frameLattice A := by
  obtain ⟨k, j, r, heq, hr0, hr1⟩ := periodic_flight_decomposition n ht
  let z := shift (j.val : ℤ) (periodicWord n)
  have hroof : 0 < roof z := lt_trans (by norm_num) (roof_gt_one z)
  let a : FlightParameter := ⟨r / roof z,
    ⟨div_nonneg hr0 hroof.le, (div_le_one hroof).mpr hr1⟩⟩
  let p : Real.Angle × FlightParameter := (k • (ellipticAngle (periodMatrix n) : Real.Angle), a)
  refine ⟨periodicFrame n j p, Set.mem_iUnion.mpr ⟨j, ⟨p, rfl⟩⟩, ?_⟩
  rw [heq]
  have hh := periodic_complete_orbit n k j.val 1 r
  simpa only [periodicFrame, p, a, z, div_mul_cancel₀ r hroof.ne',
    ellipticCircle_phase (periodMatrix_det n) h, one_mul] using hh

/-- The finite maximum controls the complete forward periodic-code orbit. -/
theorem periodic_orbit_height_bounded (N : PlaneNorm) (n : ℕ) (h : Admissible n) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ t : ℝ, 0 ≤ t →
      frameHeight N (flow t * codedChart (periodicWord n) 1) ≤ M := by
  obtain ⟨A, hA, hfin, hmax⟩ := periodic_height_maximum N n h
  refine ⟨frameHeight N A, hfin, ?_⟩
  intro t ht
  obtain ⟨B, hB, heq⟩ := periodic_orbit_representative n h ht
  rw [frameHeight_of_lattice_eq N _ B ?_ ?_ heq]
  · exact hmax B hB
  · rw [Matrix.det_mul, flow_det, codedChart_det _ (by simp), one_mul]
    norm_num
  · rw [periodicFrames_det n h hB]
    norm_num

theorem periodic_complete_height (N : PlaneNorm) (n k j : ℕ) (r : ℝ) :
    frameHeight N (flow ((k : ℝ) * periodTime n + timeSum (periodicWord n) j + r) *
      codedChart (periodicWord n) 1) =
    frameHeight N (flow r * codedChart (shift (j : ℤ) (periodicWord n))
      (periodMatrix n ^ k * cocycle fiberMap (periodicWord n) j)) := by
  apply frameHeight_of_lattice_eq
  · rw [Matrix.det_mul, flow_det, codedChart_det _ (by simp), one_mul]
    norm_num
  · rw [Matrix.det_mul, flow_det, one_mul]
    have hE : (periodMatrix n ^ k * cocycle fiberMap (periodicWord n) j).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_pow, periodMatrix_det, fiberProduct_det, one_pow, one_mul]
    rw [codedChart_det _ hE]
    norm_num
  · simpa only [one_mul] using periodic_complete_orbit n k j 1 r

/-- Every point of the compact family is approached in height at arbitrarily late times. -/
theorem periodic_frame_height_approximated (N : PlaneNorm) (n : ℕ) (h : Admissible n)
    (j : Fin (n + 1)) (p : Real.Angle × FlightParameter) :
    ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧
      Tendsto (fun i => frameHeight N (flow (t i) * codedChart (periodicWord n) 1)) atTop
        (𝓝 (frameHeight N (periodicFrame n j p))) := by
  obtain ⟨k, hk, hpow⟩ := (elliptic_power_cluster (periodMatrix_det n) h
    (periodic_angle_irrational n h) p.1).tendsto_subseq
  let r := (p.2 : ℝ) * roof (shift (j.val : ℤ) (periodicWord n))
  let t := fun i => (k i : ℝ) * periodTime n + timeSum (periodicWord n) j.val + r
  refine ⟨t, ?_, ?_⟩
  · have hcast : Tendsto (fun i => (k i : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hk.tendsto_atTop
    exact ((hcast.atTop_mul_const (periodTime_pos n)).atTop_add tendsto_const_nhds).atTop_add
      tendsto_const_nhds
  · have hc : Continuous (fun Q : Mat2 => flow r *
        codedChart (shift (j.val : ℤ) (periodicWord n))
          (Q * cocycle fiberMap (periodicWord n) j.val)) :=
      continuous_const.mul ((codedChart_fixed_continuous _).comp (continuous_id.mul_const _))
    have hmat : Tendsto (fun i => flow r *
        codedChart (shift (j.val : ℤ) (periodicWord n))
          (periodMatrix n ^ k i * cocycle fiberMap (periodicWord n) j.val)) atTop
        (𝓝 (periodicFrame n j p)) := hc.continuousAt.tendsto.comp hpow
    have hheight := (frameHeight_continuousAt N (periodicFrame n j p)
      (by rw [periodicFrame_det n h]; norm_num)).tendsto.comp hmat
    simpa only [t, periodic_complete_height, Function.comp_def] using hheight

/-- The exact periodic-code limsup is the finite maximum over the compact representatives.
This avoids needing a quotient-space or Lie-torus API for the height argument. -/
theorem periodic_height_limsup (N : PlaneNorm) (n : ℕ) (h : Admissible n) :
    ∃ A ∈ periodicFrames n, frameHeight N A ≠ ⊤ ∧
      (limsup (fun t : ℝ => frameHeight N (flow t * codedChart (periodicWord n) 1)) atTop =
        frameHeight N A) := by
  obtain ⟨A, hA, hfin, hmax⟩ := periodic_height_maximum N n h
  refine ⟨A, hA, hfin, le_antisymm ?_ ?_⟩
  · apply limsup_le_of_le (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    obtain ⟨B, hB, heq⟩ := periodic_orbit_representative n h ht
    rw [frameHeight_of_lattice_eq N _ B ?_ ?_ heq]
    · exact hmax B hB
    · rw [Matrix.det_mul, flow_det, codedChart_det _ (by simp), one_mul]
      norm_num
    · rw [periodicFrames_det n h hB]
      norm_num
  · obtain ⟨j, p, rfl⟩ := Set.mem_iUnion.mp hA
    obtain ⟨t, ht, hheight⟩ := periodic_frame_height_approximated N n h j p
    have hc : MapClusterPt (frameHeight N (periodicFrame n j p)) atTop
        (fun t : ℝ => frameHeight N (flow t * codedChart (periodicWord n) 1)) :=
      MapClusterPt.of_comp ht hheight.mapClusterPt
    exact hc.le_limsup

end HallRay

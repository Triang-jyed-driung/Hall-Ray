module

public import HallRay.SpliceEstimates

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

abbrev UPoint := {u : Point // U u}
abbrev VPoint := {v : Point // V v}

instance : CompactSpace UPoint := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Point) (1 / 5 : ℝ)).of_isClosed_subset U_closed
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le hu.1 (hu.2.trans (by norm_num))
instance : CompactSpace VPoint := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Point) (1 / 5 : ℝ)).of_isClosed_subset V_closed
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (hv.1.trans (by norm_num)) hv.2

abbrev BoundedFiber (B : ℝ) := {Q : Mat2 // Q.det = 1 ∧ ‖Q‖ ≤ B}

instance boundedFiber_compact (B : ℝ) : CompactSpace (BoundedFiber B) := by
  apply isCompact_iff_compactSpace.mp
  have hc : IsClosed {Q : Mat2 | Q.det = 1 ∧ ‖Q‖ ≤ B} :=
    (isClosed_eq continuous_id.matrix_det continuous_const).inter
      (isClosed_le continuous_norm continuous_const)
  exact (isCompact_closedBall (0 : Mat2) B).of_isClosed_subset hc
    (fun Q hQ => by simpa only [Metric.mem_closedBall, dist_zero_right] using hQ.2)

/-- A return flight in coordinates before taking the symbolic coding. -/
def returnModelFrame (s : Symbol) (u v : Point) (Q : Mat2) (a : ℝ) : Mat3 :=
  flow (a * returnTime s u v) * chart (phi s u) v Q

/-- Joint chart continuity on the invariant rectangles. -/
theorem chart_joint_continuousAt {u v : Point} (hu : U u) (hv : V v) (Q : Mat2) :
    ContinuousAt (fun p : Point × (Point × Mat2) => chart p.1 p.2.1 p.2.2) (u, v, Q) := by
  have hp : 1 + dot v u ≠ 0 := by have h := chart_positive hu hv; linarith
  have hd : Continuous (fun p : Point × (Point × Mat2) => 1 + dot p.2.1 p.1) := by unfold dot; fun_prop
  have hs : ContinuousAt (fun p : Point × (Point × Mat2) => chartScale p.1 p.2.1) (u, v, Q) :=
    Real.continuous_exp.continuousAt.comp ((hd.continuousAt.log hp).neg.div_const 3)
  unfold chart
  apply hs.smul
  apply ContinuousAt.mul
  · apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> dsimp [blockFiber] <;> fun_prop
  · apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    fin_cases i <;> fin_cases j <;> dsimp [rawChart] <;> fun_prop

abbrev FlightData (B : ℝ) := UPoint × (VPoint × (BoundedFiber B × FlightParameter))

def modelFlightHeight (N : PlaneNorm) (s : Symbol) {B : ℝ} (p : FlightData B) : ℝ :=
  (frameHeight N (returnModelFrame s p.1.val p.2.1.val p.2.2.1.val p.2.2.2)).toReal

theorem returnModelFrame_det (s : Symbol) {u v : Point} (hu : U u) (hv : V v) {Q : Mat2}
    (hQ : Q.det = 1) (a : ℝ) : (returnModelFrame s u v Q a).det = 1 := by
  rw [returnModelFrame, Matrix.det_mul, flow_det, chart_det (phi_mem s hu) hv hQ, one_mul]

theorem modelFlightHeight_continuous (N : PlaneNorm) (s : Symbol) (B : ℝ) :
    Continuous (modelFlightHeight N s (B := B)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hu : Continuous (fun q : FlightData B => q.1.val) := by fun_prop
  have hv : Continuous (fun q : FlightData B => q.2.1.val) := by fun_prop
  have hQ : Continuous (fun q : FlightData B => q.2.2.1.val) := by fun_prop
  have ha : Continuous (fun q : FlightData B => (q.2.2.2 : ℝ)) := by fun_prop
  have hd : Continuous (fun q : FlightData B => d s q.1.val) := by unfold d; fun_prop
  have he : Continuous (fun q : FlightData B => e s q.2.1.val) := by unfold e; fun_prop
  have ht : ContinuousAt (fun q : FlightData B => returnTime s q.1.val q.2.1.val) p :=
    ((hd.continuousAt.log (ne_of_gt (d_pos s p.1.property))).div_const 6).add
      ((he.continuousAt.log (ne_of_gt (e_pos s p.2.1.property))).div_const 3)
  have hphi : ContinuousAt (fun q : FlightData B => phi s q.1.val) p :=
    ContinuousAt.comp (f := fun q : FlightData B => q.1.val) (g := phi s)
      (phi_continuousAt s p.1.property) hu.continuousAt
  have hchart : ContinuousAt (fun q : FlightData B => chart (phi s q.1.val) q.2.1.val q.2.2.1.val) p :=
    ContinuousAt.comp
      (f := fun q : FlightData B => (phi s q.1.val, q.2.1.val, q.2.2.1.val))
      (g := fun q : Point × (Point × Mat2) => chart q.1 q.2.1 q.2.2)
      (chart_joint_continuousAt (phi_mem s p.1.property) p.2.1.property p.2.2.1.val)
      (hphi.prodMk (hv.continuousAt.prodMk hQ.continuousAt))
  have hm : ContinuousAt (fun q : FlightData B => returnModelFrame s q.1.val q.2.1.val q.2.2.1.val q.2.2.2) p :=
    (flow_continuous.continuousAt.comp (ha.continuousAt.mul ht)).mul hchart
  have hdet := returnModelFrame_det s p.1.property p.2.1.property p.2.2.1.property.1 (p.2.2.2 : ℝ)
  have hh := (frameHeight_continuousAt N _ (by rw [hdet]; norm_num)).comp hm
  exact ContinuousAt.comp (g := ENNReal.toReal)
    (f := fun q : FlightData B => frameHeight N
      (returnModelFrame s q.1.val q.2.1.val q.2.2.1.val q.2.2.2))
    (ENNReal.continuousAt_toReal (frameHeight_ne_top N
      (returnModelFrame s p.1.val p.2.1.val p.2.2.1.val p.2.2.2) (by rw [hdet]; norm_num))) hh

/-- Uniform continuity of every return flight on bounded determinant-one fibers. -/
theorem modelFlightHeight_uniform (N : PlaneNorm) (s : Symbol) (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p q : FlightData B, dist p q < ρ →
      |modelFlightHeight N s p - modelFlightHeight N s q| < ε := by
  have hu := CompactSpace.uniformContinuous_of_continuous (modelFlightHeight_continuous N s B)
  obtain ⟨ρ, hρ, hbound⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  exact ⟨ρ, hρ, fun p q hpq => by simpa only [Real.dist_eq] using hbound hpq⟩

/-- The coordinate model is exactly the coded flight, not an approximation. -/
theorem returnModelFrame_coded (z : Word) (Q : Mat2) (a : ℝ) :
    returnModelFrame (z 0) (futureCode (shift 1 z)) (pastCode z) Q a = flightChart a (z, Q) := by
  simp only [returnModelFrame, flightChart, roof, codedChart, ← futureCode_recurrence]

/-- A single tolerance controls all coded flights with bounded fibers, for either branch. -/
theorem coded_flight_height_uniform (N : PlaneNorm) (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z z' : Word, ∀ Q Q' : Mat2,
      Q.det = 1 → Q'.det = 1 → ‖Q‖ ≤ B → ‖Q'‖ ≤ B → z 0 = z' 0 →
      dist (futureCode (shift 1 z)) (futureCode (shift 1 z')) < ρ →
      dist (pastCode z) (pastCode z') < ρ → ‖Q - Q'‖ < ρ →
      ∀ a : FlightParameter,
        |(frameHeight N (flightChart a (z, Q))).toReal -
          (frameHeight N (flightChart a (z', Q'))).toReal| < ε := by
  classical
  choose ρ hρ hbound using fun s => modelFlightHeight_uniform N s B hε
  let R := min (ρ .a) (ρ .b)
  have hR : 0 < R := lt_min (hρ .a) (hρ .b)
  have hRs (s : Symbol) : R ≤ ρ s := by
    cases s with
    | a => exact min_le_left _ _
    | b => exact min_le_right _ _
  refine ⟨R, hR, ?_⟩
  intro z z' Q Q' hQ hQ' hB hB' hs hu hv hF a
  let p : FlightData B := (⟨futureCode (shift 1 z), futureCode_mem _⟩,
    (⟨pastCode z, pastCode_mem _⟩, (⟨Q, hQ, hB⟩, a)))
  let q : FlightData B := (⟨futureCode (shift 1 z'), futureCode_mem _⟩,
    (⟨pastCode z', pastCode_mem _⟩, (⟨Q', hQ', hB'⟩, a)))
  have hd : dist p q < ρ (z 0) := by
    simp only [p, q, Prod.dist_eq, Subtype.dist_eq, dist_self]
    exact max_lt (hu.trans_le (hRs _)) (max_lt (hv.trans_le (hRs _))
      (max_lt (by rw [dist_eq_norm]; exact hF.trans_le (hRs _)) (hρ _)))
  have hh := hbound (z 0) p q hd
  change |(frameHeight N (returnModelFrame (z 0) (futureCode (shift 1 z)) (pastCode z) Q a)).toReal -
    (frameHeight N (returnModelFrame (z 0) (futureCode (shift 1 z')) (pastCode z') Q' a)).toReal| < ε at hh
  have he : returnModelFrame (z 0) (futureCode (shift 1 z')) (pastCode z') Q' a = flightChart a (z', Q') := by
    rw [hs, returnModelFrame_coded]
  rw [returnModelFrame_coded, he] at hh
  exact hh

end HallRay

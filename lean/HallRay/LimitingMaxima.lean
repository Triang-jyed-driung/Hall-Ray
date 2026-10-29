module

public import HallRay.LimitingSkeleton

@[expose] public section
noncomputable section
open Filter Topology
open scoped ENNReal Matrix.Norms.L2Operator
namespace HallRay

abbrev TraceParameter := Set.Ioo (-2 : ℝ) 2
abbrev FiberParameter := {E : Mat2 // E.det = 1}
abbrev SkeletonPoint := limitingSkeleton
abbrev LimitingParameter := SkeletonPoint × (Real.Angle × FlightParameter)

instance : CompactSpace SkeletonPoint := isCompact_iff_compactSpace.mp limitingSkeleton_compact
instance : Nonempty SkeletonPoint := limitingSkeleton_nonempty.to_subtype
instance : Nonempty FlightParameter := ⟨⟨0, by norm_num⟩⟩

@[fun_prop] theorem traceReturn_continuous :
    Continuous (fun v : TraceParameter => ellipticTracePath v) :=
  ellipticTracePath_continuousOn.comp_continuous continuous_subtype_val
    (fun v => ⟨v.property.1.le, v.property.2.le⟩)

@[fun_prop] theorem traceCircle_continuous :
    Continuous (fun p : TraceParameter × Real.Angle => ellipticCircle (ellipticTracePath p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hf : Continuous (fun q : TraceParameter × Real.Angle =>
      (ellipticTracePath q.1, q.2)) :=
    (traceReturn_continuous.comp continuous_fst).prodMk continuous_snd
  exact ContinuousAt.comp
    (f := fun q : TraceParameter × Real.Angle => (ellipticTracePath q.1, q.2))
    (g := fun q : Mat2 × Real.Angle => ellipticCircle q.1 q.2)
    (ellipticCircle_joint_continuousAt (ellipticTracePath_det p.1)
      (ellipticTracePath_elliptic p.1.property) p.2) hf.continuousAt

/-- The limiting family uses a single compact parameter space, independent of the trace. -/
def limitingFrame (v : TraceParameter) (p : LimitingParameter) : Mat3 :=
  let z := p.1.val.1
  flow ((p.2.2 : ℝ) * roof z) * codedChart z
    (ellipticCircle (ellipticTracePath v) p.2.1 * p.1.val.2)

@[fun_prop] theorem limitingFrame_continuous :
    Continuous (fun p : TraceParameter × LimitingParameter => limitingFrame p.1 p.2) := by
  unfold limitingFrame
  have hz : Continuous (fun p : TraceParameter × LimitingParameter => p.2.1.val.1) := by fun_prop
  have hQ : Continuous (fun p : TraceParameter × LimitingParameter => p.2.1.val.2) := by fun_prop
  have ha : Continuous (fun p : TraceParameter × LimitingParameter => (p.2.2.2 : ℝ)) := by fun_prop
  have hc : Continuous (fun p : TraceParameter × LimitingParameter =>
      ellipticCircle (ellipticTracePath p.1) p.2.2.1) :=
    Continuous.comp
      (g := fun q : TraceParameter × Real.Angle => ellipticCircle (ellipticTracePath q.1) q.2)
      (f := fun p : TraceParameter × LimitingParameter => (p.1, p.2.2.1))
      traceCircle_continuous (show Continuous (fun p : TraceParameter × LimitingParameter => (p.1, p.2.2.1)) by fun_prop)
  exact (flow_continuous.comp (ha.mul (roof_continuous.comp hz))).mul
    (codedChart_continuous.comp (hz.prodMk (hc.mul hQ)))

theorem limitingFrame_det (v : TraceParameter) (p : LimitingParameter) :
    (limitingFrame v p).det = 1 := by
  unfold limitingFrame
  rw [Matrix.det_mul, flow_det, one_mul]
  apply codedChart_det
  rw [Matrix.det_mul, ellipticCircle_det (ellipticTracePath_det v)
    (ellipticTracePath_elliptic v.property), limitingSkeleton_det p.1.property, one_mul]

@[fun_prop] theorem blockFiber_continuous : Continuous blockFiber := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp [blockFiber] <;> fun_prop

def limitingHeightFamily (N : PlaneNorm) (d : FiberParameter × TraceParameter)
    (p : LimitingParameter) : ℝ≥0∞ := frameHeight N (blockFiber d.1.val * limitingFrame d.2 p)

theorem limitingHeightFamily_continuous (N : PlaneNorm) : Continuous ↿(limitingHeightFamily N) := by
  change Continuous (fun p : (FiberParameter × TraceParameter) × LimitingParameter =>
    frameHeight N (blockFiber p.1.1.val * limitingFrame p.1.2 p.2))
  have hm : Continuous (fun p : (FiberParameter × TraceParameter) × LimitingParameter =>
      blockFiber p.1.1.val * limitingFrame p.1.2 p.2) := by
    apply Continuous.mul
    · exact blockFiber_continuous.comp
        (show Continuous (fun p : (FiberParameter × TraceParameter) × LimitingParameter => p.1.1.val) by fun_prop)
    · exact Continuous.comp
        (g := fun q : TraceParameter × LimitingParameter => limitingFrame q.1 q.2)
        (f := fun p : (FiberParameter × TraceParameter) × LimitingParameter => (p.1.2, p.2))
        limitingFrame_continuous (show Continuous (fun p : (FiberParameter × TraceParameter) × LimitingParameter => (p.1.2, p.2)) by fun_prop)
  apply continuous_iff_continuousAt.mpr
  intro p
  have hdet : (blockFiber p.1.1.val * limitingFrame p.1.2 p.2).det = 1 := by
    rw [Matrix.det_mul, blockFiber_det, p.1.1.property, limitingFrame_det, one_mul]
  exact (frameHeight_continuousAt N _ (by rw [hdet]; norm_num)).comp hm.continuousAt

/-- The continuous maximum over the limiting family, including an arbitrary initial fiber. -/
def limitingDepth (N : PlaneNorm) (d : FiberParameter × TraceParameter) : ℝ≥0∞ :=
  sSup (Set.range (limitingHeightFamily N d))

theorem limitingDepth_continuous (N : PlaneNorm) : Continuous (limitingDepth N) := by
  unfold limitingDepth
  simpa only [Set.image_univ] using
    (isCompact_univ : IsCompact (Set.univ : Set LimitingParameter)).continuous_sSup
      (limitingHeightFamily_continuous N)

theorem limitingDepth_attained (N : PlaneNorm) (d : FiberParameter × TraceParameter) :
    ∃ p : LimitingParameter, limitingDepth N d = limitingHeightFamily N d p := by
  have hpair : Continuous (fun p : LimitingParameter => (d, p)) := continuous_const.prodMk continuous_id
  have hc : Continuous (limitingHeightFamily N d) :=
    Continuous.comp
      (g := fun q : (FiberParameter × TraceParameter) × LimitingParameter => limitingHeightFamily N q.1 q.2)
      (f := fun p : LimitingParameter => (d, p)) (limitingHeightFamily_continuous N) hpair
  obtain ⟨p, _, hp⟩ := (isCompact_univ : IsCompact (Set.univ : Set LimitingParameter)).exists_sSup_image_eq
    Set.univ_nonempty hc.continuousOn
  exact ⟨p, by simpa only [limitingDepth, Set.image_univ] using hp⟩

theorem limitingDepth_ne_top (N : PlaneNorm) (d : FiberParameter × TraceParameter) : limitingDepth N d ≠ ⊤ := by
  obtain ⟨p, hp⟩ := limitingDepth_attained N d
  rw [hp]
  apply frameHeight_ne_top
  rw [Matrix.det_mul, blockFiber_det, d.1.property, limitingFrame_det, one_mul]
  norm_num

end HallRay

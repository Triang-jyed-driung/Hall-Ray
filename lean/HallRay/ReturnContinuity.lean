module

public import HallRay.WordLimits

@[expose] public section
noncomputable section
open Filter Topology
namespace HallRay

@[fun_prop] theorem sign_coordinate_continuous : Continuous (fun z : Word => sign (z 0)) := by
  have hs : Continuous sign := continuous_of_discreteTopology
  exact hs.comp (continuous_apply 0)

@[fun_prop] theorem coded_d_continuous :
    Continuous (fun z : Word => d (z 0) (futureCode (shift 1 z))) := by
  have hf := futureCode_continuous.comp (shift_continuous 1)
  unfold d
  fun_prop

@[fun_prop] theorem coded_e_continuous :
    Continuous (fun z : Word => e (z 0) (pastCode z)) := by
  have hp := pastCode_continuous
  have hs := sign_coordinate_continuous
  unfold e
  fun_prop

@[fun_prop] theorem fiberMap_continuous : Continuous fiberMap := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hd : Real.sqrt (d (z 0) (futureCode (shift 1 z))) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (d_pos _ (futureCode_mem _)))
  have hf := futureCode_continuous.comp (shift_continuous 1)
  have hnorm := (Real.continuous_sqrt.comp coded_d_continuous).continuousAt.inv₀ hd
  have hs := sign_coordinate_continuous.continuousAt (x := z)
  unfold fiberMap fiber
  apply hnorm.smul
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [fiberNumerator] <;> fun_prop

@[fun_prop] theorem roof_continuous : Continuous roof := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hd : d (z 0) (futureCode (shift 1 z)) ≠ 0 := ne_of_gt (d_pos _ (futureCode_mem _))
  have he : e (z 0) (pastCode z) ≠ 0 := ne_of_gt (e_pos _ (pastCode_mem _))
  exact (coded_d_continuous.continuousAt.log hd).div_const 6 |>.add
    ((coded_e_continuous.continuousAt.log he).div_const 3)

@[fun_prop] theorem fiberProduct_continuous (r : ℕ) : Continuous (fun z => cocycle fiberMap z r) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
    exact ih.mul (fiberMap_continuous.comp (shift_continuous (r : ℤ)))

@[fun_prop] theorem timeSum_continuous (r : ℕ) : Continuous (fun z => timeSum z r) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
    simpa only [timeSum_succ, Function.comp_def, Pi.add_def] using
      ih.add (roof_continuous.comp (shift_continuous (r : ℤ)))

theorem beginning_fiber_limit (r : ℕ) :
    Tendsto (fun n => cocycle fiberMap (periodicWord n) r) atTop
      (𝓝 (cocycle fiberMap (shift 1 defectWord) r)) :=
  (fiberProduct_continuous r).continuousAt.tendsto.comp periodicWord_beginning_limit

theorem end_suffix_limit (r : ℕ) :
    Tendsto (fun n : ℕ => cocycle fiberMap (shift ((n : ℤ) - r) (periodicWord n)) (r + 1))
      atTop (𝓝 (cocycle fiberMap (shift (-(r : ℤ)) defectWord) (r + 1))) :=
  (fiberProduct_continuous (r + 1)).continuousAt.tendsto.comp (periodicWord_end_limit r)

@[fun_prop] theorem flow_continuous : Continuous flow := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> dsimp [flow] <;> fun_prop

/-- Joint continuity of the marked frame in its code and fiber coordinates. -/
@[fun_prop] theorem codedChart_continuous :
    Continuous (fun p : Word × Mat2 => codedChart p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hu : Continuous (fun q : Word × Mat2 => futureCode q.1) :=
    futureCode_continuous.comp continuous_fst
  have hv : Continuous (fun q : Word × Mat2 => pastCode q.1) :=
    pastCode_continuous.comp continuous_fst
  have hdot : Continuous (fun q : Word × Mat2 =>
      1 + dot (pastCode q.1) (futureCode q.1)) := by
    unfold dot
    fun_prop
  have hp : 1 + dot (pastCode p.1) (futureCode p.1) ≠ 0 := by
    have h := chart_positive (futureCode_mem p.1) (pastCode_mem p.1)
    linarith
  have hscale : ContinuousAt (fun q : Word × Mat2 =>
      chartScale (futureCode q.1) (pastCode q.1)) p := by
    exact Real.continuous_exp.continuousAt.comp
      ((hdot.continuousAt.log hp).neg.div_const 3)
  have hua := hu.continuousAt (x := p)
  have hva := hv.continuousAt (x := p)
  unfold codedChart chart
  apply hscale.smul
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
    fin_cases i <;> fin_cases j <;> simp only [rawChart] <;> fun_prop

@[fun_prop] theorem codedChart_fixed_continuous (z : Word) : Continuous (codedChart z) := by
  have hp : Continuous (fun E : Mat2 => (z, E)) := continuous_const.prodMk continuous_id
  exact Continuous.comp (f := fun E : Mat2 => (z, E))
    (g := fun p : Word × Mat2 => codedChart p.1 p.2) codedChart_continuous hp

end HallRay

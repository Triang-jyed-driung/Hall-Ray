module

public import HallRay.BlockFiberEstimates

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

theorem coordinate_decay_le (n : ℕ) : (2 / 5 : ℝ) * (1 / 900 : ℝ) ^ n ≤ (1 / 600 : ℝ) ^ n := by
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 900) (by norm_num : (1 / 900 : ℝ) ≤ 1 / 600) n
  have hn := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 900) n
  linarith

/-- Symbolic coordinates throughout the next block shadow its periodic model. -/
theorem block_code_shadowing {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i j : ℕ)
    (hj : j < (concatenationStages P hρ (i + 1)).repetitions * ((concatenationStages P hρ (i + 1)).n + 1)) :
    let w := shift (((concatenationStages P hρ (i + 1)).start + j : ℕ) : ℤ) (concatenationWord P hρ)
    let w' := shift (j : ℤ) (periodicWord (concatenationStages P hρ (i + 1)).n)
    w 0 = w' 0 ∧
      dist (futureCode (shift 1 w)) (futureCode (shift 1 w')) ≤ (1 / 600 : ℝ) ^ (concatenationStages P hρ i).n ∧
      dist (pastCode w) (pastCode w') ≤ (1 / 600 : ℝ) ^ (concatenationStages P hρ i).n := by
  let S := concatenationStages P hρ i
  let T := concatenationStages P hρ (i + 1)
  have hn : S.n < T.n := (concatenationStages_extends P hρ i).2.1
  have hpow : (1 / 600 : ℝ) ^ T.n ≤ (1 / 600 : ℝ) ^ S.n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn.le
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.cast_zero] using concatenation_block_future P hρ (i + 1) j 0 (by omega)
  · rw [dist_eq_supDist]
    apply (futureCode_closeness T.n ?_).trans ((coordinate_decay_le T.n).trans hpow)
    intro m hm
    have hh := concatenation_block_future P hρ (i + 1) j (m + 1) (by
      change (m + 1) + j < T.repetitions * (T.n + 1) + T.n
      change j < T.repetitions * (T.n + 1) at hj
      omega)
    simpa only [shift, Nat.cast_add, Nat.cast_one] using hh
  · rw [dist_eq_supDist]
    exact (pastCode_closeness S.n (fun d hd hdn => concatenation_block_past P hρ i j d hj hd hdn)).trans
      (coordinate_decay_le S.n)

/-- A positive, at-most-one tolerance for stage i's real flight heights. -/
def shadowTolerance (N : PlaneNorm) (B : ℝ) (i : ℕ) : ℝ :=
  min 1 (Classical.choose (coded_flight_height_uniform N B (stageError_pos i)))

theorem shadowTolerance_pos (N : PlaneNorm) (B : ℝ) (i : ℕ) : 0 < shadowTolerance N B i :=
  lt_min (by norm_num) (Classical.choose_spec (coded_flight_height_uniform N B (stageError_pos i))).1

theorem shadowTolerance_le_one (N : PlaneNorm) (B : ℝ) (i : ℕ) : shadowTolerance N B i ≤ 1 := min_le_left _ _

/-- Uniform whole-flight comparison for every return in every block after the first. -/
theorem block_flight_shadowing {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i)
    (hcontrol : ∀ i, ρ i ≤ shadowTolerance N (2 * P.bound + 1) i) (i j : ℕ)
    (hj : j < (concatenationStages P hρ (i + 1)).repetitions * ((concatenationStages P hρ (i + 1)).n + 1))
    (a : FlightParameter) :
    |(frameHeight N (returnFlightFrame (concatenationWord P hρ) 1
      ((concatenationStages P hρ (i + 1)).start + j) a)).toReal -
      (frameHeight N (returnFlightFrame (periodicWord (concatenationStages P hρ (i + 1)).n)
        (concatenationStages P hρ (i + 1)).input.val j a)).toReal| < stageError (i + 1) := by
  let S := concatenationStages P hρ i
  let T := concatenationStages P hρ (i + 1)
  let z := concatenationWord P hρ
  let w := shift ((T.start + j : ℕ) : ℤ) z
  let w' := shift (j : ℤ) (periodicWord T.n)
  let Q := cocycle fiberMap z (T.start + j)
  let Q' := T.input.val * cocycle fiberMap (periodicWord T.n) j
  let q := (1 / 600 : ℝ) ^ S.n
  let D := 6 * P.bound + 3
  have hK := P.bound_ge_one
  have hq0 : 0 ≤ q := by positivity
  have hD : 0 < D := by dsimp [D]; linarith
  have hsmall : D * q < ρ (i + 1) := by
    have hb : q < ρ (i + 1) / D := S.overlap_small.trans_le (min_le_right _ _)
    have hh := (lt_div_iff₀ hD).mp hb
    linarith
  have hρ1 : ρ (i + 1) ≤ 1 := (hcontrol _).trans (shadowTolerance_le_one _ _ _)
  have hcode := block_code_shadowing P hρ i j hj
  have hf : ‖Q - Q'‖ ≤ 6 * P.bound * q := cumulative_block_fiber_error P hρ i j hj.le
  have hinput : T.input.val = S.fiber := (concatenationStages_extends P hρ i).2.2.2
  have hQ' : ‖Q'‖ ≤ 2 * P.bound := by
    exact (norm_mul_le _ _).trans (mul_le_mul (by rw [hinput]; exact S.fiber_norm_lt_two.le)
      (T.partial_bound j).1 (norm_nonneg _) (by norm_num))
  have hQ : ‖Q‖ ≤ 2 * P.bound + 1 := by
    have htri : ‖Q‖ ≤ ‖Q - Q'‖ + ‖Q'‖ := by
      simpa only [sub_add_cancel] using norm_add_le (Q - Q') Q'
    dsimp [D] at hsmall
    nlinarith
  have hnear : ‖Q - Q'‖ < ρ (i + 1) := by dsimp [D] at hsmall; nlinarith
  have hcoord : q < ρ (i + 1) := by dsimp [D] at hsmall; nlinarith
  have hchosen := (Classical.choose_spec
    (coded_flight_height_uniform N (2 * P.bound + 1) (stageError_pos (i + 1)))).2
  have htolerance : ρ (i + 1) ≤ Classical.choose
      (coded_flight_height_uniform N (2 * P.bound + 1) (stageError_pos (i + 1))) :=
    (hcontrol _).trans (min_le_right _ _)
  have hQdet : Q.det = 1 := fiberProduct_det _ _
  have hQ'det : Q'.det = 1 := by rw [Matrix.det_mul, T.input.property, fiberProduct_det, one_mul]
  have hh := hchosen w w' Q Q' hQdet hQ'det hQ (hQ'.trans (by linarith)) hcode.1
    ((hcode.2.1.trans_lt hcoord).trans_le htolerance)
    ((hcode.2.2.trans_lt hcoord).trans_le htolerance) (hnear.trans_le htolerance) a
  simpa only [returnFlightFrame, one_mul, w, w', Q, Q'] using hh

end HallRay

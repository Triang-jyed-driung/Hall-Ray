module

public import HallRay.BlockAgreement

@[expose] public section
noncomputable section
open Filter Topology
open scoped Matrix.Norms.L2Operator
namespace HallRay

/-- The final word's accumulated fiber is close to the finite-stage terminal fiber. -/
theorem final_prefix_fiber_error {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i : ℕ) :
    ‖cocycle fiberMap (concatenationWord P hρ) (concatenationStages P hρ i).finish -
      (concatenationStages P hρ i).fiber‖ ≤ 2 * (1 / 600 : ℝ) ^ (concatenationStages P hρ i).n := by
  let S := concatenationStages P hρ i
  have ha : ∀ m : ℕ, m < S.finish + S.n → S.word (m : ℤ) = concatenationWord P hρ (m : ℤ) := by
    intro m hm
    exact (concatenationWord_agreement P hρ i (by exact_mod_cast hm)).symm
  have he := fiber_product_error S.finish S.n ha
  have hb := (absolute_error_le _ _ S.fiber_det).trans (mul_le_mul_of_nonneg_left he (norm_nonneg S.fiber))
  exact hb.trans (mul_le_mul_of_nonneg_right S.fiber_norm_lt_two.le (by positivity))

/-- The in-block product follows its periodic model uniformly over the whole block. -/
theorem block_partial_fiber_error {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i j : ℕ)
    (hj : j ≤ (concatenationStages P hρ i).repetitions * ((concatenationStages P hρ i).n + 1)) :
    ‖cocycle fiberMap (shift ((concatenationStages P hρ i).start : ℤ) (concatenationWord P hρ)) j -
      cocycle fiberMap (periodicWord (concatenationStages P hρ i).n) j‖ ≤
        P.bound * (1 / 600 : ℝ) ^ (concatenationStages P hρ i).n := by
  let S := concatenationStages P hρ i
  change j ≤ S.repetitions * (S.n + 1) at hj
  have ha : ∀ m : ℕ, m < j + S.n → periodicWord S.n (m : ℤ) =
      shift (S.start : ℤ) (concatenationWord P hρ) (m : ℤ) := by
    intro m hm
    simpa only [Nat.add_zero, Nat.cast_zero, shift_zero] using
      (concatenation_block_future P hρ i 0 m (by
        change m + 0 < S.repetitions * (S.n + 1) + S.n
        omega)).symm
  have he := fiber_product_error j S.n ha
  exact ((absolute_error_le _ _ (fiberProduct_det _ _)).trans
    (mul_le_mul_of_nonneg_left he (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_right (S.partial_bound j).1 (by positivity))

theorem block_partial_fiber_norm {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i j : ℕ)
    (hj : j ≤ (concatenationStages P hρ i).repetitions * ((concatenationStages P hρ i).n + 1)) :
    ‖cocycle fiberMap (shift ((concatenationStages P hρ i).start : ℤ) (concatenationWord P hρ)) j‖ ≤
      2 * P.bound := by
  let S := concatenationStages P hρ i
  have he := block_partial_fiber_error P hρ i j hj
  have hp : (1 / 600 : ℝ) ^ S.n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have htri := norm_sub_le
    (cocycle fiberMap (shift (S.start : ℤ) (concatenationWord P hρ)) j - cocycle fiberMap (periodicWord S.n) j)
    (-cocycle fiberMap (periodicWord S.n) j)
  simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at htri
  have hb := (S.partial_bound j).1
  have hK := P.bound_ge_one
  have hprod := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ P.bound)
  nlinarith

/-- The cumulative fiber comparison includes both the inherited prefix error and the new block error. -/
theorem cumulative_block_fiber_error {N : PlaneNorm} {A : ℝ} (P : ConcatenationParameters N A)
    {ρ : ℕ → ℝ} (hρ : ∀ i, 0 < ρ i) (i j : ℕ)
    (hj : j ≤ (concatenationStages P hρ (i + 1)).repetitions * ((concatenationStages P hρ (i + 1)).n + 1)) :
    ‖cocycle fiberMap (concatenationWord P hρ) ((concatenationStages P hρ (i + 1)).start + j) -
      (concatenationStages P hρ (i + 1)).input.val *
        cocycle fiberMap (periodicWord (concatenationStages P hρ (i + 1)).n) j‖ ≤
      6 * P.bound * (1 / 600 : ℝ) ^ (concatenationStages P hρ i).n := by
  let S := concatenationStages P hρ i
  let T := concatenationStages P hρ (i + 1)
  let U := cocycle fiberMap (concatenationWord P hρ) S.finish
  let V := cocycle fiberMap (shift (T.start : ℤ) (concatenationWord P hρ)) j
  let W := cocycle fiberMap (periodicWord T.n) j
  have he := concatenationStages_extends P hρ i
  have hU : ‖U - S.fiber‖ ≤ 2 * (1 / 600 : ℝ) ^ S.n := final_prefix_fiber_error P hρ i
  have hV : ‖V - W‖ ≤ P.bound * (1 / 600 : ℝ) ^ T.n := block_partial_fiber_error P hρ (i + 1) j hj
  have hnV : ‖V‖ ≤ 2 * P.bound := block_partial_fiber_norm P hρ (i + 1) j hj
  have hF := S.fiber_norm_lt_two.le
  have hp : (1 / 600 : ℝ) ^ T.n ≤ (1 / 600 : ℝ) ^ S.n := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) he.2.1.le
  have hstart : T.start = S.finish := he.1
  have hinput : T.input.val = S.fiber := he.2.2.2
  have hproduct : cocycle fiberMap (concatenationWord P hρ) (T.start + j) = U * V := by
    rw [cocycle_add]
    exact congrArg (fun F : Mat2 => F * V) (congrArg (cocycle fiberMap (concatenationWord P hρ)) hstart)
  change ‖cocycle fiberMap (concatenationWord P hρ) (T.start + j) - T.input.val * W‖ ≤ _
  rw [hproduct, hinput]
  have hd : U * V - S.fiber * W = (U - S.fiber) * V + S.fiber * (V - W) := by noncomm_ring
  rw [hd]
  have h1 : ‖(U - S.fiber) * V‖ ≤ (2 * (1 / 600 : ℝ) ^ S.n) * (2 * P.bound) :=
    (norm_mul_le (U - S.fiber) V).trans
    (mul_le_mul hU hnV (norm_nonneg _) (by positivity))
  have h2 : ‖S.fiber * (V - W)‖ ≤ 2 * (P.bound * (1 / 600 : ℝ) ^ T.n) :=
    (norm_mul_le S.fiber (V - W)).trans
    (mul_le_mul hF hV (norm_nonneg _) (by norm_num))
  have hK := P.bound_ge_one
  have hm := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ P.bound)
  exact (norm_add_le _ _).trans (by nlinarith)

end HallRay

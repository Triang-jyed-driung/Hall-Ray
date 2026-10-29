From Stdlib Require Import Reals Psatz Lia.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices
  FiberProducts EuclideanNorm MatrixLimits ConcreteCocycle SymbolicCoding SymbolicCocycle
  DefectLimit PeriodicReturns EllipticConjugacy EllipticPowers EllipticContinuity
  TwoSidedCoding LatticeReturns LimitingWords LimitingFibers LimitingRepresentatives
  PaperTarget LatticeSystole SystoleCurves ChartCompactness RoofLimits CompactMatrices.
Open Scope R_scope.

(* The three explicit families from Section 5. Taking their height supremum
   also accounts for their closure, once that closure is identified below. *)
Inductive limiting_representative (X A : mat2) : mat3 -> Prop :=
| limiting_beginning : forall E j t,
    in_elliptic_circle A E -> 0 <= t <= orbit_roof_time (beginning_word j) ->
    limiting_representative X A (beginning_representative (mul2 X E) j t)
| limiting_ending : forall E r t,
    in_elliptic_circle A E -> 0 <= t <= orbit_roof_time (ending_word r) ->
    limiting_representative X A (ending_representative (mul2 X E) r t)
| limiting_bulk : forall E R t,
    in_elliptic_circle A E -> det2 R = 1 -> orthogonal2 R ->
    0 <= t <= orbit_roof_time constant_word ->
    limiting_representative X A (bulk_representative (mul2 X E) R t).

Definition limiting_height_values nm X A y := exists L,
  limiting_representative X A L /\ y = cusp_height nm L.

Theorem limiting_representatives_unimodular : forall X A L,
  det2 X = 1 -> det2 A = 1 -> Rabs (trace2 A) < 2 ->
  limiting_representative X A L -> det3 L = 1.
Proof.
  intros X A L HX HA Hell HL. destruct HL as [E j t HE Ht|E r t HE Ht|E R t HE HR Ho Ht].
  - apply beginning_representative_unimodular. rewrite det2_mul, HX,
      (elliptic_circle_unimodular A E HA Hell HE); ring.
  - apply ending_representative_unimodular. rewrite det2_mul, HX,
      (elliptic_circle_unimodular A E HA Hell HE); ring.
  - apply bulk_representative_unimodular; [|exact HR].
    rewrite det2_mul, HX, (elliptic_circle_unimodular A E HA Hell HE); ring.
Qed.

Lemma model_fiber_bound_nonnegative : 0 <= defect_product_bound.
Proof.
  unfold defect_product_bound; pose proof constant_power_bound_nonnegative.
  pose proof (opnorm_nonnegative defect_limit); nra.
Qed.

Lemma three_factor_norm_bound : forall X E F M K,
  0 <= M -> 0 <= K -> opnorm E <= M -> opnorm F <= K ->
  opnorm (mul2 (mul2 X E) F) <= (opnorm X+1)*(M+1)*(K+1).
Proof.
  intros X E F M K HM HK HE HF.
  pose proof (opnorm_submultiplicative X E) as H1.
  pose proof (opnorm_submultiplicative (mul2 X E) F) as H2.
  assert (Hinner : opnorm (mul2 X E) <= (opnorm X+1)*(M+1)).
  { assert (opnorm X*opnorm E <= opnorm X*M) by
      (apply Rmult_le_compat_l; [apply opnorm_nonnegative|exact HE]).
    pose proof (opnorm_nonnegative X); nra. }
  eapply Rle_trans; [exact H2|]. apply Rmult_le_compat;
    [apply opnorm_nonnegative|apply opnorm_nonnegative|exact Hinner|lra].
Qed.

Lemma conjugated_rotation_norm_bound : forall R,
  orthogonal2 R -> opnorm (mul2 (mul2 constant_basis R) (adj2 constant_basis)) <= constant_power_bound.
Proof.
  intros R HR. unfold constant_power_bound.
  pose proof (opnorm_submultiplicative constant_basis R) as H1.
  rewrite (orthogonal_opnorm R HR) in H1.
  eapply Rle_trans; [apply opnorm_submultiplicative|].
  apply Rmult_le_compat_r; [apply opnorm_nonnegative|lra].
Qed.

Lemma return_segment_time_bound : forall z t,
  0 <= t <= orbit_roof_time z -> Rabs t <= Rabs (ln 11)+1.
Proof.
  intros z t Ht.
  assert (Hr : orbit_roof_time z < ln 11).
  { unfold orbit_roof_time; apply ln_increasing; pose proof (orbit_roof_scale_bounds z); lra. }
  rewrite Rabs_right by lra. pose proof (Rle_abs (ln 11)); lra.
Qed.

Theorem limiting_height_values_bounded : forall nm X A,
  det2 X = 1 -> det2 A = 1 -> Rabs (trace2 A) < 2 ->
  bound (limiting_height_values nm X A).
Proof.
  intros nm X A HX HA Hell.
  destruct (elliptic_circles_uniformly_bounded (fun _ => A) A (matrix_cv_constant A) HA Hell)
    as [M [HM Hcircle]].
  set (K := constant_power_bound+2*defect_product_bound+1).
  assert (HK : 0 <= K) by
    (unfold K; pose proof constant_power_bound_nonnegative; pose proof model_fiber_bound_nonnegative; lra).
  set (Bfiber := (opnorm X+1)*(M+1)*(K+1)).
  destruct (bounded_chart_heights nm Bfiber (Rabs (ln 11)+1)) as [B HB].
  exists B. intros y [L [HL Hy]]. subst y.
  destruct HL as [E j t HE Ht|E r t HE Ht|E R t HE HR Ho Ht].
  - unfold beginning_representative. apply HB.
    + apply u_code_inside.
    + apply v_code_inside.
    + rewrite !det2_mul, HX, (elliptic_circle_unimodular A E HA Hell HE), matrix_power_unimodular;
        [ring|apply cocycle_unimodular].
    + apply three_factor_norm_bound; try lra.
      * exact (Hcircle 0%nat E HE).
      * eapply Rle_trans; [apply constant_powers_uniformly_bounded|].
        unfold K; pose proof model_fiber_bound_nonnegative; lra.
    + exact (return_segment_time_bound (beginning_word j) t Ht).
  - unfold ending_representative. apply HB.
    + apply u_code_inside.
    + apply v_code_inside.
    + rewrite !det2_mul, HX, (elliptic_circle_unimodular A E HA Hell HE), adjugate_determinant.
      unfold defect_product; rewrite factor_product_unimodular; ring.
    + apply three_factor_norm_bound; try lra.
      * exact (Hcircle 0%nat E HE).
      * pose proof (opnorm_adjugate_bound (defect_product r)); pose proof (defect_products_bounded r).
        unfold K; pose proof constant_power_bound_nonnegative; lra.
    + exact (return_segment_time_bound (ending_word r) t Ht).
  - unfold bulk_representative. apply HB.
    + apply u_code_inside.
    + apply v_code_inside.
    + rewrite !det2_mul, HX, (elliptic_circle_unimodular A E HA Hell HE), HR,
        adjugate_determinant, constant_basis_unimodular; ring.
    + apply three_factor_norm_bound; try lra.
      * exact (Hcircle 0%nat E HE).
      * eapply Rle_trans; [apply conjugated_rotation_norm_bound; exact Ho|].
        unfold K; pose proof model_fiber_bound_nonnegative; lra.
    + exact (return_segment_time_bound constant_word t Ht).
Qed.

Theorem limiting_height_values_nonempty : forall nm X A,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> exists y, limiting_height_values nm X A y.
Proof.
  intros nm X A HA Hell.
  exists (cusp_height nm (beginning_representative (mul2 X id2) 0 0)).
  exists (beginning_representative (mul2 X id2) 0 0); split; [|reflexivity].
  apply limiting_beginning; [apply elliptic_circle_identity; assumption|].
  pose proof (orbit_roof_time_gt_one (beginning_word 0)); lra.
Qed.

Definition limiting_peak nm X A (HX : det2 X = 1) (HA : det2 A = 1)
  (Hell : Rabs (trace2 A) < 2) :=
  proj1_sig (completeness (limiting_height_values nm X A)
    (limiting_height_values_bounded nm X A HX HA Hell)
    (limiting_height_values_nonempty nm X A HA Hell)).

Theorem limiting_peak_lub : forall nm X A HX HA Hell,
  is_lub (limiting_height_values nm X A) (limiting_peak nm X A HX HA Hell).
Proof. intros; apply (proj2_sig (completeness _ _ _)). Qed.

Theorem limiting_peak_upper : forall nm X A HX HA Hell L,
  limiting_representative X A L -> cusp_height nm L <= limiting_peak nm X A HX HA Hell.
Proof.
  intros nm X A HX HA Hell L HL. destruct (limiting_peak_lub nm X A HX HA Hell) as [Hb _].
  apply Hb; exists L; auto.
Qed.

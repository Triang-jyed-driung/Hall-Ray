From Stdlib Require Import Reals Psatz Lia FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices LatticeBasis
  PaperTarget ScalarEstimates NormGeometry DaniCorrespondence LatticeSystole DaniSystole
  SystoleContinuity SystoleCurves NormalizedFlow LatticeReturns TwoSidedCoding
  Concatenation StableForgetting.
Open Scope R_scope.

Definition has_cubic_lower_limit (f : R -> R) rho : Prop :=
  (forall eps, 0 < eps < rho -> exists T, forall t, T <= t -> (rho-eps)^2 <= (f t)^3) /\
  (forall eps, 0 < eps -> forall T, exists t, T <= t /\ (f t)^3 <= (rho+eps)^2).

Lemma inverse_cube_continuous : forall H,
  0 < H -> continuity_pt (fun u : R => (/u)^3) H.
Proof. intros H HH; reg; lra. Qed.

Theorem reciprocal_limsup_cubic_lower_limit : forall f H rho,
  (forall t, 0 < f t) -> 0 < H -> 0 < rho -> (/H)^3 = rho^2 ->
  has_limsup f H -> has_cubic_lower_limit (fun t => /f t) rho.
Proof.
  intros f H rho Hpos HH Hr Hpower [Hupper Hpeaks]. split.
  - intros eps He.
    set (margin := rho^2-(rho-eps)^2).
    assert (Hm : 0 < margin) by (unfold margin; nra).
    destruct (scalar_continuity_estimate (fun u : R => (/u)^3) H (margin/2)
      (inverse_cube_continuous H HH) ltac:(lra)) as [d [Hd Hcont]].
    set (e := Rmin (H/2) (d/2)).
    assert (He0 : 0 < e) by (apply Rmin_pos; lra).
    assert (Hed : e < d) by (unfold e; pose proof (Rmin_r (H/2) (d/2)); lra).
    pose proof (Hcont (H+e) ltac:(replace (H+e-H) with e by ring; rewrite Rabs_right; lra)) as Hnear.
    destruct (Hupper e He0) as [T HT]. exists T. intros t Ht.
    specialize (HT t Ht).
    assert (Hinv : /(H+e) <= /f t).
    { apply Rinv_le_contravar; [apply Hpos|lra]. }
    pose proof (pow_incr (/(H+e)) (/f t) 3
      ltac:(split; [apply Rlt_le, Rinv_0_lt_compat; lra|exact Hinv])) as Hcube.
    rewrite Hpower in Hnear.
    apply absolute_difference_sandwich in Hnear. unfold margin in *; lra.
  - intros eps He T.
    set (margin := (rho+eps)^2-rho^2).
    assert (Hm : 0 < margin) by (unfold margin; nra).
    destruct (scalar_continuity_estimate (fun u : R => (/u)^3) H (margin/2)
      (inverse_cube_continuous H HH) ltac:(lra)) as [d [Hd Hcont]].
    set (e := Rmin (H/2) (d/2)).
    assert (He0 : 0 < e) by (apply Rmin_pos; lra).
    assert (HeH : e <= H/2) by apply Rmin_l.
    assert (Hed : e < d) by (unfold e; pose proof (Rmin_r (H/2) (d/2)); lra).
    pose proof (Hcont (H-e) ltac:(replace (H-e-H) with (-e) by ring;
      rewrite Rabs_Ropp, Rabs_right; lra)) as Hnear.
    destruct (Hpeaks e T He0) as [t [Ht Hft]]. exists t; split; [exact Ht|].
    assert (Hinv : /f t <= /(H-e)).
    { apply Rinv_le_contravar; lra. }
    pose proof (pow_incr (/f t) (/(H-e)) 3
      ltac:(split; [apply Rlt_le, Rinv_0_lt_compat, Hpos|exact Hinv])) as Hcube.
    rewrite Hpower in Hnear.
    apply absolute_difference_sandwich in Hnear. unfold margin in *; lra.
Qed.

Lemma hx_flow_determinant : forall x t,
  det3 (mul3 (diagonal_flow t) (hx (fst x) (snd x))) = 1.
Proof.
  intros x t. rewrite mul3_determinant, diagonal_flow_unimodular, hx_determinant; ring.
Qed.

Lemma rational_systole_upper : forall nm x,
  rational_vector x -> exists q, (0 < q)%nat /\ forall r,
    0 < r -> approximation_systole nm x r <= INR q/(r*r).
Proof.
  intros nm x [q [p1 [p2 [Hq [Hx Hy]]]]]. exists q; split; [exact Hq|].
  assert (Hqr : 0 < INR q) by (apply lt_0_INR; exact Hq).
  assert (Herr : length2 nm (approximation_vector x q p1 p2) = 0).
  { replace (approximation_vector x q p1 p2) with vzero by
      (unfold approximation_vector, vzero; rewrite Hx, Hy; f_equal; field; lra).
    apply length2_zero. }
  intros r Hr.
  pose proof (systole_lower_bound nm (mul3 (flow_scale r) (hx (fst x) (snd x)))
    (approximation_lattice_vector x q p1 p2)
    ltac:(rewrite approximation_lattice_vector_independent;
      apply approximation_index_nonzero_iff; unfold approximation_index_nonzero; left; lia)) as Hb.
  rewrite dani_vector_identity in Hb by exact Hr. rewrite Herr in Hb.
  unfold vector_length in Hb. rewrite Rmult_0_r, Rmax_left in Hb.
  - exact Hb.
  - apply Rlt_le. unfold Rdiv. apply Rmult_lt_0_compat; [exact Hqr|].
    apply Rinv_0_lt_compat; nra.
Qed.

Theorem finite_height_limsup_irrational : forall nm x H,
  0 < H -> has_limsup (lattice_height_orbit nm (hx (fst x) (snd x))) H ->
  ~ rational_vector x.
Proof.
  intros nm x H HH [Hupper Hpeaks] Hrat.
  destruct (rational_systole_upper nm x Hrat) as [q [Hq Hb]].
  assert (Hqr : 0 < INR q) by (apply lt_0_INR; exact Hq).
  destruct (Hupper 1 ltac:(lra)) as [T HT].
  set (r := Rmax (exp T) (INR q*(H+1)+1)).
  assert (Hrt : exp T <= r) by apply Rmax_l.
  assert (Hrb : INR q*(H+1)+1 <= r) by apply Rmax_r.
  assert (Hr : 0 < r) by (pose proof (exp_pos T); lra).
  specialize (HT (ln r) (logarithmic_scale_bound r T Hr Hrt)).
  unfold lattice_height_orbit, cusp_height, diagonal_flow in HT.
  rewrite exp_ln in HT by exact Hr.
  specialize (Hb r Hr).
  set (s := approximation_systole nm x r) in *.
  change (/s < H+1) in HT.
  assert (Hs : 0 < s).
  { unfold s, approximation_systole. apply systole_positive.
    rewrite mul3_determinant, flow_scale_determinant by lra.
    rewrite hx_determinant; ring. }
  apply (Rmult_lt_compat_r s) in HT; [|exact Hs].
  replace (/s*s) with 1 in HT by (field; lra).
  assert (Hprod : (H+1)*s <= (H+1)*(INR q/(r*r))) by nra.
  apply (Rmult_le_compat_r (r*r)) in Hprod; [|nra].
  replace ((H+1)*(INR q/(r*r))*(r*r)) with ((H+1)*INR q) in Hprod by (field; lra).
  assert (Hrr : (H+1)*INR q < r*r) by nra. nra.
Qed.

Theorem height_limsup_implies_approximation : forall nm x H rho,
  0 < H -> 0 < rho -> (/H)^3 = rho^2 ->
  has_limsup (lattice_height_orbit nm (hx (fst x) (snd x))) H ->
  ~ rational_vector x /\ has_approximation_constant nm x rho.
Proof.
  intros nm x H rho HH Hr Hpower Hlim.
  pose proof (finite_height_limsup_irrational nm x H HH Hlim) as Hirr.
  split; [exact Hirr|]. apply (proj2 (dani_correspondence nm x rho Hirr Hr)).
  pose proof (reciprocal_limsup_cubic_lower_limit _ H rho
    ltac:(intro t; unfold lattice_height_orbit, cusp_height;
      apply Rinv_0_lt_compat, systole_positive, hx_flow_determinant)
    HH Hr Hpower Hlim) as Hbounds.
  assert (Hsame : (fun t => /lattice_height_orbit nm (hx (fst x) (snd x)) t) = flow_systole nm x).
  { apply functional_extensionality; intro t.
    unfold lattice_height_orbit, cusp_height, flow_systole, approximation_systole, diagonal_flow.
    rewrite Rinv_inv; reflexivity. }
  change (has_cubic_lower_limit
    (fun t => /lattice_height_orbit nm (hx (fst x) (snd x)) t) rho) in Hbounds.
  rewrite Hsame in Hbounds. exact Hbounds.
Qed.

Definition height_for_constant rho := /positive_cube_root (rho^2).

Theorem symbolic_height_realizes_constant : forall nm z rho,
  0 < rho ->
  has_limsup (lattice_height_orbit nm (orbit_frame z id2)) (height_for_constant rho) ->
  ~ rational_vector (u_code z) /\ has_approximation_constant nm (u_code z) rho.
Proof.
  intros nm z rho Hr Hlim.
  pose proof (forgetting_symbolic_past nm z (height_for_constant rho) Hlim) as Hhx.
  apply (height_limsup_implies_approximation nm (u_code z) (height_for_constant rho) rho).
  - unfold height_for_constant; apply Rinv_0_lt_compat, positive_cube_root_positive.
  - exact Hr.
  - unfold height_for_constant. rewrite Rinv_inv, positive_cube_root_cube; nra.
  - exact Hhx.
Qed.

Lemma height_for_constant_cube : forall rho,
  0 < rho -> (height_for_constant rho)^3*rho^2 = 1.
Proof.
  intros rho Hr. unfold height_for_constant.
  rewrite <- (positive_cube_root_cube (rho^2) ltac:(nra)) at 2.
  field. pose proof (positive_cube_root_positive (rho^2)); lra.
Qed.

Lemma small_constants_give_large_heights : forall T,
  exists rho0, 0 < rho0 /\ forall rho,
    0 < rho < rho0 -> T < height_for_constant rho.
Proof.
  intro T. set (S := Rabs T+1).
  assert (HS : 1 <= S) by (unfold S; pose proof (Rabs_pos T); lra).
  assert (HT : T < S) by (unfold S; pose proof (Rle_abs T); lra).
  assert (HS3 : 0 <= S^3) by (apply pow_le; lra).
  exists (/(S^3+1)); split; [apply Rinv_0_lt_compat; lra|].
  intros rho Hr.
  assert (Hmult : rho*(S^3+1) < 1).
  { pose proof (proj2 Hr) as Hupper.
    apply (Rmult_lt_compat_r (S^3+1)) in Hupper; [|lra].
    replace (/(S^3+1)*(S^3+1)) with 1 in Hupper by (field; lra). exact Hupper. }
  assert (Hr1 : rho < 1) by nra.
  pose proof (height_for_constant_cube rho ltac:(lra)) as Hcube.
  assert (Hheight : 0 < height_for_constant rho) by
    (unfold height_for_constant; apply Rinv_0_lt_compat, positive_cube_root_positive).
  destruct (Rlt_dec S (height_for_constant rho)) as [Hyes|Hno]; [lra|].
  pose proof (pow_incr (height_for_constant rho) S 3 ltac:(lra)) as Hp.
  assert (Hsq : rho^2 <= rho) by nra.
  assert (Hbound : S^3*rho^2 < 1) by nra. nra.
Qed.

(* This is the remaining dynamical construction, not an axiom or a proved
   claim. The theorem below checks its implication to the original target. *)
Definition symbolic_height_ray_claim : Prop :=
  forall nm : planar_norm, exists T, forall H, T < H -> exists z,
    has_limsup (lattice_height_orbit nm (orbit_frame z id2)) H.

Theorem hall_ray_from_symbolic_heights : symbolic_height_ray_claim -> hall_ray_claim.
Proof.
  intros Hconstruction nm. destruct (Hconstruction nm) as [T HT].
  destruct (small_constants_give_large_heights T) as [rho0 [Hr0 Hlarge]].
  exists rho0; split; [exact Hr0|]. intros rho Hr.
  destruct (HT (height_for_constant rho) (Hlarge rho Hr)) as [z Hz].
  exists (u_code z). apply symbolic_height_realizes_constant; [lra|exact Hz].
Qed.

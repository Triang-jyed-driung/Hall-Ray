From Stdlib Require Import Reals Psatz FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices LatticeBasis
  PaperTarget NormGeometry DaniCorrespondence LatticeSystole SystoleContinuity
  SystoleCurves NormalizedFlow LatticeReturns TwoSidedCoding Concatenation.
Open Scope R_scope.

Lemma reciprocal_relative_difference : forall a b h,
  0 < a -> 0 < b -> Rabs (b-a) <= h*a ->
  Rabs (/a-/b) <= h* /b.
Proof.
  intros a b h Ha Hb Hdiff. apply absolute_difference_sandwich in Hdiff.
  apply Rabs_le; split.
  - apply (Rmult_le_reg_r (a*b)); [nra|].
    replace (-(h* /b)*(a*b)) with (-h*a) by (field; lra).
    replace ((/a-/b)*(a*b)) with (b-a) by (field; lra). lra.
  - apply (Rmult_le_reg_r (a*b)); [nra|].
    replace ((h* /b)*(a*b)) with (h*a) by (field; lra).
    replace ((/a-/b)*(a*b)) with (b-a) by (field; lra). lra.
Qed.

Theorem cusp_height_left_relative_continuity : forall nm,
  exists K, 0 < K /\ forall A L d,
    det3 A = 1 -> det3 L = 1 ->
    0 <= d -> K*d <= 1 -> matrices_close3 d id3 L ->
    Rabs (cusp_height nm A-cusp_height nm (mul3 L A)) <=
      K*d*cusp_height nm (mul3 L A).
Proof.
  intro nm. destruct (systole_left_relative_continuity nm) as [K [HK Hb]].
  exists K; split; [exact HK|]. intros A L d HA HL Hd Hsmall Hclose.
  unfold cusp_height. apply reciprocal_relative_difference.
  - apply systole_positive; exact HA.
  - apply systole_positive. rewrite mul3_determinant, HA, HL; ring.
  - exact (Hb A L d Hd Hsmall Hclose).
Qed.

Definition decaying_shear v w t :=
  stable_shear (v/(exp t)^3) (w/(exp t)^3).

Lemma stable_shear_determinant : forall v w, det3 (stable_shear v w) = 1.
Proof. intros v w; unfold det3, stable_shear; simpl; ring. Qed.

Theorem flowing_stable_shear : forall v w t,
  mul3 (diagonal_flow t) (stable_shear v w) =
    mul3 (decaying_shear v w t) (diagonal_flow t).
Proof.
  intros v w t. pose proof (exp_pos t).
  apply mat3_ext; unfold diagonal_flow, decaying_shear, flow_scale, stable_shear, mul3;
    simpl; field; lra.
Qed.

Lemma decaying_shear_close : forall v w eps,
  0 < eps -> exists T, forall t, T <= t -> matrices_close3 eps id3 (decaying_shear v w t).
Proof.
  intros v w eps He.
  set (S := Rabs v+Rabs w+1).
  assert (HS : 0 < S) by (unfold S; pose proof (Rabs_pos v); pose proof (Rabs_pos w); lra).
  exists (S/eps). intros t Ht.
  assert (HT : 0 < S/eps) by (apply Rdiv_lt_0_compat; assumption).
  pose proof (exp_ineq1_le t) as Hexp.
  assert (He1 : 1 <= exp t) by lra.
  assert (Hscaled : S <= eps*exp t).
  { apply (Rmult_le_compat_r eps) in Ht; [|lra].
    replace (S/eps*eps) with S in Ht by (field; lra). nra. }
  assert (Hcube : exp t <= (exp t)^3).
  { assert (1 <= (exp t)^2) by (pose proof (pow_incr 1 (exp t) 2 ltac:(lra)); simpl in *; nra).
    simpl; nra. }
  assert (Hbounds : forall a, Rabs a <= S -> Rabs (a/(exp t)^3) <= eps).
  { intros a Ha. unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
    rewrite (Rabs_right ((exp t)^3)) by (apply Rle_ge, pow_le; lra).
    apply (Rmult_le_reg_r ((exp t)^3)); [apply pow_lt; lra|].
    replace (Rabs a* / (exp t)^3*(exp t)^3) with (Rabs a) by (field; lra). nra. }
  unfold matrices_close3, entries_bounded3, matrix_difference3, decaying_shear,
    stable_shear, id3; simpl. fold ((exp t)^3).
  replace (1-1) with 0 by ring. replace (0-0) with 0 by ring. rewrite Rabs_R0.
  replace (v/(exp t)^3-0) with (v/(exp t)^3) by ring.
  replace (w/(exp t)^3-0) with (w/(exp t)^3) by ring.
  repeat split; try lra; apply Hbounds; unfold S; pose proof (Rabs_pos v); pose proof (Rabs_pos w); lra.
Qed.

Definition lattice_height_orbit nm A t := cusp_height nm (mul3 (diagonal_flow t) A).

Theorem stable_shear_height_difference : forall nm A v w H,
  det3 A = 1 ->
  has_limsup (lattice_height_orbit nm (mul3 (stable_shear v w) A)) H ->
  asymptotic_difference (lattice_height_orbit nm (mul3 (stable_shear v w) A))
    (lattice_height_orbit nm A).
Proof.
  intros nm A v w H HA [Hupper Hpeaks] eps He.
  destruct (cusp_height_left_relative_continuity nm) as [K [HK Hb]].
  set (M := Rabs H+2).
  assert (HM : 0 < M) by (unfold M; pose proof (Rabs_pos H); lra).
  set (d := Rmin (1/(2*K)) (eps/(2*K*M))).
  assert (Hd : 0 < d) by (apply Rmin_pos; apply Rdiv_lt_0_compat; nra).
  assert (Hsmall : K*d <= 1/2).
  { pose proof (Rmin_l (1/(2*K)) (eps/(2*K*M))) as Hmin.
    change (d <= 1/(2*K)) in Hmin.
    apply (Rmult_le_compat_r (2*K)) in Hmin; [|nra].
    replace (1/(2*K)*(2*K)) with 1 in Hmin by (field; lra). nra. }
  assert (Herr : K*d*M < eps).
  { pose proof (Rmin_r (1/(2*K)) (eps/(2*K*M))) as Hmin.
    change (d <= eps/(2*K*M)) in Hmin.
    apply (Rmult_le_compat_r (2*K*M)) in Hmin; [|nra].
    replace (eps/(2*K*M)*(2*K*M)) with eps in Hmin by (field; nra). nra. }
  destruct (decaying_shear_close v w d Hd) as [T1 Hclose].
  destruct (Hupper 1 ltac:(lra)) as [T2 Hbound].
  exists (Rmax T1 T2). intros t Ht.
  assert (HT1 : T1 <= t) by (pose proof (Rmax_l T1 T2); lra).
  assert (HT2 : T2 <= t) by (pose proof (Rmax_r T1 T2); lra).
  assert (Hbase : det3 (mul3 (diagonal_flow t) A) = 1).
  { rewrite mul3_determinant, diagonal_flow_unimodular, HA; ring. }
  pose proof (Hb (mul3 (diagonal_flow t) A) (decaying_shear v w t) d Hbase
    (stable_shear_determinant _ _) ltac:(lra) ltac:(lra) (Hclose t HT1)) as Hdiff.
  assert (Horbit : mul3 (decaying_shear v w t) (mul3 (diagonal_flow t) A) =
    mul3 (diagonal_flow t) (mul3 (stable_shear v w) A)).
  { rewrite <- mul3_assoc, <- flowing_stable_shear, mul3_assoc; reflexivity. }
  rewrite Horbit in Hdiff.
  unfold lattice_height_orbit. rewrite Rabs_minus_sym.
  eapply Rle_lt_trans; [exact Hdiff|].
  eapply Rle_lt_trans; [|exact Herr].
  apply Rmult_le_compat_l; [nra|].
  specialize (Hbound t HT2). unfold lattice_height_orbit in Hbound.
  unfold M. pose proof (Rle_abs H); lra.
Qed.

Theorem forgetting_stable_shear : forall nm A v w H,
  det3 A = 1 ->
  has_limsup (lattice_height_orbit nm (mul3 (stable_shear v w) A)) H ->
  has_limsup (lattice_height_orbit nm A) H.
Proof.
  intros nm A v w H HA Hlim.
  eapply limsup_stable_under_vanishing_error; [exact Hlim|].
  apply (stable_shear_height_difference nm A v w H HA Hlim).
Qed.

Lemma normalizing_block_is_flow : forall i,
  0 < i ->
  block3 (frame_normalizer i*i) (scale2 (frame_normalizer i) id2) =
    diagonal_flow (ln (frame_normalizer i)).
Proof.
  intros i Hi. unfold diagonal_flow.
  rewrite exp_ln by apply frame_normalizer_positive.
  pose proof (frame_normalizer_cube i Hi) as Hcube.
  pose proof (frame_normalizer_positive i) as Hpos.
  apply mat3_ext; unfold block3, scale2, id2, flow_scale; simpl; try ring.
  apply (Rmult_eq_reg_r (frame_normalizer i*frame_normalizer i)); [|nra].
  replace (/ (frame_normalizer i*frame_normalizer i)*
    (frame_normalizer i*frame_normalizer i)) with 1 by (field; lra). nra.
Qed.

Theorem normalized_frame_forgetting_past : forall x y v w,
  0 < chart_weight x y v w ->
  normalized_frame x y v w id2 =
    mul3 (diagonal_flow (ln (frame_normalizer (chart_weight x y v w))))
      (mul3 (stable_shear (v/chart_weight x y v w) (w/chart_weight x y v w)) (hx x y)).
Proof.
  intros x y v w Hi. unfold normalized_frame.
  rewrite forgetting_past_factorization by (unfold chart_weight in Hi; lra).
  fold (chart_weight x y v w).
  rewrite normalizing_block_is_flow by exact Hi. reflexivity.
Qed.

Lemma hx_determinant : forall x y, det3 (hx x y) = 1.
Proof. intros; unfold hx, det3; simpl; ring. Qed.

Lemma height_orbit_time_translation : forall nm A c t,
  lattice_height_orbit nm (mul3 (diagonal_flow c) A) t =
    lattice_height_orbit nm A (t+c).
Proof.
  intros. unfold lattice_height_orbit. rewrite <- mul3_assoc, <- diagonal_flow_add; reflexivity.
Qed.

Theorem forgetting_normalized_frame : forall nm x y v w H,
  0 < chart_weight x y v w ->
  has_limsup (lattice_height_orbit nm (normalized_frame x y v w id2)) H ->
  has_limsup (lattice_height_orbit nm (hx x y)) H.
Proof.
  intros nm x y v w H Hi Hlim.
  rewrite normalized_frame_forgetting_past in Hlim by exact Hi.
  set (c := ln (frame_normalizer (chart_weight x y v w))) in *.
  pose proof (limsup_time_shift _ H (-c) Hlim) as Hshift.
  assert (Hsame : (fun t => lattice_height_orbit nm
    (mul3 (diagonal_flow c)
      (mul3 (stable_shear (v/chart_weight x y v w) (w/chart_weight x y v w)) (hx x y))) (t+-c)) =
    lattice_height_orbit nm
      (mul3 (stable_shear (v/chart_weight x y v w) (w/chart_weight x y v w)) (hx x y))).
  { apply functional_extensionality. intro t. rewrite height_orbit_time_translation.
    replace (t+-c+c) with t by ring. reflexivity. }
  rewrite Hsame in Hshift.
  eapply forgetting_stable_shear; [apply hx_determinant|exact Hshift].
Qed.

Theorem forgetting_symbolic_past : forall nm z H,
  has_limsup (lattice_height_orbit nm (orbit_frame z id2)) H ->
  has_limsup (lattice_height_orbit nm (hx (fst (u_code z)) (snd (u_code z)))) H.
Proof.
  intros nm z H Hlim. apply (forgetting_normalized_frame nm
    (fst (u_code z)) (snd (u_code z)) (fst (v_code z)) (snd (v_code z)) H).
  - pose proof (chart_weight_bounds _ _ _ _ (u_code_inside z) (v_code_inside z)); lra.
  - exact Hlim.
Qed.

From Stdlib Require Import Reals Psatz Lia ZArith Ratan.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  DefectLimit EllipticConjugacy RealRotationDensity.
Open Scope R_scope.

Lemma rotation_zero : rotation 0 = id2.
Proof. unfold rotation, id2. rewrite cos_0, sin_0. apply mat2_ext; simpl; ring. Qed.
Lemma rotation_addition : forall a b, mul2 (rotation a) (rotation b) = rotation (a+b).
Proof.
  intros a b. apply mat2_ext; unfold mul2, rotation; simpl;
    rewrite ?cos_plus, ?sin_plus; ring.
Qed.
Theorem rotation_natural_power : forall t n,
  matrix_power (rotation t) n = rotation (INR n*t).
Proof.
  intros t n. induction n.
  - simpl. replace (0*t) with 0 by ring. symmetry; apply rotation_zero.
  - cbn [matrix_power]. rewrite IHn, rotation_addition, S_INR.
    f_equal; ring.
Qed.

Lemma trigonometric_integer_period : forall t z,
  sin (t+2*PI*IZR z) = sin t /\ cos (t+2*PI*IZR z) = cos t.
Proof.
  intros t z. destruct (Z_le_gt_dec 0 z) as [Hz|Hz].
  - assert (Hcast : IZR z = INR (Z.to_nat z)).
    { rewrite INR_IZR_INZ, Z2Nat.id by exact Hz. reflexivity. }
    rewrite Hcast.
    replace (t+2*PI*INR (Z.to_nat z)) with (t+2*INR (Z.to_nat z)*PI) by ring.
    split; [apply sin_period|apply cos_period].
  - assert (Hcast : IZR (-z) = INR (Z.to_nat (-z))).
    { rewrite INR_IZR_INZ, Z2Nat.id by lia. reflexivity. }
    pose proof (sin_period (t+2*PI*IZR z) (Z.to_nat (-z))) as Hsin.
    pose proof (cos_period (t+2*PI*IZR z) (Z.to_nat (-z))) as Hcos.
    rewrite <- Hcast, opp_IZR in Hsin, Hcos.
    replace (t+2*PI*IZR z+2*(-IZR z)*PI) with t in Hsin, Hcos by ring.
    split; symmetry; assumption.
Qed.
Theorem rotation_integer_period : forall t z,
  rotation (t+2*PI*IZR z) = rotation t.
Proof.
  intros t z. destruct (trigonometric_integer_period t z) as [Hs Hc].
  unfold rotation. rewrite Hs, Hc; reflexivity.
Qed.
Lemma rotation_integral_turn : forall z, rotation (2*PI*IZR z) = id2.
Proof.
  intro z. replace (2*PI*IZR z) with (0+2*PI*IZR z) by ring.
  rewrite rotation_integer_period. apply rotation_zero.
Qed.

Theorem infinite_rotation_number_irrational : forall t,
  (forall n, (0 < n)%nat -> matrix_power (rotation t) n <> id2) ->
  irrational_rotation_number (t/(2*PI)).
Proof.
  intros t Hinf m z Hm Hrel.
  pose proof PI_RGT_0 as Hpi.
  assert (Hlinear : IZR m*t+2*PI*IZR z = 0).
  { assert (Hid : (IZR m*(t/(2*PI))+IZR z)*(2*PI) = IZR m*t+2*PI*IZR z) by (field; lra).
    rewrite Hrel in Hid. nra. }
  destruct (Z_lt_ge_dec 0 m) as [Hpos|Hneg].
  - assert (Hcast : IZR m = INR (Z.to_nat m))
      by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
    assert (Hnat : (0 < Z.to_nat m)%nat) by (pose proof (Z2Nat.id m ltac:(lia)); lia).
    apply (Hinf (Z.to_nat m) Hnat). rewrite rotation_natural_power.
    replace (INR (Z.to_nat m)*t) with (2*PI*IZR (-z)) by (rewrite <- Hcast, opp_IZR; lra).
    apply rotation_integral_turn.
  - assert (Hcast : IZR (-m) = INR (Z.to_nat (-m)))
      by (rewrite INR_IZR_INZ, Z2Nat.id by lia; reflexivity).
    assert (Hnat : (0 < Z.to_nat (-m))%nat) by (pose proof (Z2Nat.id (-m) ltac:(lia)); lia).
    apply (Hinf (Z.to_nat (-m)) Hnat). rewrite rotation_natural_power.
    replace (INR (Z.to_nat (-m))*t) with (2*PI*IZR z) by (rewrite <- Hcast, opp_IZR; lra).
    apply rotation_integral_turn.
Qed.

Theorem special_orthogonal_angle : forall A,
  det2 A = 1 -> orthogonal2 A -> exists t, A = rotation t.
Proof.
  intros [a b c d] Hd Ho.
  destruct (special_orthogonal_shape _ Hd Ho) as [Ha Hb]. simpl in Ha, Hb.
  subst a b. unfold det2 in Hd; simpl in Hd.
  assert (Hcircle : d*d+c*c = 1) by nra.
  assert (Hrange : -1 <= d <= 1) by nra.
  pose proof (cos_acos d Hrange) as Hcos.
  assert (Hsin : sin (acos d) = Rabs c).
  { rewrite sin_acos by exact Hrange.
    replace (1-d²) with (c*c) by (unfold Rsqr; nra).
    apply sqrt_Rsqr_abs. }
  destruct (Rle_dec 0 c) as [Hc|Hc].
  - exists (acos d). apply mat2_ext; unfold rotation; simpl;
      rewrite ?Hcos, ?Hsin; rewrite ?Rabs_right by lra; ring.
  - exists (-acos d). apply mat2_ext; unfold rotation; simpl;
      rewrite ?cos_neg, ?sin_neg, ?Hcos, ?Hsin; rewrite ?Rabs_left by lra; ring.
Qed.

Lemma continuity_epsilon : forall f t,
  continuity_pt f t -> forall eps, 0 < eps ->
  exists delta, 0 < delta /\ forall u, Rabs (u-t) < delta -> Rabs (f u-f t) < eps.
Proof.
  intros f t H eps He.
  unfold continuity_pt, continue_in, limit1_in, limit_in in H; simpl in H.
  destruct (H eps He) as [delta [Hd Hbound]]. exists delta. split; auto.
  intros u Hu. destruct (Req_dec t u) as [Hsame|Hneq].
  - subst u. replace (f t-f t) with 0 by ring. rewrite Rabs_R0; exact He.
  - apply Hbound. split; [split; [exact I|exact Hneq]|exact Hu].
Qed.

Lemma opnorm_entry_sum : forall A, opnorm A <= entry_bound A.
Proof.
  intro A. apply opnorm_upper. intros v Hv.
  pose proof (action_entry_bound A v). pose proof (entry_bound_nonnegative A). nra.
Qed.

Theorem rotation_continuity : forall t eps, 0 < eps ->
  exists delta, 0 < delta /\ forall u,
    Rabs (u-t) < delta -> opnorm (sub2 (rotation u) (rotation t)) < eps.
Proof.
  intros t eps He.
  destruct (continuity_epsilon sin t (continuity_sin t) (eps/8) ltac:(lra)) as [ds [Hds Hsin]].
  destruct (continuity_epsilon cos t (continuity_cos t) (eps/8) ltac:(lra)) as [dc [Hdc Hcos]].
  exists (Rmin ds dc). split; [apply Rmin_pos; lra|].
  intros u Hu. pose proof (Rmin_l ds dc). pose proof (Rmin_r ds dc).
  specialize (Hsin u ltac:(lra)). specialize (Hcos u ltac:(lra)).
  pose proof (opnorm_entry_sum (sub2 (rotation u) (rotation t))) as Hnorm.
  unfold entry_bound in Hnorm. rewrite a11_sub, a12_sub, a21_sub, a22_sub in Hnorm.
  unfold rotation in Hnorm; simpl in Hnorm.
  replace (-sin u- -sin t) with (-(sin u-sin t)) in Hnorm by ring.
  rewrite Rabs_Ropp in Hnorm. fold (rotation u) (rotation t) in Hnorm. lra.
Qed.

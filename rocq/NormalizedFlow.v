From Stdlib Require Import Reals Psatz Lia.
From HallRay Require Import MatrixAlgebra ReturnIdentity ReturnBranches StableBranches
  IntegralMatrices MarkedCocycle FiberProducts ConcreteCocycle.
Open Scope R_scope.

Lemma exponential_natural_power : forall t n, (exp t)^n = exp (INR n*t).
Proof.
  intros t n; induction n.
  - simpl. replace (0*t) with 0 by ring. rewrite exp_0; reflexivity.
  - cbn [pow]. rewrite IHn, <- exp_plus, S_INR. f_equal; ring.
Qed.

Definition positive_cube_root (t : R) := exp (ln t/3).
Definition frame_normalizer (t : R) := /positive_cube_root t.
Lemma positive_cube_root_positive : forall t, 0 < positive_cube_root t.
Proof. intro t; apply exp_pos. Qed.
Lemma positive_cube_root_cube : forall t, 0 < t -> (positive_cube_root t)^3 = t.
Proof.
  intros t Ht. unfold positive_cube_root. rewrite exponential_natural_power.
  replace (INR 3*(ln t/3)) with (ln t) by (simpl; field). apply exp_ln; exact Ht.
Qed.
Lemma frame_normalizer_positive : forall t, 0 < frame_normalizer t.
Proof. intro t; apply Rinv_0_lt_compat, positive_cube_root_positive. Qed.
Lemma frame_normalizer_cube : forall t, 0 < t -> (frame_normalizer t)^3*t = 1.
Proof.
  intros t Ht. unfold frame_normalizer.
  rewrite <- (positive_cube_root_cube t Ht) at 2.
  field. pose proof (positive_cube_root_positive t); lra.
Qed.

Lemma positive_cube_injective : forall x y,
  0 < x -> 0 < y -> x^3 = y^3 -> x = y.
Proof.
  intros x y Hx Hy Hcube.
  assert (Hprod : (x-y)*(x*x+x*y+y*y) = 0) by nra.
  apply Rmult_integral in Hprod. destruct Hprod; [lra|].
  pose proof (Rmult_lt_0_compat x y Hx Hy). nra.
Qed.

Definition chart_weight (x y v w : R) := 1+v*x+w*y.
Definition normalized_frame (x y v w : R) (E : mat2) :=
  chart (frame_normalizer (chart_weight x y v w)) x y v w E.

Lemma chart_weight_bounds : forall x y v w,
  in_U x y -> in_V v w -> 124/125 <= chart_weight x y v w <= 126/125.
Proof.
  intros x y v w HU HV. pose proof (chart_denominator_positive x y v w HU HV) as Hlow.
  assert (HVneg : in_V (-v) (-w)) by (unfold in_V in *; lra).
  pose proof (chart_denominator_positive x y (-v) (-w) HU HVneg) as Hhigh.
  unfold chart_weight; split; nra.
Qed.
Theorem normalized_frame_unimodular : forall x y v w E,
  in_U x y -> in_V v w -> det2 E = 1 -> det3 (normalized_frame x y v w E) = 1.
Proof.
  intros x y v w E HU HV HE. apply normalized_chart_unimodular; [|exact HE].
  change ((frame_normalizer (chart_weight x y v w))^3*chart_weight x y v w = 1).
  apply frame_normalizer_cube. pose proof (chart_weight_bounds x y v w HU HV); lra.
Qed.

Lemma block3_product : forall a A b B,
  mul3 (block3 a A) (block3 b B) = block3 (a*b) (mul2 A B).
Proof. intros a [] b []; apply mat3_ext; unfold block3, mul3, mul2; simpl; ring. Qed.
Lemma block3_scale : forall c a A,
  scale3 c (block3 a A) = block3 (c*a) (scale2 c A).
Proof. intros c a []; apply mat3_ext; unfold block3, scale3, scale2; simpl; ring. Qed.
Lemma scale3_product_left : forall c A B, mul3 (scale3 c A) B = scale3 c (mul3 A B).
Proof. intros c [] []; apply mat3_ext; unfold scale3, mul3; simpl; ring. Qed.
Lemma scale3_product_right : forall c A B, mul3 A (scale3 c B) = scale3 c (mul3 A B).
Proof. intros c [] []; apply mat3_ext; unfold scale3, mul3; simpl; ring. Qed.
Lemma scale2_identity_product : forall r A, mul2 (scale2 r id2) A = scale2 r A.
Proof. intros r []; apply mat2_ext; unfold mul2, scale2, id2; simpl; ring. Qed.
Lemma matrix_right_scale : forall r A B, mul2 A (scale2 r B) = scale2 r (mul2 A B).
Proof. intros r [] []; apply mat2_ext; unfold mul2, scale2; simpl; ring. Qed.
Lemma flow_scale_block : forall r, flow_scale r = block3 (/(r*r)) (scale2 r id2).
Proof. intro r; apply mat3_ext; unfold flow_scale, block3, scale2, id2; simpl; ring. Qed.

(* Normalization relations, isolated from the matrix computation. *)
Lemma normalized_scalar_relations : forall i0 i1 a d,
  0 < i0 -> 0 < i1 -> 0 < a -> 0 < d -> a*i1 = d*i0 ->
  let c0 := frame_normalizer i0 in
  let c1 := frame_normalizer i1 in
  let r := positive_cube_root (a*sqrt d) in
  c0*a/(r*r) = c1 /\ c0*r/sqrt d = c1.
Proof.
  intros i0 i1 a d Hi0 Hi1 Ha Hd; cbn zeta.
  set (c0 := frame_normalizer i0). set (c1 := frame_normalizer i1).
  set (r := positive_cube_root (a*sqrt d)).
  assert (Hc0 : 0 < c0) by apply frame_normalizer_positive.
  assert (Hc1 : 0 < c1) by apply frame_normalizer_positive.
  assert (Hr : 0 < r) by apply positive_cube_root_positive.
  assert (Hs : 0 < sqrt d) by (apply sqrt_lt_R0; exact Hd).
  assert (H0 : c0^3*i0 = 1) by (apply frame_normalizer_cube; exact Hi0).
  assert (H1 : c1^3*i1 = 1) by (apply frame_normalizer_cube; exact Hi1).
  assert (HR : r^3 = a*sqrt d).
  { apply positive_cube_root_cube, Rmult_lt_0_compat; assumption. }
  assert (HS : sqrt d*sqrt d = d) by (apply sqrt_sqrt; lra).
  intro Hratio.
  assert (Hcross : c0^3*a = c1^3*d).
  { apply (Rmult_eq_reg_r (i0*i1)); [|nra].
    replace (c0^3*a*(i0*i1)) with (a*(c0^3*i0)*i1) by ring.
    replace (c1^3*d*(i0*i1)) with (d*(c1^3*i1)*i0) by ring.
    rewrite H0, H1; nra. }
  assert (Hlower : c0*r = c1*sqrt d).
  { apply positive_cube_injective; [nra|nra|].
    replace ((c0*r)^3) with (c0^3*r^3) by ring.
    replace ((c1*sqrt d)^3) with (c1^3*(sqrt d*sqrt d)*sqrt d) by ring.
    rewrite HR, HS. replace (c0^3*(a*sqrt d)) with ((c0^3*a)*sqrt d) by ring.
    rewrite Hcross; ring. }
  assert (Hupper : c0*a = c1*(r*r)).
  { apply (Rmult_eq_reg_r r); [|lra].
    replace (c0*a*r) with (a*(c0*r)) by ring.
    replace (c1*(r*r)*r) with (c1*r^3) by ring.
    rewrite Hlower, HR; ring. }
  split; [rewrite Hupper|rewrite Hlower]; field; lra.
Qed.

Lemma normalize_marked_equation : forall B0 B1 Gamma E M c0 c1 a d r,
  mul3 B0 Gamma = mul3 (block3 a (scale2 (/sqrt d) M)) B1 ->
  c0*a/(r*r) = c1 -> c0*r/sqrt d = c1 ->
  mul3 (flow_scale r) (mul3 (scale3 c0 (mul3 (block3 1 E) B0)) Gamma) =
  scale3 c1 (mul3 (block3 1 (mul2 E M)) B1).
Proof.
  intros B0 B1 Gamma E M c0 c1 a d r Hraw Htop Hbottom.
  rewrite scale3_product_left, scale3_product_right, !mul3_assoc, Hraw.
  rewrite <- (mul3_assoc (block3 1 E) (block3 a (scale2 (/sqrt d) M)) B1).
  rewrite <- (mul3_assoc (flow_scale r) (mul3 (block3 1 E) (block3 a (scale2 (/sqrt d) M))) B1).
  rewrite <- scale3_product_left.
  assert (Hblock : scale3 c0 (mul3 (flow_scale r)
    (mul3 (block3 1 E) (block3 a (scale2 (/sqrt d) M)))) = scale3 c1 (block3 1 (mul2 E M))).
  { rewrite flow_scale_block, !block3_product, scale2_identity_product, matrix_right_scale,
      !matrix_scale_composition, !block3_scale, !matrix_scale_composition.
    replace (c0*(/(r*r)*(1*a))) with (c0*a/(r*r)) by (unfold Rdiv; ring).
    replace (c0*(r*(/sqrt d))) with (c0*r/sqrt d) by (unfold Rdiv; ring).
    rewrite Htop, Hbottom. replace (c1*1) with c1 by ring. reflexivity. }
  rewrite Hblock, scale3_product_left. reflexivity.
Qed.

Definition branch_roof_a (x y v w : R) := positive_cube_root ((101+10*v+w)*sqrt (da x y)).
Definition branch_roof_b (x y v w : R) := positive_cube_root ((101+10*v-w)*sqrt (db x y)).

Lemma branch_weight_balance_a : forall x y v w,
  in_U x y -> in_V v w ->
  (101+10*v+w)*chart_weight x y (psi_a1 v w) (psi_a2 v w) =
  da x y*chart_weight (phi_a1 x y) (phi_a2 x y) v w.
Proof.
  intros x y v w HU HV. pose proof (da_bounds x y HU). pose proof (sa_bounds v w HV).
  unfold da, sa in *. unfold chart_weight, psi_a1, psi_a2, phi_a1, phi_a2, da.
  field; split; lra.
Qed.
Lemma branch_weight_balance_b : forall x y v w,
  in_U x y -> in_V v w ->
  (101+10*v-w)*chart_weight x y (psi_b1 v w) (psi_b2 v w) =
  db x y*chart_weight (phi_b1 x y) (phi_b2 x y) v w.
Proof.
  intros x y v w HU HV. pose proof (db_bounds x y HU). pose proof (sb_bounds v w HV).
  unfold db, sb in *. unfold chart_weight, psi_b1, psi_b2, phi_b1, phi_b2, db.
  field; split; lra.
Qed.

Theorem normalized_marked_return_a : forall x y v w E,
  in_U x y -> in_V v w ->
  mul3 (flow_scale (branch_roof_a x y v w))
    (mul3 (normalized_frame (phi_a1 x y) (phi_a2 x y) v w E) gamma_a) =
  normalized_frame x y (psi_a1 v w) (psi_a2 v w) (mul2 E (normalized_a x y)).
Proof.
  intros x y v w E HU HV.
  pose proof (chart_weight_bounds (phi_a1 x y) (phi_a2 x y) v w (phi_a_invariant x y HU) HV) as H0.
  pose proof (chart_weight_bounds x y (psi_a1 v w) (psi_a2 v w) HU (psi_a_invariant v w HV)) as H1.
  pose proof (da_bounds x y HU) as Hd. pose proof (sa_bounds v w HV) as HA.
  destruct (normalized_scalar_relations
    (chart_weight (phi_a1 x y) (phi_a2 x y) v w)
    (chart_weight x y (psi_a1 v w) (psi_a2 v w)) (101+10*v+w) (da x y)
    ltac:(lra) ltac:(lra) ltac:(unfold sa in HA; lra)
    ltac:(lra) (branch_weight_balance_a x y v w HU HV)) as [Htop Hbottom].
  unfold normalized_frame, chart, branch_roof_a.
  eapply normalize_marked_equation with (a := 101+10*v+w) (d := da x y); [|exact Htop|exact Hbottom].
  rewrite normalized_schur_a by exact HU.
  apply raw_marked_return_a; [lra|unfold sa in HA; lra].
Qed.
Theorem normalized_marked_return_b : forall x y v w E,
  in_U x y -> in_V v w ->
  mul3 (flow_scale (branch_roof_b x y v w))
    (mul3 (normalized_frame (phi_b1 x y) (phi_b2 x y) v w E) gamma_b) =
  normalized_frame x y (psi_b1 v w) (psi_b2 v w) (mul2 E (normalized_b x y)).
Proof.
  intros x y v w E HU HV.
  pose proof (chart_weight_bounds (phi_b1 x y) (phi_b2 x y) v w (phi_b_invariant x y HU) HV) as H0.
  pose proof (chart_weight_bounds x y (psi_b1 v w) (psi_b2 v w) HU (psi_b_invariant v w HV)) as H1.
  pose proof (db_bounds x y HU) as Hd. pose proof (sb_bounds v w HV) as HA.
  destruct (normalized_scalar_relations
    (chart_weight (phi_b1 x y) (phi_b2 x y) v w)
    (chart_weight x y (psi_b1 v w) (psi_b2 v w)) (101+10*v-w) (db x y)
    ltac:(lra) ltac:(lra) ltac:(unfold sb in HA; lra)
    ltac:(lra) (branch_weight_balance_b x y v w HU HV)) as [Htop Hbottom].
  unfold normalized_frame, chart, branch_roof_b.
  eapply normalize_marked_equation with (a := 101+10*v-w) (d := db x y); [|exact Htop|exact Hbottom].
  rewrite normalized_schur_b by exact HU.
  apply raw_marked_return_b; [lra|unfold sb in HA; lra].
Qed.

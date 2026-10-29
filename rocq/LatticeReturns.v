From Stdlib Require Import Reals Psatz Lia Arith ZArith.
From HallRay Require Import MatrixAlgebra ReturnIdentity ReturnBranches StableBranches
  IntegralMatrices MarkedCocycle FiberProducts ConcreteCocycle SymbolicCoding SymbolicCocycle
  PeriodicReturns Concatenation StableCoding TwoSidedCoding NormalizedFlow.
Open Scope R_scope.

Definition orbit_frame (z : biword) (E : mat2) := normalized_frame
  (fst (u_code z)) (snd (u_code z)) (fst (v_code z)) (snd (v_code z)) E.
Definition orbit_roof_scale (z : biword) :=
  if z 0%Z then branch_roof_a
    (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z))) (fst (v_code z)) (snd (v_code z))
  else branch_roof_b
    (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z))) (fst (v_code z)) (snd (v_code z)).
Definition orbit_roof_time (z : biword) := ln (orbit_roof_scale z).
Definition diagonal_flow (t : R) := flow_scale (exp t).
Definition orbit_fiber (z : biword) := cocycle (future_of z).

Lemma cube_roof_uniform_bounds : forall a d,
  503/5 <= a <= 507/5 -> 503/5 <= d <= 507/5 ->
  9 < positive_cube_root (a*sqrt d) < 11.
Proof.
  intros a d Ha Hd.
  pose proof (sqrt_at_least_ten d ltac:(lra)) as Hslo.
  pose proof (Rsqr_sqrt d ltac:(lra)) as Hsq; unfold Rsqr in Hsq.
  assert (Hshi : sqrt d <= 11) by nra.
  pose proof (positive_cube_root_positive (a*sqrt d)) as Hr.
  pose proof (positive_cube_root_cube (a*sqrt d) ltac:(apply Rmult_lt_0_compat; lra)) as Hcube.
  assert (Hlow : 1000 <= a*sqrt d).
  { pose proof (Rmult_le_compat 100 a 10 (sqrt d) ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra)); nra. }
  assert (Hhigh : a*sqrt d <= 1122).
  { pose proof (Rmult_le_compat a 102 (sqrt d) 11 ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra)); nra. }
  split.
  - destruct (Rlt_dec 9 (positive_cube_root (a*sqrt d))); auto.
    pose proof (pow_incr (positive_cube_root (a*sqrt d)) 9 3 ltac:(lra)); simpl in H; nra.
  - destruct (Rlt_dec (positive_cube_root (a*sqrt d)) 11); auto.
    pose proof (pow_incr 11 (positive_cube_root (a*sqrt d)) 3 ltac:(lra)); simpl in H; nra.
Qed.

Theorem orbit_roof_scale_bounds : forall z, 9 < orbit_roof_scale z < 11.
Proof.
  intro z. pose proof (u_code_inside (bi_shift z)) as HU.
  pose proof (v_code_inside z) as HV. unfold inside in HU; unfold stable_inside in HV.
  unfold orbit_roof_scale. destruct (z 0%Z); [unfold branch_roof_a|unfold branch_roof_b];
    apply cube_roof_uniform_bounds.
  - pose proof (sa_bounds _ _ HV); unfold sa in *; lra.
  - apply da_bounds; exact HU.
  - pose proof (sb_bounds _ _ HV); unfold sb in *; lra.
  - apply db_bounds; exact HU.
Qed.
Theorem orbit_roof_time_gt_one : forall z, 1 < orbit_roof_time z.
Proof.
  intro z. pose proof (orbit_roof_scale_bounds z).
  pose proof exp_le_3 as He. pose proof (exp_pos 1) as Hp.
  pose proof (ln_increasing (exp 1) (orbit_roof_scale z) Hp ltac:(lra)) as Hln.
  rewrite ln_exp in Hln. exact Hln.
Qed.

Lemma orbit_fiber_formula : forall z, orbit_fiber z =
  fiber_matrix (z 0%Z) (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z))).
Proof.
  intro z. unfold orbit_fiber, cocycle.
  assert (Hshift : coded (shift (future_of z)) = coded (future_of (bi_shift z)))
    by (apply coded_extensional; apply future_shift_matches).
  rewrite Hshift; reflexivity.
Qed.

Theorem orbit_frame_unimodular : forall z E,
  det2 E = 1 -> det3 (orbit_frame z E) = 1.
Proof.
  intros z E HE. apply normalized_frame_unimodular.
  - exact (u_code_inside z).
  - exact (v_code_inside z).
  - exact HE.
Qed.

Theorem orbit_marked_return : forall z E,
  mul3 (diagonal_flow (orbit_roof_time z)) (mul3 (orbit_frame z E) (marking (z 0%Z))) =
    orbit_frame (bi_shift z) (mul2 E (orbit_fiber z)).
Proof.
  intros z E. unfold diagonal_flow, orbit_roof_time.
  rewrite exp_ln by (pose proof (orbit_roof_scale_bounds z); lra).
  rewrite orbit_fiber_formula.
  unfold orbit_frame. rewrite (u_code_recursion z), (v_code_recursion z).
  unfold orbit_roof_scale, marking. destruct (z 0%Z); unfold branch, psi_branch;
    simpl fst; simpl snd; unfold fiber_matrix.
  - apply normalized_marked_return_a; [exact (u_code_inside (bi_shift z))|exact (v_code_inside z)].
  - apply normalized_marked_return_b; [exact (u_code_inside (bi_shift z))|exact (v_code_inside z)].
Qed.

Lemma flow_scale_multiplication : forall r s, r <> 0 -> s <> 0 ->
  flow_scale (r*s) = mul3 (flow_scale r) (flow_scale s).
Proof.
  intros r s Hr Hs. apply mat3_ext; unfold flow_scale, mul3; simpl; field; auto.
Qed.
Theorem diagonal_flow_add : forall t s,
  diagonal_flow (t+s) = mul3 (diagonal_flow t) (diagonal_flow s).
Proof.
  intros t s; unfold diagonal_flow. rewrite exp_plus. apply flow_scale_multiplication;
    pose proof (exp_pos t); pose proof (exp_pos s); lra.
Qed.
Theorem diagonal_flow_zero : diagonal_flow 0 = id3.
Proof.
  unfold diagonal_flow. rewrite exp_0. apply mat3_ext; unfold flow_scale, id3; simpl; field.
Qed.
Theorem diagonal_flow_unimodular : forall t, det3 (diagonal_flow t) = 1.
Proof.
  intro t. unfold diagonal_flow, det3, flow_scale; simpl.
  field. pose proof (exp_pos t); lra.
Qed.

Fixpoint orbit_shift (n : nat) (z : biword) : biword :=
  match n with O => z | S k => orbit_shift k (bi_shift z) end.
Fixpoint orbit_time (n : nat) (z : biword) : R :=
  match n with O => 0 | S k => orbit_roof_time z+orbit_time k (bi_shift z) end.
Fixpoint orbit_product (n : nat) (z : biword) :=
  match n with O => id2 | S k => mul2 (orbit_fiber z) (orbit_product k (bi_shift z)) end.
Fixpoint orbit_markings (n : nat) (z : biword) :=
  match n with O => id3 | S k => mul3 (marking (z 0%Z)) (orbit_markings k (bi_shift z)) end.

Theorem orbit_product_matches_future : forall n z,
  orbit_product n z = fiber_product n (future_of z).
Proof.
  induction n; intro z; [reflexivity|].
  cbn [orbit_product]. rewrite IHn.
  change (mul2 (cocycle (future_of z)) (fiber_product n (future_of (bi_shift z))) =
    mul2 (cocycle (future_of z)) (fiber_product n (shift (future_of z)))).
  f_equal; apply fiber_product_extensional; intro k; symmetry; apply future_shift_matches.
Qed.
Theorem orbit_markings_integral : forall n z, integral_matrix (orbit_markings n z).
Proof.
  induction n; intro z; simpl; [apply integral_identity|].
  apply integral_product; auto using marking_integral.
Qed.
Theorem orbit_markings_unimodular : forall n z, det3 (orbit_markings n z) = 1.
Proof.
  induction n; intro z; simpl.
  - unfold det3, id3; simpl; ring.
  - rewrite mul3_determinant, marking_unimodular, IHn; ring.
Qed.

Theorem orbit_return_identity : forall n z E,
  mul3 (diagonal_flow (orbit_time n z)) (mul3 (orbit_frame z E) (orbit_markings n z)) =
    orbit_frame (orbit_shift n z) (mul2 E (orbit_product n z)).
Proof.
  induction n; intros z E.
  - cbn [orbit_time orbit_markings orbit_shift orbit_product].
    rewrite diagonal_flow_zero, mul3_id_right, mul3_id_left, mul2_id_right; reflexivity.
  - cbn [orbit_time orbit_markings orbit_product orbit_shift].
    rewrite Rplus_comm, diagonal_flow_add.
    rewrite <- (mul3_assoc (orbit_frame z E) (marking (z 0%Z)) (orbit_markings n (bi_shift z))).
    rewrite mul3_assoc.
    rewrite <- (mul3_assoc (diagonal_flow (orbit_roof_time z))
      (mul3 (orbit_frame z E) (marking (z 0%Z))) (orbit_markings n (bi_shift z))).
    rewrite orbit_marked_return, IHn, mul2_assoc; reflexivity.
Qed.

Lemma orbit_shift_by_matches : forall n z k, orbit_shift n z k = bi_shift_by n z k.
Proof.
  induction n; intros z k; simpl; [unfold bi_shift_by; f_equal; lia|].
  rewrite IHn. symmetry; apply bi_shift_by_successor.
Qed.
Theorem orbit_time_lower_bound : forall n z, INR n <= orbit_time n z.
Proof.
  induction n; intro z; [simpl; lra|]. cbn [orbit_time].
  pose proof (orbit_roof_time_gt_one z); specialize (IHn (bi_shift z)). rewrite S_INR; lra.
Qed.

Theorem orbit_time_successor : forall n z,
  orbit_time (S n) z = orbit_time n z+orbit_roof_time (orbit_shift n z).
Proof.
  induction n; intro z; [simpl; ring|].
  change (orbit_roof_time z+orbit_time (S n) (bi_shift z) =
    (orbit_roof_time z+orbit_time n (bi_shift z))+orbit_roof_time (orbit_shift n (bi_shift z))).
  rewrite IHn; ring.
Qed.
Theorem orbit_time_increasing : forall n z, orbit_time n z < orbit_time (S n) z.
Proof.
  intros n z; rewrite orbit_time_successor. pose proof (orbit_roof_time_gt_one (orbit_shift n z)); lra.
Qed.

Theorem orbit_time_cofinal : forall z T, exists n, T < orbit_time n z.
Proof.
  intros z T. destruct (Rlt_dec T 0) as [Hneg|Hnonneg].
  - exists O; simpl; exact Hneg.
  - pose proof (archimed T) as Hup.
    assert (HupZ : (0 < up T)%Z) by (apply lt_IZR; simpl; lra).
    exists (Z.to_nat (up T)).
    pose proof (orbit_time_lower_bound (Z.to_nat (up T)) z) as Hlower.
    rewrite INR_IZR_INZ, Z2Nat.id in Hlower by lia. lra.
Qed.

Theorem orbit_forward_segment_cover : forall z t,
  0 <= t -> exists n r,
    0 <= r < orbit_roof_time (orbit_shift n z) /\ t = orbit_time n z+r.
Proof.
  intros z t Ht.
  destruct (@tail_cover (fun n => orbit_time n z) (fun n => orbit_time_increasing n z)
    (orbit_time_cofinal z) O t Ht) as [n [Hn Htime]].
  exists n, (t-orbit_time n z). rewrite orbit_time_successor in Htime. split; lra.
Qed.

Theorem orbit_segment_identity : forall z E n r,
  mul3 (diagonal_flow (orbit_time n z+r)) (mul3 (orbit_frame z E) (orbit_markings n z)) =
    mul3 (diagonal_flow r) (orbit_frame (orbit_shift n z) (mul2 E (orbit_product n z))).
Proof.
  intros z E n r. rewrite Rplus_comm, diagonal_flow_add, mul3_assoc, orbit_return_identity. reflexivity.
Qed.

Theorem complete_forward_return_system : forall z E t,
  0 <= t -> exists n r,
    0 <= r < orbit_roof_time (orbit_shift n z) /\
    integral_matrix (orbit_markings n z) /\ det3 (orbit_markings n z) = 1 /\
    mul3 (diagonal_flow t) (mul3 (orbit_frame z E) (orbit_markings n z)) =
      mul3 (diagonal_flow r) (orbit_frame (orbit_shift n z) (mul2 E (orbit_product n z))).
Proof.
  intros z E t Ht. destruct (orbit_forward_segment_cover z t Ht) as [n [r [Hr Htime]]].
  exists n, r. split; [exact Hr|]. split; [apply orbit_markings_integral|].
  split; [apply orbit_markings_unimodular|]. rewrite Htime; apply orbit_segment_identity.
Qed.

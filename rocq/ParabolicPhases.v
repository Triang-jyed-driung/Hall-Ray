From Stdlib Require Import Reals Psatz Lia FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  DefectLimit DefectPhases EllipticConjugacy PeriodicReturns LimitingConvergence
  Matrix3Limits EllipticContinuity CirclePeaks.
Open Scope R_scope.

Definition trace_phase_gap t := sqrt (phase_amplitude^2-t^2).
Definition trace_phase (side : bool) t :=
  let g := if side then trace_phase_gap t else -trace_phase_gap t in
  circle_matrix ((trace2 rotation_defect*t-(a12 rotation_defect-a21 rotation_defect)*g)/phase_amplitude^2)
    (((a12 rotation_defect-a21 rotation_defect)*t+trace2 rotation_defect*g)/phase_amplitude^2).

Lemma phase_amplitude_coefficients :
  phase_amplitude^2 = (trace2 rotation_defect)^2+(a12 rotation_defect-a21 rotation_defect)^2.
Proof.
  pose proof phase_amplitude_square. unfold amplitude_squared in H.
  fold (trace2 rotation_defect) in H; nra.
Qed.

Lemma phase_coordinates_circle : forall a b L t g,
  L <> 0 -> a^2+b^2 = L -> t^2+g^2 = L ->
  ((a*t-b*g)/L)*((a*t-b*g)/L)+((b*t+a*g)/L)*((b*t+a*g)/L) = 1.
Proof.
  intros a b L t g HL Hab Htg.
  replace (((a*t-b*g)/L)*((a*t-b*g)/L)+((b*t+a*g)/L)*((b*t+a*g)/L)) with
    (((a^2+b^2)*(t^2+g^2))/(L*L)) by (field; exact HL).
  rewrite Hab,Htg; field; exact HL.
Qed.

Theorem trace_phase_special_orthogonal : forall side t,
  -2 <= t <= 2 -> det2 (trace_phase side t) = 1 /\ orthogonal2 (trace_phase side t).
Proof.
  intros side t Ht. pose proof phase_amplitude_gt_two as HK.
  pose proof (pow2_sqrt (phase_amplitude^2-t^2) ltac:(nra)) as Hgap.
  fold (trace_phase_gap t) in Hgap.
  unfold trace_phase; apply circle_matrix_special_orthogonal.
  apply phase_coordinates_circle; [nra|symmetry; exact phase_amplitude_coefficients|].
  destruct side; nra.
Qed.

Lemma phase_limit_original_conjugacy : forall S,
  phase_limit_original S =
    mul2 (mul2 constant_basis (mul2 S rotation_defect)) (adj2 constant_basis).
Proof.
  intro S; unfold phase_limit_original,rotation_defect. rewrite !mul2_assoc.
  rewrite (unimodular_right_inverse constant_basis constant_basis_unimodular),mul2_id_right; reflexivity.
Qed.
Lemma phase_limit_original_trace : forall S,
  trace2 (phase_limit_original S) = trace2 (mul2 S rotation_defect).
Proof.
  intro S. rewrite phase_limit_original_conjugacy.
  rewrite <- (adj2_involutive constant_basis) at 1.
  apply trace_conjugation. rewrite adjugate_determinant; exact constant_basis_unimodular.
Qed.
Theorem trace_phase_trace : forall side t,
  trace2 (phase_limit_original (trace_phase side t)) = t.
Proof.
  intros side t. rewrite phase_limit_original_trace. unfold trace_phase.
  rewrite circle_matrix_trace.
  pose proof phase_amplitude_coefficients as Hab; pose proof phase_amplitude_gt_two as HK.
  pose proof (f_equal (fun x => x*t) Hab) as Hscaled.
  destruct side; apply (Rmult_eq_reg_r (phase_amplitude^2)); [|nra| |nra];
    field_simplify; nra.
Qed.

Lemma independent_phase_endpoints :
  let P := trace_phase true 2 in let Q := trace_phase false 2 in
  a11 P*a21 Q-a21 P*a11 Q <> 0.
Proof.
  cbn zeta. pose proof phase_amplitude_gt_two as HK.
  pose proof phase_amplitude_coefficients as Hab.
  assert (Hg : 0 < trace_phase_gap 2) by (unfold trace_phase_gap; apply sqrt_lt_R0; nra).
  assert (Hcross : a11 (trace_phase true 2)*a21 (trace_phase false 2)-
    a21 (trace_phase true 2)*a11 (trace_phase false 2) = -4*trace_phase_gap 2/(phase_amplitude^2)).
  { set (a := trace2 rotation_defect). set (b := a12 rotation_defect-a21 rotation_defect).
    set (L := phase_amplitude^2). set (g := trace_phase_gap 2).
    fold a b L in Hab.
    assert (HL : L <> 0) by (unfold L; nra).
    unfold trace_phase.
    change (((a*2-b*g)/L)*((b*2+a*(-g))/L)-
      ((b*2+a*g)/L)*((a*2-b*(-g))/L) = -4*g/L).
    replace (((a*2-b*g)/L)*((b*2+a*(-g))/L)-
      ((b*2+a*g)/L)*((a*2-b*(-g))/L)) with
      (-4*g*(a^2+b^2)/(L^2)) by (field; exact HL).
    rewrite <- Hab; field; exact HL. }
  rewrite Hcross. intro Hz. apply (f_equal (fun x => x*phase_amplitude^2)) in Hz.
  field_simplify in Hz; nra.
Qed.

Lemma independent_phases_have_nonzero_entry : forall G D c s a b,
  det2 G = 1 -> a21 G = 0 -> det2 D = 1 -> c*b-s*a <> 0 ->
  a21 (mul2 (mul2 (mul2 G (circle_matrix c s)) (adj2 G)) D) <> 0 \/
  a21 (mul2 (mul2 (mul2 G (circle_matrix a b)) (adj2 G)) D) <> 0.
Proof.
  intros G D c s a b HG Htri HD Hind.
  set (V := mul2 (adj2 G) D).
  assert (HV : det2 V = 1) by (unfold V; rewrite det2_mul,adjugate_determinant,HG,HD; ring).
  assert (Hg22 : a22 G <> 0) by (unfold det2 in HG; rewrite Htri in HG; nra).
  rewrite !mul2_assoc. fold V.
  destruct (Req_dec (a21 (mul2 G (mul2 (circle_matrix c s) V))) 0) as [H1|H1]; [right|auto].
  intro H2.
  assert (Hlin1 : s*a11 V+c*a21 V = 0).
  { assert (Hfactor : a22 G*(s*a11 V+c*a21 V) = 0).
    { change (a21 G*(c*a11 V+(-s)*a21 V)+a22 G*(s*a11 V+c*a21 V) = 0) in H1.
      rewrite Htri in H1; nra. }
    apply Rmult_integral in Hfactor; tauto. }
  assert (Hlin2 : b*a11 V+a*a21 V = 0).
  { assert (Hfactor : a22 G*(b*a11 V+a*a21 V) = 0).
    { change (a21 G*(a*a11 V+(-b)*a21 V)+a22 G*(b*a11 V+a*a21 V) = 0) in H2.
      rewrite Htri in H2; nra. }
    apply Rmult_integral in Hfactor; tauto. }
  assert (Hcol1 : (c*b-s*a)*a11 V = 0).
  { pose proof (f_equal (fun x => x*a) Hlin1); pose proof (f_equal (fun x => x*c) Hlin2); nra. }
  assert (Hcol2 : (c*b-s*a)*a21 V = 0).
  { pose proof (f_equal (fun x => x*b) Hlin1); pose proof (f_equal (fun x => x*s) Hlin2); nra. }
  apply Rmult_integral in Hcol1,Hcol2.
  assert (Ha : a11 V = 0) by tauto. assert (Hc : a21 V = 0) by tauto.
  unfold det2 in HV; rewrite Ha,Hc in HV; nra.
Qed.

Theorem one_parabolic_endpoint_nonzero :
  a21 (phase_limit_original (trace_phase true 2)) <> 0 \/
  a21 (phase_limit_original (trace_phase false 2)) <> 0.
Proof.
  pose proof independent_phase_endpoints as Hind.
  pose proof (trace_phase_special_orthogonal true 2 ltac:(lra)) as Htrue.
  pose proof (trace_phase_special_orthogonal false 2 ltac:(lra)) as Hfalse.
  unfold phase_limit_original.
  apply independent_phases_have_nonzero_entry; try exact constant_basis_unimodular;
    try exact defect_limit_unimodular; [reflexivity|exact Hind].
Qed.

Definition parabolic_branch :=
  if Req_EM_T (a21 (phase_limit_original (trace_phase true 2))) 0 then false else true.
Lemma parabolic_branch_endpoint_nonzero :
  a21 (phase_limit_original (trace_phase parabolic_branch 2)) <> 0.
Proof.
  unfold parabolic_branch; destruct (Req_EM_T (a21 (phase_limit_original (trace_phase true 2))) 0);
    pose proof one_parabolic_endpoint_nonzero; tauto.
Qed.
Definition parabolic_orientation :=
  if Rlt_dec 0 (a21 (phase_limit_original (trace_phase parabolic_branch 2))) then true else false.
Definition parabolic_phase t :=
  if parabolic_orientation then trace_phase parabolic_branch t else scale2 (-1) (trace_phase parabolic_branch t).

Lemma phase_limit_original_negative : forall S,
  phase_limit_original (scale2 (-1) S) = scale2 (-1) (phase_limit_original S).
Proof.
  intro S; apply mat2_ext; unfold phase_limit_original,mul2,scale2; simpl; ring.
Qed.
Lemma negative_special_orthogonal : forall A,
  det2 A = 1 -> orthogonal2 A -> det2 (scale2 (-1) A) = 1 /\ orthogonal2 (scale2 (-1) A).
Proof.
  intros A HA Ho.
  assert (Hnegative : scale2 (-1) A = mul2 (circle_matrix (-1) 0) A) by
    (apply mat2_ext; unfold scale2,mul2,circle_matrix; simpl; ring).
  destruct (circle_matrix_special_orthogonal (-1) 0 ltac:(nra)) as [Hd Horth].
  rewrite Hnegative; split; [rewrite det2_mul,Hd,HA; ring|apply orthogonal_product; assumption].
Qed.
Theorem parabolic_phase_special_orthogonal : forall t,
  -2 <= t <= 2 -> det2 (parabolic_phase t) = 1 /\ orthogonal2 (parabolic_phase t).
Proof.
  intros t Ht; unfold parabolic_phase; destruct parabolic_orientation.
  - apply trace_phase_special_orthogonal; exact Ht.
  - apply negative_special_orthogonal; exact (proj1 (trace_phase_special_orthogonal _ _ Ht)) ||
      exact (proj2 (trace_phase_special_orthogonal _ _ Ht)).
Qed.
Lemma trace2_scale : forall r A, trace2 (scale2 r A) = r*trace2 A.
Proof. intros r []; unfold trace2,scale2; simpl; ring. Qed.
Theorem parabolic_phase_trace : forall t,
  trace2 (phase_limit_original (parabolic_phase t)) = if parabolic_orientation then t else -t.
Proof.
  intro t; unfold parabolic_phase; destruct parabolic_orientation; [apply trace_phase_trace|].
  rewrite phase_limit_original_negative,trace2_scale,trace_phase_trace; ring.
Qed.
Theorem parabolic_endpoint_positive : 0 < a21 (phase_limit_original (parabolic_phase 2)).
Proof.
  unfold parabolic_phase,parabolic_orientation.
  destruct (Rlt_dec 0 (a21 (phase_limit_original (trace_phase parabolic_branch 2)))) as [Hpos|Hneg]; [exact Hpos|].
  rewrite phase_limit_original_negative.
  change (0 < (-1)*a21 (phase_limit_original (trace_phase parabolic_branch 2))).
  pose proof parabolic_branch_endpoint_nonzero; lra.
Qed.
Lemma phase_limit_original_unimodular : forall S,
  det2 S = 1 -> det2 (phase_limit_original S) = 1.
Proof.
  intros S HS; unfold phase_limit_original; rewrite !det2_mul,adjugate_determinant,
    constant_basis_unimodular,defect_limit_unimodular,HS; ring.
Qed.

From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  DefectLimit EllipticConjugacy.
Open Scope R_scope.

Definition circle_matrix (c s : R) := Mat2 c (-s) s c.
Lemma circle_matrix_special_orthogonal : forall c s,
  c*c+s*s = 1 -> det2 (circle_matrix c s) = 1 /\ orthogonal2 (circle_matrix c s).
Proof.
  intros c s H. split.
  - unfold det2, circle_matrix; simpl; nra.
  - unfold orthogonal2; apply mat2_ext;
      unfold mul2, transpose2, circle_matrix, id2; simpl; nra.
Qed.

Lemma circle_matrix_trace : forall c s B,
  trace2 (mul2 (circle_matrix c s) B) = trace2 B*c+(a12 B-a21 B)*s.
Proof. intros c s []; unfold trace2, mul2, circle_matrix; simpl; ring. Qed.

Definition phase_amplitude := sqrt (amplitude_squared rotation_defect).
Lemma phase_amplitude_square : phase_amplitude*phase_amplitude = amplitude_squared rotation_defect.
Proof. apply sqrt_sqrt. pose proof defect_trace_amplitude; lra. Qed.
Theorem phase_amplitude_gt_two : 2 < phase_amplitude.
Proof.
  pose proof phase_amplitude_square. pose proof defect_trace_amplitude.
  pose proof (sqrt_pos (amplitude_squared rotation_defect)).
  change (0 <= phase_amplitude) in H1. nra.
Qed.

Definition zero_trace_phase := circle_matrix
  ((a12 rotation_defect-a21 rotation_defect)/phase_amplitude)
  (-trace2 rotation_defect/phase_amplitude).
Definition maximum_trace_phase := circle_matrix
  (trace2 rotation_defect/phase_amplitude)
  ((a12 rotation_defect-a21 rotation_defect)/phase_amplitude).

Theorem zero_trace_phase_special_orthogonal :
  det2 zero_trace_phase = 1 /\ orthogonal2 zero_trace_phase.
Proof.
  unfold zero_trace_phase. apply circle_matrix_special_orthogonal.
  pose proof phase_amplitude_square as Hsq. pose proof phase_amplitude_gt_two.
  unfold amplitude_squared in Hsq. fold (trace2 rotation_defect) in Hsq.
  apply (Rmult_eq_reg_r (phase_amplitude*phase_amplitude)); [|nra].
  field_simplify; nra.
Qed.

Theorem zero_trace_phase_elliptic : Rabs (trace2 (mul2 zero_trace_phase rotation_defect)) < 2.
Proof.
  unfold zero_trace_phase. rewrite circle_matrix_trace.
  pose proof phase_amplitude_gt_two.
  replace (trace2 rotation_defect*((a12 rotation_defect-a21 rotation_defect)/phase_amplitude)+
    (a12 rotation_defect-a21 rotation_defect)*(-trace2 rotation_defect/phase_amplitude))
    with 0 by (field; lra).
  rewrite Rabs_R0. lra.
Qed.

Theorem maximum_trace_phase_special_orthogonal :
  det2 maximum_trace_phase = 1 /\ orthogonal2 maximum_trace_phase.
Proof.
  unfold maximum_trace_phase. apply circle_matrix_special_orthogonal.
  pose proof phase_amplitude_square as Hsq. pose proof phase_amplitude_gt_two.
  unfold amplitude_squared in Hsq. fold (trace2 rotation_defect) in Hsq.
  apply (Rmult_eq_reg_r (phase_amplitude*phase_amplitude)); [|nra].
  field_simplify; nra.
Qed.

Theorem maximum_trace_phase_hyperbolic : 2 < trace2 (mul2 maximum_trace_phase rotation_defect).
Proof.
  unfold maximum_trace_phase. rewrite circle_matrix_trace.
  pose proof phase_amplitude_gt_two as HK.
  pose proof phase_amplitude_square as Hsq.
  unfold amplitude_squared in Hsq. fold (trace2 rotation_defect) in Hsq.
  assert (Hmax : trace2 rotation_defect*(trace2 rotation_defect/phase_amplitude)+
    (a12 rotation_defect-a21 rotation_defect)*((a12 rotation_defect-a21 rotation_defect)/phase_amplitude) =
    phase_amplitude).
  { apply (Rmult_eq_reg_r phase_amplitude); [|lra]. field_simplify; nra. }
  rewrite Hmax. exact HK.
Qed.

Lemma trace_operator_bound : forall A, Rabs (trace2 A) <= 2*opnorm A.
Proof.
  intro A. pose proof (opnorm_entries A).
  unfold trace2. pose proof (Rabs_triang (a11 A) (a22 A)). lra.
Qed.
Lemma trace_subtraction : forall A B, trace2 (sub2 A B) = trace2 A-trace2 B.
Proof. intros [] []; unfold trace2, sub2, add2, scale2; simpl; ring. Qed.
Lemma multiplication_subtraction_left : forall A B C,
  sub2 (mul2 A C) (mul2 B C) = mul2 (sub2 A B) C.
Proof. intros [] [] []; apply mat2_ext; unfold sub2, add2, scale2, mul2; simpl; ring. Qed.

(* Openness of the elliptic phase condition in the concrete operator metric.
   Restriction to the circle gives an open, nonempty, proper phase set. *)
Theorem elliptic_phase_open : forall R,
  Rabs (trace2 (mul2 R rotation_defect)) < 2 ->
  exists eps, 0 < eps /\ forall S,
    opnorm (sub2 S R) < eps -> Rabs (trace2 (mul2 S rotation_defect)) < 2.
Proof.
  intros R HR.
  set (margin := 2-Rabs (trace2 (mul2 R rotation_defect))).
  set (C := opnorm rotation_defect+1).
  assert (HM : 0 < margin) by (unfold margin; lra).
  assert (HC : 0 < C) by (unfold C; pose proof (opnorm_nonnegative rotation_defect); lra).
  exists (margin/(4*C)). split; [apply Rdiv_lt_0_compat; lra|].
  intros S HS.
  pose proof (trace_operator_bound (sub2 (mul2 S rotation_defect) (mul2 R rotation_defect))) as HT.
  rewrite trace_subtraction, multiplication_subtraction_left in HT.
  pose proof (opnorm_submultiplicative (sub2 S R) rotation_defect) as HP.
  pose proof (opnorm_nonnegative (sub2 S R)) as HN.
  assert (Hsmall : 4*C*opnorm (sub2 S R) < margin).
  { pose proof (Rmult_lt_compat_l (4*C) _ _ ltac:(lra) HS) as HX.
    replace (4*C*(margin/(4*C))) with margin in HX by (field; lra). exact HX. }
  assert (Htrace : Rabs (trace2 (mul2 S rotation_defect)) <=
    Rabs (trace2 (mul2 S rotation_defect)-trace2 (mul2 R rotation_defect))+
    Rabs (trace2 (mul2 R rotation_defect))).
  { replace (trace2 (mul2 S rotation_defect)) with
      ((trace2 (mul2 S rotation_defect)-trace2 (mul2 R rotation_defect))+trace2 (mul2 R rotation_defect)) at 1 by ring.
    apply Rabs_triang. }
  unfold C in Hsmall. unfold margin in *. nra.
Qed.

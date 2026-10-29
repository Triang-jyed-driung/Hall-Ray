From Stdlib Require Import Reals Psatz Lia.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices LatticeBasis
  FiberProducts EuclideanNorm SymbolicCoding SymbolicCocycle DefectLimit ScalarEstimates
  EllipticConjugacy EllipticContinuity NormalizedFlow TwoSidedCoding LatticeReturns
  LimitingWords NormGeometry PaperTarget DaniCorrespondence LatticeSystole
  RoofLimits RotationAlignment ContractingCircle.
Open Scope R_scope.

Lemma planar_norm_enorm_upper : forall nm v,
  length2 nm v <= 2*norm_bound nm*enorm v.
Proof.
  intros nm [x y]. pose proof (planar_norm_upper nm x y).
  destruct (enorm_coordinates x y). pose proof (norm_bound_positive nm); nra.
Qed.

Definition bulk_unstable := u_code constant_word.
Definition bulk_stable := v_code constant_word.
Definition bulk_frame_scale := frame_normalizer
  (chart_weight (fst bulk_unstable) (snd bulk_unstable) (fst bulk_stable) (snd bulk_stable)).

Lemma bulk_input_positive : 0 < enorm (action (adj2 constant_basis) bulk_unstable).
Proof.
  apply enorm_positive_nonzero; intro Hzero.
  apply (f_equal (action constant_basis)) in Hzero.
  rewrite (unimodular_action_inverse constant_basis bulk_unstable constant_basis_unimodular),
    action_zero in Hzero.
  pose proof (f_equal snd Hzero) as Hsnd; simpl in Hsnd.
  apply (unstable_code_second_nonzero constant_word); exact Hsnd.
Qed.

Definition bulk_contraction_bound nm X :=
  2*norm_bound nm*(opnorm X+1)*(opnorm constant_basis+1)*
    (enorm (action (adj2 constant_basis) bulk_unstable)+1).

Lemma bulk_contraction_bound_positive : forall nm X, 0 < bulk_contraction_bound nm X.
Proof.
  intros nm X; unfold bulk_contraction_bound.
  pose proof (norm_bound_positive nm); pose proof (opnorm_nonnegative X);
    pose proof (opnorm_nonnegative constant_basis);
    pose proof (enorm_nonnegative (action (adj2 constant_basis) bulk_unstable)).
  repeat apply Rmult_lt_0_compat; lra.
Qed.

Theorem bulk_fiber_small_vector : forall nm X A,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> 0 < a21 A ->
  exists E R, in_elliptic_circle A E /\ det2 R = 1 /\ orthogonal2 R /\
    length2 nm (action (mul2 (mul2 X E) (mul2 (mul2 constant_basis R) (adj2 constant_basis))) bulk_unstable) <=
      bulk_contraction_bound nm X*(elliptic_scale A)^2.
Proof.
  intros nm X A HA Hell Hc.
  destruct (elliptic_circle_contracts_after_rotation A constant_basis bulk_unstable
    HA Hell Hc constant_basis_unimodular bulk_input_positive) as [E [R [HE [HRd [HRo Hcontract]]]]].
  exists E,R; split; [exact HE|]. split; [exact HRd|]. split; [exact HRo|].
  rewrite mul2_assoc,action_product.
  eapply Rle_trans; [apply planar_norm_enorm_upper|].
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [pose proof (norm_bound_positive nm); lra|apply opnorm_action_bound].
  - eapply Rle_trans.
    + apply Rmult_le_compat_l; [pose proof (norm_bound_positive nm); lra|].
      apply Rmult_le_compat_l; [apply opnorm_nonnegative|exact Hcontract].
    + assert (Hb : opnorm X*opnorm constant_basis*enorm (action (adj2 constant_basis) bulk_unstable) <=
        (opnorm X+1)*(opnorm constant_basis+1)*(enorm (action (adj2 constant_basis) bulk_unstable)+1)).
      { apply Rmult_le_compat.
        - apply Rmult_le_pos; apply opnorm_nonnegative.
        - apply enorm_nonnegative.
        - apply Rmult_le_compat; pose proof (opnorm_nonnegative X); pose proof (opnorm_nonnegative constant_basis); lra.
        - lra. }
      replace (2*norm_bound nm*(opnorm X*(opnorm constant_basis*
        enorm (action (adj2 constant_basis) bulk_unstable)*(elliptic_scale A)^2))) with
        ((2*norm_bound nm*(opnorm X*opnorm constant_basis*
          enorm (action (adj2 constant_basis) bulk_unstable)))*(elliptic_scale A)^2) by ring.
      unfold bulk_contraction_bound.
      apply Rmult_le_compat_r; [apply pow2_ge_0|].
      replace (2*norm_bound nm*(opnorm X+1)*(opnorm constant_basis+1)*
        (enorm (action (adj2 constant_basis) bulk_unstable)+1)) with
        ((2*norm_bound nm)*((opnorm X+1)*(opnorm constant_basis+1)*
          (enorm (action (adj2 constant_basis) bulk_unstable)+1))) by ring.
      apply Rmult_le_compat_l; [pose proof (norm_bound_positive nm); lra|exact Hb].
Qed.

Lemma normalized_first_vector_length : forall nm u v E r,
  0 < r ->
  length3 nm (action3 (mul3 (flow_scale r)
    (normalized_frame (fst u) (snd u) (fst v) (snd v) E)) (real_vector (ZVec3 1 0 0))) =
  frame_normalizer (chart_weight (fst u) (snd u) (fst v) (snd v))*
    vector_length 1 (length2 nm (action E u)) r.
Proof.
  intros nm [x y] [a b] E r Hr.
  set (c := frame_normalizer (chart_weight x y a b)).
  assert (Hc : 0 < c) by apply frame_normalizer_positive.
  assert (Hvec : action3 (mul3 (flow_scale r) (normalized_frame x y a b E))
    (real_vector (ZVec3 1 0 0)) =
    Vec3 (c/(r*r)) ((-c*r)*fst (action E (x,y))) ((-c*r)*snd (action E (x,y)))).
  { apply vec3_ext; unfold action3,mul3,flow_scale,normalized_frame,chart,scale3,block3,raw_chart,real_vector,action;
      simpl; fold c; field; lra. }
  simpl fst; simpl snd. rewrite Hvec. unfold length3; simpl v1; simpl v2; simpl v3.
  change (Rmax (Rabs (c/(r*r))) (length2 nm (vscale (-c*r) (action E (x,y)))) =
    c*vector_length 1 (length2 nm (action E (x,y))) r).
  rewrite length2_homogeneous,(Rabs_left (-c*r)) by nra.
  rewrite (Rabs_right (c/(r*r))) by
    (apply Rle_ge,Rlt_le,Rdiv_lt_0_compat; nra).
  unfold vector_length.
  replace (c/(r*r)) with (c*(1/(r*r))) by (field; lra).
  replace (-(-c*r)*length2 nm (action E (x,y))) with (c*(r*length2 nm (action E (x,y)))) by ring.
  rewrite RmaxRmult by lra. reflexivity.
Qed.

Theorem normalized_first_vector_systole_bound : forall nm u v E r,
  0 < r ->
  systole nm (mul3 (flow_scale r) (normalized_frame (fst u) (snd u) (fst v) (snd v) E)) <=
  frame_normalizer (chart_weight (fst u) (snd u) (fst v) (snd v))*
    vector_length 1 (length2 nm (action E u)) r.
Proof.
  intros nm u v E r Hr. rewrite <- normalized_first_vector_length by exact Hr.
  apply systole_lower_bound. unfold zzero3; discriminate.
Qed.

Lemma square_root_balancing_bound : forall p d D,
  0 < p <= 1 -> 0 <= D -> 0 <= d -> d <= D*p^2 ->
  vector_length 1 d (/sqrt p) <= (D+1)*p.
Proof.
  intros p d D Hp HD Hd Hbound.
  pose proof (sqrt_lt_R0 p ltac:(lra)) as Hroot.
  pose proof (pow2_sqrt p ltac:(lra)) as Hsquare.
  assert (Hinv : 1/((/sqrt p)*(/sqrt p)) = p).
  { field_simplify; nra. }
  unfold vector_length; rewrite Hinv. apply Rmax_lub; [nra|].
  apply (Rmult_le_reg_r (sqrt p)); [exact Hroot|].
  replace ((/sqrt p*d)*sqrt p) with d by (field; lra).
  assert (Hsmall : p <= sqrt p) by nra.
  assert (Hmul : D*p^2 <= (D+1)*p*sqrt p) by nra. lra.
Qed.

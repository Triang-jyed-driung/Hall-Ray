From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  DefectLimit DefectPhases EllipticConjugacy EllipticRecurrence EllipticContinuity RotationAlignment.
Open Scope R_scope.

Definition triangular_basis p q := Mat2 p q 0 (/p).
Definition quarter_turn := circle_matrix 0 1.
Definition triangular_quarter p q :=
  mul2 (mul2 (triangular_basis p q) quarter_turn) (adj2 (triangular_basis p q)).

Lemma quarter_turn_special_orthogonal : det2 quarter_turn = 1 /\ orthogonal2 quarter_turn.
Proof. apply circle_matrix_special_orthogonal; nra. Qed.
Lemma triangular_quarter_column : forall p q,
  0 < p -> action (triangular_quarter p q) (q,/p) = (-p,0).
Proof.
  intros p q Hp. unfold triangular_quarter,triangular_basis,quarter_turn,circle_matrix,mul2,adj2,action;
    simpl; f_equal; field; lra.
Qed.
Lemma unimodular_action_inverse : forall H v,
  det2 H = 1 -> action H (action (adj2 H) v) = v.
Proof.
  intros H v HH. rewrite <- action_product,(unimodular_right_inverse H HH),action_identity; reflexivity.
Qed.

Theorem triangular_circle_contraction : forall H u p q,
  det2 H = 1 -> 0 < enorm (action (adj2 H) u) -> 0 < p ->
  exists R, det2 R = 1 /\ orthogonal2 R /\
    enorm (action (mul2 (triangular_quarter p q) (mul2 (mul2 H R) (adj2 H))) u) <=
      opnorm H*enorm (action (adj2 H) u)*p^2.
Proof.
  intros H u p q HH Hu Hp.
  set (v := action (adj2 H) u).
  fold v in Hu.
  set (w := action (adj2 H) (q,/p)).
  assert (Hlower : /p <= opnorm H*enorm w).
  { pose proof (opnorm_action_bound H w) as Haction.
    unfold w in Haction. rewrite (unimodular_action_inverse H (q,/p) HH) in Haction. fold w in Haction.
    pose proof (proj2 (enorm_coordinates q (/p))) as Hcoord.
    rewrite Rabs_right in Hcoord by (apply Rle_ge,Rlt_le,Rinv_0_lt_compat; exact Hp). lra. }
  assert (Hw : 0 < enorm w).
  { pose proof (enorm_nonnegative w); pose proof (opnorm_nonnegative H).
    pose proof (Rinv_0_lt_compat p Hp); nra. }
  destruct (rotation_aligns_vectors v w Hu Hw) as [R [HRd [HRo HR]]].
  exists R; split; [exact HRd|]. split; [exact HRo|].
  assert (Himage : action (mul2 (triangular_quarter p q) (mul2 (mul2 H R) (adj2 H))) u =
    evscale (enorm v/enorm w) (-p,0)).
  { rewrite !action_product. fold v. rewrite HR,action_vector_scale.
    unfold w; rewrite (unimodular_action_inverse H (q,/p) HH),action_vector_scale,triangular_quarter_column by exact Hp.
    reflexivity. }
  rewrite Himage,enorm_scale.
  assert (Hnp : enorm (-p,0) = p).
  { replace (-p,0) with (evscale (-p) (1,0)) by (unfold evscale; simpl; f_equal; ring).
    rewrite enorm_scale,enorm_unit,Rabs_left by lra; ring. }
  rewrite Hnp,Rabs_right by (apply Rle_ge,Rlt_le,Rdiv_lt_0_compat; assumption).
  apply (Rmult_le_reg_r (enorm w)); [exact Hw|].
  replace (enorm v/enorm w*p*enorm w) with (enorm v*p) by (field; lra).
  assert (Hscaled : 1 <= p*opnorm H*enorm w).
  { apply (Rmult_le_compat_l p) in Hlower; [|lra].
    replace (p* /p) with 1 in Hlower by (field; lra). nra. }
  assert (Hprod : enorm v*p <= (enorm v*p)*(p*opnorm H*enorm w)).
  { replace (enorm v*p) with ((enorm v*p)*1) at 1 by ring.
    apply Rmult_le_compat_l; [nra|exact Hscaled]. }
  change (enorm v*p <= opnorm H*enorm v*p^2*enorm w). nra.
Qed.

Theorem elliptic_circle_contracts_after_rotation : forall A H u,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> 0 < a21 A ->
  det2 H = 1 -> 0 < enorm (action (adj2 H) u) ->
  exists E R, in_elliptic_circle A E /\ det2 R = 1 /\ orthogonal2 R /\
    enorm (action (mul2 E (mul2 (mul2 H R) (adj2 H))) u) <=
      opnorm H*enorm (action (adj2 H) u)*(elliptic_scale A)^2.
Proof.
  intros A H u HA Hell Hc HH Hu.
  pose proof (elliptic_scale_positive A Hell Hc) as Hp.
  destruct (triangular_circle_contraction H u (elliptic_scale A)
    (elliptic_scale A*(a11 A-elliptic_cosine A)/elliptic_sine A) HH Hu Hp)
    as [R [HRd [HRo Hbound]]].
  exists (elliptic_circle A quarter_turn), R. split.
  - exists quarter_turn; split; [exact (proj1 quarter_turn_special_orthogonal)|].
    split; [exact (proj2 quarter_turn_special_orthogonal)|reflexivity].
  - split; [exact HRd|]. split; [exact HRo|].
    assert (Hbasis : oriented_elliptic_basis A = elliptic_basis A).
    { unfold oriented_elliptic_basis; destruct (Rlt_dec 0 (a21 A)); [reflexivity|lra]. }
    unfold elliptic_circle. rewrite Hbasis. exact Hbound.
Qed.

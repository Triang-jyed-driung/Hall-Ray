From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra ReturnBranches ScalarEstimates.
Open Scope R_scope.

Definition constant_matrix (alpha : R) :=
  scale2 (/sqrt alpha)
    (Mat2 (10-1/alpha) (-1+10/alpha-1/alpha^2) 1 10).

Lemma constant_matrix_is_cocycle : forall alpha,
  100 < alpha -> cubic alpha = 0 ->
  constant_matrix alpha = normalized_a (fixed_u1 alpha) (fixed_u2 alpha).
Proof.
  intros alpha Ha Hf. unfold constant_matrix, normalized_a.
  change (scale2 (/sqrt alpha)
      (Mat2 (10-1/alpha) (-1+10/alpha-1/alpha^2) 1 10) =
    scale2 (/sqrt (da (fixed_u1 alpha) (fixed_u2 alpha)))
      (numerator_a (fixed_u1 alpha) (fixed_u2 alpha))).
  rewrite (fixed_point_denominator alpha Ha Hf). f_equal.
  apply mat2_ext; unfold numerator_a, fixed_u1, fixed_u2; simpl; ring.
Qed.

Theorem constant_return_unimodular : forall alpha,
  100 < alpha -> cubic alpha = 0 -> det2 (constant_matrix alpha) = 1.
Proof.
  intros alpha Ha Hf. rewrite (constant_matrix_is_cocycle alpha Ha Hf).
  apply normalized_a_unimodular.
  change (0 < da (fixed_u1 alpha) (fixed_u2 alpha)).
  rewrite (fixed_point_denominator alpha Ha Hf). lra.
Qed.

Theorem constant_return_elliptic : forall alpha,
  100 < alpha -> Rabs (trace2 (constant_matrix alpha)) < 2.
Proof.
  intros alpha Ha.
  pose proof (sqrt_pos alpha) as Hsnonneg.
  pose proof (Rsqr_sqrt alpha ltac:(lra)) as Hsquare. unfold Rsqr in Hsquare.
  assert (Hs : 10 < sqrt alpha) by nra.
  assert (Hinv : 0 < /alpha) by (apply Rinv_0_lt_compat; lra).
  assert (Hinvbound : /alpha < 1/100).
  { apply (Rmult_lt_reg_r alpha); [lra|].
    replace (/alpha*alpha) with 1 by (field; lra). nra. }
  assert (Htr : trace2 (constant_matrix alpha) = (20- /alpha)/sqrt alpha).
  { unfold trace2, constant_matrix, scale2; simpl; field; lra. }
  rewrite Htr, Rabs_right.
  - apply (Rmult_lt_reg_r (sqrt alpha)); [lra|].
    replace ((20- /alpha)/sqrt alpha*sqrt alpha) with (20- /alpha) by (field; lra).
    lra.
  - apply Rle_ge, Rlt_le, Rdiv_lt_0_compat; lra.
Qed.

Theorem constant_elliptic_return_exists : exists alpha,
  100 < alpha < 101 /\ cubic alpha = 0 /\
  det2 (constant_matrix alpha) = 1 /\
  Rabs (trace2 (constant_matrix alpha)) < 2.
Proof.
  destruct constant_root_exists as [alpha [Ha Hf]]. exists alpha.
  repeat split; try tauto.
  - apply constant_return_unimodular; tauto.
  - apply constant_return_elliptic; tauto.
Qed.

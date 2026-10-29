From Stdlib Require Import Reals Psatz Lia Arith List.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits ConcreteCocycle
  SymbolicCoding SymbolicCocycle DefectLimit PeriodicReturns WordPrefixes.
Open Scope R_scope.
Import ListNotations.

Definition stage_future xs n := prepend_word xs (periodic_future n).
Definition stage_fiber xs n := fiber_product (length xs) (stage_future xs n).

Lemma appended_stage_future : forall xs n L,
  stage_future (xs++repeated_return_word n L) n = stage_future xs n.
Proof.
  intros xs n L; unfold stage_future. rewrite prepend_word_append,prepend_repeated_periodic; reflexivity.
Qed.
Theorem appended_stage_fiber : forall xs n L,
  stage_fiber (xs++repeated_return_word n L) n =
    mul2 (fiber_product (length xs) (stage_future xs n)) (matrix_power (periodic_return n) L).
Proof.
  intros xs n L; unfold stage_fiber at 1.
  rewrite appended_stage_future,length_app,repeated_return_length,fiber_product_concatenation.
  unfold stage_future. rewrite prepend_word_shift,periodic_cycle_products; reflexivity.
Qed.
Lemma stage_fiber_unimodular : forall xs n, det2 (stage_fiber xs n) = 1.
Proof. intros xs n; apply factor_product_unimodular. Qed.

Theorem stage_prefix_fiber_comparison : forall xs n m,
  (n <= m)%nat ->
  opnorm (sub2 (fiber_product (length xs) (stage_future xs m)) (stage_fiber xs n)) <=
    opnorm (stage_fiber xs n)*(1/600)^n.
Proof.
  intros xs n m Hnm; apply symbolic_relative_absolute_bound.
  intros k Hk; symmetry; apply (prepend_growing_periodic_common xs n m Hnm k Hk).
Qed.
Theorem appended_stage_fiber_error : forall xs n m L,
  (n <= m)%nat ->
  opnorm (sub2 (stage_fiber (xs++repeated_return_word m L) m)
    (mul2 (stage_fiber xs n) (matrix_power (periodic_return m) L))) <=
    opnorm (stage_fiber xs n)*opnorm (matrix_power (periodic_return m) L)*(1/600)^n.
Proof.
  intros xs n m L Hnm; rewrite appended_stage_fiber, <- matrix_multiply_difference_left.
  eapply Rle_trans; [apply opnorm_submultiplicative|].
  replace (opnorm (stage_fiber xs n)*opnorm (matrix_power (periodic_return m) L)*(1/600)^n) with
    ((opnorm (stage_fiber xs n)*(1/600)^n)*opnorm (matrix_power (periodic_return m) L)) by ring.
  apply Rmult_le_compat_r; [apply opnorm_nonnegative|apply stage_prefix_fiber_comparison; exact Hnm].
Qed.
Lemma empty_stage_fiber : forall n, stage_fiber [] n = id2.
Proof. reflexivity. Qed.
Lemma first_stage_fiber : forall n L,
  stage_fiber (repeated_return_word n L) n = matrix_power (periodic_return n) L.
Proof.
  intros n L; replace (repeated_return_word n L) with ([]++repeated_return_word n L) by reflexivity.
  rewrite appended_stage_fiber; simpl; apply mul2_id_left.
Qed.

Lemma matrix_near_identity_norm : forall A,
  opnorm A <= 1+opnorm (sub2 A id2).
Proof.
  intro A. pose proof (opnorm_subadditive (sub2 A id2) id2) as H.
  rewrite opnorm_identity in H. rewrite <- matrix_difference_decomposition in H; lra.
Qed.
Lemma matrix_drift_step : forall F G E,
  opnorm (sub2 F id2) <= opnorm (sub2 F (mul2 G E))+
    opnorm G*opnorm (sub2 E id2)+opnorm (sub2 G id2).
Proof.
  intros F G E.
  pose proof (opnorm_difference_triangle F (mul2 G E) id2) as H1.
  pose proof (opnorm_difference_triangle (mul2 G E) G id2) as H2.
  assert (Hfactor : sub2 (mul2 G E) G = mul2 G (sub2 E id2)).
  { rewrite matrix_multiply_difference_right,mul2_id_right; reflexivity. }
  rewrite Hfactor in H2.
  pose proof (opnorm_submultiplicative G (sub2 E id2)); lra.
Qed.

Definition fiber_budget delta i := delta*(1-(1/2)^i).
Lemma fiber_budget_zero : forall delta, fiber_budget delta 0 = 0.
Proof. intro delta; unfold fiber_budget; simpl; ring. Qed.
Lemma fiber_budget_step : forall delta i,
  fiber_budget delta (S i) = fiber_budget delta i+delta*(1/2)^(S i).
Proof. intros; unfold fiber_budget; simpl; field. Qed.
Lemma fiber_budget_within : forall delta i,
  0 < delta -> 0 <= fiber_budget delta i < delta.
Proof.
  intros delta i Hd; unfold fiber_budget.
  pose proof (pow_lt (1/2) i ltac:(lra)); pose proof (pow_incr (1/2) 1 i ltac:(lra)); rewrite pow1 in H0; nra.
Qed.

Theorem appended_stage_budget_step : forall delta i xs n m L,
  0 < delta < 1 -> (n <= m)%nat ->
  opnorm (sub2 (stage_fiber xs n) id2) <= fiber_budget delta i ->
  opnorm (sub2 (matrix_power (periodic_return m) L) id2) <= delta*(1/2)^(i+3) ->
  (xs=[] \/ 4*(1/600)^n <= delta*(1/2)^(i+2)) ->
  opnorm (sub2 (stage_fiber (xs++repeated_return_word m L) m) id2) <= fiber_budget delta (S i).
Proof.
  intros delta i xs n m L Hd Hnm Hbudget Hterminal Hguard.
  assert (Hpow : (1/2)^i <= 1) by (pose proof (pow_incr (1/2) 1 i ltac:(lra)); rewrite pow1 in H; exact H).
  assert (Hgi : opnorm (stage_fiber xs n) <= 2).
  { pose proof (matrix_near_identity_norm (stage_fiber xs n)); pose proof (fiber_budget_within delta i ltac:(lra)); lra. }
  assert (He : opnorm (matrix_power (periodic_return m) L) <= 2).
  { pose proof (matrix_near_identity_norm (matrix_power (periodic_return m) L)).
    replace ((1/2)^(i+3)) with ((1/2)^i*(1/8)) in Hterminal by (rewrite pow_add; simpl; field). nra. }
  assert (Herror : opnorm (sub2 (stage_fiber (xs++repeated_return_word m L) m)
    (mul2 (stage_fiber xs n) (matrix_power (periodic_return m) L))) <= delta*(1/2)^(i+2)).
  { destruct Hguard as [Hzero|Hsmall].
    - subst xs; rewrite empty_stage_fiber,mul2_id_left; change
        (opnorm (sub2 (stage_fiber (repeated_return_word m L) m) (matrix_power (periodic_return m) L)) <= delta*(1/2)^(i+2)).
      rewrite first_stage_fiber. replace (sub2 (matrix_power (periodic_return m) L) (matrix_power (periodic_return m) L)) with zero2 by
        (generalize (matrix_power (periodic_return m) L); intros []; apply mat2_ext; unfold sub2,add2,scale2,zero2; simpl; ring).
      rewrite opnorm_zero; apply Rmult_le_pos; [lra|apply pow_le; lra].
    - eapply Rle_trans; [apply appended_stage_fiber_error; exact Hnm|].
      assert (Hfactor : opnorm (stage_fiber xs n)*opnorm (matrix_power (periodic_return m) L) <= 4).
      { pose proof (opnorm_nonnegative (stage_fiber xs n)); pose proof (opnorm_nonnegative (matrix_power (periodic_return m) L)); nra. }
      pose proof (Rmult_le_compat_r ((1/600)^n) _ _ ltac:(apply pow_le; lra) Hfactor); lra. }
  pose proof (matrix_drift_step (stage_fiber (xs++repeated_return_word m L) m) (stage_fiber xs n)
    (matrix_power (periodic_return m) L)) as Hdrift.
  assert (Hscaled : opnorm (stage_fiber xs n)*opnorm (sub2 (matrix_power (periodic_return m) L) id2) <=
    2*(delta*(1/2)^(i+3))).
  { apply Rmult_le_compat; auto using opnorm_nonnegative. }
  rewrite fiber_budget_step.
  replace ((1/2)^(i+2)) with ((1/2)^i*(1/4)) in Herror by (rewrite pow_add; simpl; field).
  replace ((1/2)^(i+3)) with ((1/2)^i*(1/8)) in Hscaled by (rewrite pow_add; simpl; field).
  change (opnorm (sub2 (stage_fiber (xs++repeated_return_word m L) m) id2) <=
    fiber_budget delta i+delta*((1/2)*(1/2)^i)). nra.
Qed.

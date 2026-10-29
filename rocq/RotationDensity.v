From Stdlib Require Import Reals Psatz Lia Arith ClassicalChoice.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  DefectLimit EllipticConjugacy DefectPhases PeriodicReturns EllipticPowers
  ReturnInfiniteOrder RealRotationDensity TrigRotations.
Open Scope R_scope.

Theorem special_orthogonal_powers_dense_late : forall R,
  det2 R = 1 -> orthogonal2 R ->
  (forall n, (0 < n)%nat -> matrix_power R n <> id2) ->
  forall S eps N, det2 S = 1 -> orthogonal2 S -> 0 < eps ->
  exists n, (N <= n)%nat /\ opnorm (sub2 (matrix_power R n) S) < eps.
Proof.
  intros R HRd HRo Hinf S eps N HSd HSo He.
  destruct (special_orthogonal_angle R HRd HRo) as [t HR].
  destruct (special_orthogonal_angle S HSd HSo) as [u HS]. subst R S.
  pose proof (infinite_rotation_number_irrational t Hinf) as Hirr.
  destruct (rotation_continuity u eps He) as [delta [Hd Hcont]].
  pose proof PI_RGT_0 as Hpi.
  destruct (irrational_forward_rotation_dense_late (t/(2*PI)) Hirr (u/(2*PI))
    (delta/(2*PI)) N ltac:(apply Rdiv_lt_0_compat; lra)) as [n [z [Hn Hnear]]].
  assert (Hangle : Rabs ((INR n*t-2*PI*IZR z)-u) < delta).
  { assert (Hid : (INR n*t-2*PI*IZR z)-u =
        (2*PI)*(INR n*(t/(2*PI))-u/(2*PI)-IZR z)) by (field; lra).
    rewrite Hid, Rabs_mult, (Rabs_right (2*PI)) by lra.
    pose proof (Rmult_lt_compat_l (2*PI) _ _ ltac:(lra) Hnear) as HX.
    replace (2*PI*(delta/(2*PI))) with delta in HX by (field; lra). exact HX. }
  exists n. split; [exact Hn|]. rewrite rotation_natural_power.
  replace (INR n*t) with ((INR n*t-2*PI*IZR z)+2*PI*IZR z) at 1 by ring.
  rewrite rotation_integer_period. apply Hcont; exact Hangle.
Qed.

Theorem special_orthogonal_dense_subsequence : forall R S,
  det2 R = 1 -> orthogonal2 R ->
  (forall n, (0 < n)%nat -> matrix_power R n <> id2) ->
  det2 S = 1 -> orthogonal2 S ->
  exists ns, indices_tend_to_infinity ns /\
    matrix_cv (fun k => matrix_power R (ns k)) S.
Proof.
  intros R S HRd HRo Hinf HSd HSo.
  assert (Hchoose : forall k, exists n,
    (k <= n)%nat /\ opnorm (sub2 (matrix_power R n) S) < (1/2)^k).
  { intro k. apply special_orthogonal_powers_dense_late; auto.
    apply pow_lt; lra. }
  destruct (@choice nat nat (fun k n =>
    (k <= n)%nat /\ opnorm (sub2 (matrix_power R n) S) < (1/2)^k) Hchoose) as [ns Hns].
  exists ns. split.
  - intros N. exists N. intros k Hk. pose proof (proj1 (Hns k)); lia.
  - intros eps He.
    destruct (pow_lt_1_zero (1/2) ltac:(rewrite Rabs_right; lra) eps He) as [N HN].
    exists N. intros k Hk. specialize (HN k Hk).
    rewrite Rabs_right in HN by (apply Rle_ge, pow_le; lra).
    pose proof (proj2 (Hns k)); lra.
Qed.

Lemma identity_special_orthogonal : det2 id2 = 1 /\ orthogonal2 id2.
Proof.
  split; [unfold det2, id2; simpl; ring|].
  unfold orthogonal2. apply mat2_ext; unfold mul2, transpose2, id2; simpl; ring.
Qed.

Theorem special_orthogonal_powers_recurrent : forall R,
  det2 R = 1 -> orthogonal2 R ->
  (forall n, (0 < n)%nat -> matrix_power R n <> id2) ->
  forall eps N, 0 < eps -> exists n, (N <= n)%nat /\
    opnorm (sub2 (matrix_power R n) id2) < eps.
Proof.
  intros R HRd HRo Hinf eps N He.
  exact (special_orthogonal_powers_dense_late R HRd HRo Hinf id2 eps N
    (proj1 identity_special_orthogonal) (proj2 identity_special_orthogonal) He).
Qed.

Theorem constant_rotation_dense_late : forall S eps N,
  det2 S = 1 -> orthogonal2 S -> 0 < eps ->
  exists n, (N <= n)%nat /\ opnorm (sub2 (matrix_power constant_rotation n) S) < eps.
Proof.
  intros S eps N HSd HSo He.
  exact (special_orthogonal_powers_dense_late constant_rotation
    (proj1 constant_rotation_special_orthogonal) (proj2 constant_rotation_special_orthogonal)
    constant_rotation_infinite_order S eps N HSd HSo He).
Qed.

Theorem constant_rotation_dense_subsequence : forall S,
  det2 S = 1 -> orthogonal2 S -> exists ns,
    indices_tend_to_infinity ns /\ matrix_cv (fun k => matrix_power constant_rotation (ns k)) S.
Proof.
  intros S HSd HSo.
  exact (special_orthogonal_dense_subsequence constant_rotation S
    (proj1 constant_rotation_special_orthogonal) (proj2 constant_rotation_special_orthogonal)
    constant_rotation_infinite_order HSd HSo).
Qed.

(* Every elliptic phase is approached by actual admissible long-period words. *)
Theorem elliptic_phase_realized_by_periodic_returns : forall S,
  det2 S = 1 -> orthogonal2 S -> Rabs (trace2 (mul2 S rotation_defect)) < 2 ->
  exists ns, indices_tend_to_infinity ns /\
    matrix_cv (fun k => matrix_power constant_rotation (ns k)) S /\
    (exists I, forall k, (I <= k)%nat -> Rabs (trace2 (periodic_return (ns k))) < 2).
Proof.
  intros S HSd HSo HS.
  destruct (constant_rotation_dense_subsequence S HSd HSo) as [ns [Hns HC]].
  exists ns. split; [exact Hns|]. split; [exact HC|].
  exact (periodic_returns_elliptic_at_phase_limit ns S Hns HC HS).
Qed.

Theorem arbitrarily_large_elliptic_returns : forall N,
  exists n, (N <= n)%nat /\ Rabs (trace2 (periodic_return n)) < 2.
Proof.
  intro N.
  destruct (elliptic_phase_realized_by_periodic_returns zero_trace_phase
    (proj1 zero_trace_phase_special_orthogonal) (proj2 zero_trace_phase_special_orthogonal)
    zero_trace_phase_elliptic) as [ns [Hns [HC [I HI]]]].
  destruct (Hns N) as [J HJ]. exists (ns (Nat.max I J)). split.
  - apply HJ; lia.
  - apply HI; lia.
Qed.

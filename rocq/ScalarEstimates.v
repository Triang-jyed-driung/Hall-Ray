From Stdlib Require Import Reals Psatz Lia.
From HallRay Require Import MatrixAlgebra.
Open Scope R_scope.

(* The minimization underlying (2.2).  r stands for e^t; r0 is the
   positive balancing scale, r0^3=q/d.  Thus m^3=q*d^2. *)
Definition vector_length (q d r : R) := Rmax (q/(r*r)) (r*d).

Theorem balanced_vector_minimum : forall q d r0,
  0 < q -> 0 < d -> 0 < r0 -> r0^3*d = q ->
  vector_length q d r0 = r0*d /\
  (forall r, 0 < r -> r0*d <= vector_length q d r) /\
  (r0*d)^3 = q*d^2.
Proof.
  intros q d r0 Hq Hd Hr0 Hbal.
  assert (H0 : r0 <> 0) by lra.
  assert (Hbalanced : q/(r0*r0) = r0*d).
  { apply (Rmult_eq_reg_r (r0*r0)); [|nra]. field_simplify; nra. }
  split.
  - unfold vector_length. rewrite Hbalanced. apply Rmax_left; lra.
  - split.
    + intros r Hr. unfold vector_length.
      destruct (Rle_dec r0 r) as [Hle|Hle].
      * eapply Rle_trans; [|apply Rmax_r]. nra.
      * eapply Rle_trans; [|apply Rmax_l].
        apply (Rmult_le_reg_r (r*r)); [nra|].
        replace (q/(r*r)*(r*r)) with q by (field; lra).
        assert (Hsq : r*r <= r0*r0) by nra.
        assert (0 <= r0*d) by nra. nra.
    + nra.
Qed.

(* A finite geometric-sum certificate for Lemma 3.6. *)
Fixpoint geometric_sum (x : R) (n : nat) : R :=
  match n with O => 0 | S k => 1+x*geometric_sum x k end.

Lemma geometric_sum_bound : forall x n,
  0 <= x < 1 -> geometric_sum x n <= / (1-x).
Proof.
  intros x n Hx. induction n as [|n IH]; simpl.
  - apply Rlt_le, Rinv_0_lt_compat; lra.
  - assert (Heq : 1+x*/(1-x) = /(1-x)) by (field; lra).
    rewrite <- Heq. apply Rplus_le_compat_l, Rmult_le_compat_l; tauto.
Qed.

Theorem fiber_geometric_constant : forall n,
  (2/25)*(11/10)*geometric_sum ((11/10)^2/900) n < 1.
Proof.
  intro n.
  pose proof (geometric_sum_bound ((11/10)^2/900) n ltac:(simpl; nra)) as H.
  assert (Hc : (2/25)*(11/10)* / (1-(11/10)^2/900) < 1).
  { apply (Rmult_lt_reg_r (1-(11/10)^2/900)); [simpl; nra|].
    field_simplify; simpl; nra. }
  nra.
Qed.

Theorem geometric_error_vanishes : forall eps,
  0 < eps -> exists N, forall n, (N <= n)%nat ->
  3*(1/2)^n < eps.
Proof.
  intros eps Heps.
  destruct (pow_lt_1_zero (1/2) ltac:(rewrite Rabs_right; lra)
              (eps/3) ltac:(lra)) as [N HN].
  exists N. intros n Hn. specialize (HN n Hn).
  rewrite Rabs_right in HN; [lra|apply Rle_ge, pow_le; lra].
Qed.

(* The algebraic root used by the constant-code orbit genuinely exists. *)
Theorem constant_root_exists : exists alpha,
  100 < alpha < 101 /\ cubic alpha = 0.
Proof.
  assert (Hcont : continuity cubic).
  { unfold cubic. reg. }
  assert (Hl : cubic 100 < 0) by (unfold cubic; simpl; nra).
  assert (Hr : 0 < cubic 101) by (unfold cubic; simpl; nra).
  destruct (IVT cubic 100 101 Hcont ltac:(lra) Hl Hr) as [alpha [Ha Hf]].
  exists alpha. split; [|exact Hf].
  split; destruct Ha; try lra.
  - destruct (Req_dec alpha 100); [subst; lra|lra].
  - destruct (Req_dec alpha 101); [subst; lra|lra].
Qed.

Theorem constant_root_unique : forall a b,
  100 <= a -> 100 <= b -> cubic a = 0 -> cubic b = 0 -> a = b.
Proof.
  intros a b Ha Hb Hfa Hfb.
  set (k := a*a+a*b+b*b-101*(a+b)+20).
  assert (Hk : 0 < k).
  { unfold k.
    pose proof (Rmult_le_pos (a-100) (b-100) ltac:(lra) ltac:(lra)).
    pose proof (pow2_ge_0 (a-100)). pose proof (pow2_ge_0 (b-100)). nra. }
  assert (Hdiff : (a-b)*k = 0).
  { unfold k. unfold cubic in *. nra. }
  nra.
Qed.

(* A direct exact-rational isolation bound, with substantially less precision
   than the earlier floating-point audit but sufficient to isolate the root. *)
Theorem constant_root_isolation : forall alpha,
  100 < alpha -> cubic alpha = 0 ->
  100801689/1000000 < alpha < 100801690/1000000.
Proof.
  intros alpha Ha Hf.
  assert (Hmono : forall a b, 100 <= a -> a < b -> cubic a < cubic b).
  { intros a b Haa Hab.
    assert (Hk : 0 < a*a+a*b+b*b-101*(a+b)+20).
    { pose proof (Rmult_le_pos (a-100) (b-100) ltac:(lra) ltac:(lra)).
      pose proof (pow2_ge_0 (a-100)). pose proof (pow2_ge_0 (b-100)). nra. }
    unfold cubic. nra. }
  assert (Hl : cubic (100801689/1000000) < 0) by (unfold cubic; simpl; nra).
  assert (Hr : 0 < cubic (100801690/1000000)) by (unfold cubic; simpl; nra).
  split.
  - destruct (Rlt_dec (100801689/1000000) alpha); auto.
    destruct (Req_dec alpha (100801689/1000000)); [subst; lra|].
    pose proof (Hmono alpha (100801689/1000000) ltac:(lra) ltac:(lra)). lra.
  - destruct (Rlt_dec alpha (100801690/1000000)); auto.
    destruct (Req_dec alpha (100801690/1000000)); [subst; lra|].
    pose proof (Hmono (100801690/1000000) alpha ltac:(lra) ltac:(lra)). lra.
Qed.

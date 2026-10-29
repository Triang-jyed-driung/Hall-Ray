From Stdlib Require Import Reals Psatz.
From HallRay Require Import ReturnBranches ReturnIdentity Contraction.
Open Scope R_scope.

Definition sa (v w : R) := 101+10*v+w.
Definition sb (v w : R) := 101+10*v-w.

Lemma sa_bounds : forall v w, in_V v w -> 503/5 <= sa v w <= 507/5.
Proof. unfold in_V, sa; intros; lra. Qed.
Lemma sb_bounds : forall v w, in_V v w -> 503/5 <= sb v w <= 507/5.
Proof. unfold in_V, sb; intros; lra. Qed.

Theorem psi_a_invariant : forall v w,
  in_V v w -> in_V (psi_a1 v w) (psi_a2 v w).
Proof.
  intros v w Hv. pose proof (sa_bounds v w Hv) as Hs.
  unfold sa in Hs. unfold in_V in *. unfold psi_a1, psi_a2.
  assert (Hpos : 0 < 101+10*v+w) by lra.
  split; split; apply (Rmult_le_reg_r (101+10*v+w)); try lra;
    field_simplify; nra.
Qed.
Theorem psi_b_invariant : forall v w,
  in_V v w -> in_V (psi_b1 v w) (psi_b2 v w).
Proof.
  intros v w Hv. pose proof (sb_bounds v w Hv) as Hs.
  unfold sb in Hs. unfold in_V in *. unfold psi_b1, psi_b2.
  assert (Hpos : 0 < 101+10*v-w) by lra.
  split; split; apply (Rmult_le_reg_r (101+10*v-w)); try lra;
    field_simplify; nra.
Qed.

Theorem psi_disjoint : forall v w v' w', in_V v w -> in_V v' w' ->
  psi_a2 v w <> psi_b2 v' w'.
Proof.
  intros v w v' w' Hv Hv'.
  pose proof (sa_bounds v w Hv). pose proof (sb_bounds v' w' Hv').
  unfold sa, sb in *. unfold in_V in *. unfold psi_a2, psi_b2.
  assert ((-10-v)/(101+10*v+w) < 0) by (apply Rdiv_neg_pos; lra).
  assert (0 < (10+v')/(101+10*v'-w')) by (apply Rdiv_lt_0_compat; lra).
  lra.
Qed.

Theorem psi_a_contraction : forall v w v' w' eps,
  in_V v w -> in_V v' w' -> 0 <= eps ->
  Rabs (v-v') <= eps -> Rabs (w-w') <= eps ->
  Rabs (psi_a1 v w-psi_a1 v' w') <= eps/900 /\
  Rabs (psi_a2 v w-psi_a2 v' w') <= eps/900.
Proof.
  intros v w v' w' eps Hv Hv' He Hdv Hdw.
  pose proof (sa_bounds v w Hv) as Hs.
  pose proof (sa_bounds v' w' Hv') as Hs'.
  assert (Hs0 : sa v w <> 0) by lra.
  assert (Hs0' : sa v' w' <> 0) by lra.
  assert (HD : (503/5)^2 <= sa v w*sa v' w').
  { pose proof (Rmult_le_compat (503/5) (sa v w) (503/5) (sa v' w')
                  ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra)). nra. }
  split.
  - apply (large_denominator_bound (sa v w*sa v' w')); auto.
    assert (Hid : sa v w*sa v' w'*(psi_a1 v w-psi_a1 v' w') =
                  10*(v-v')+(w-w')).
    { unfold sa in *. unfold psi_a1.
      field_simplify; [ring|split; assumption]. }
    rewrite Hid. eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_mult.
    replace (Rabs 10) with 10 by (rewrite Rabs_right; lra). lra.
  - apply (large_denominator_bound (sa v w*sa v' w')); auto.
    assert (Hid : sa v w*sa v' w'*(psi_a2 v w-psi_a2 v' w') =
                  (10+v)*(w-w')+(-1-w)*(v-v')).
    { unfold sa in *. unfold psi_a2.
      field_simplify; [ring|split; assumption]. }
    rewrite Hid. apply abs_linear_bound; auto.
    + unfold in_V in Hv. rewrite Rabs_right; lra.
    + unfold in_V in Hv. rewrite Rabs_left; lra.
Qed.

Theorem psi_b_contraction : forall v w v' w' eps,
  in_V v w -> in_V v' w' -> 0 <= eps ->
  Rabs (v-v') <= eps -> Rabs (w-w') <= eps ->
  Rabs (psi_b1 v w-psi_b1 v' w') <= eps/900 /\
  Rabs (psi_b2 v w-psi_b2 v' w') <= eps/900.
Proof.
  intros v w v' w' eps Hv Hv' He Hdv Hdw.
  assert (Hrv : in_V v (-w)) by (unfold in_V in *; lra).
  assert (Hrv' : in_V v' (-w')) by (unfold in_V in *; lra).
  assert (Hrw : Rabs (-w- -w') <= eps).
  { replace (-w- -w') with (-(w-w')) by ring. rewrite Rabs_Ropp. exact Hdw. }
  destruct (psi_a_contraction v (-w) v' (-w') eps Hrv Hrv' He Hdv Hrw) as [H1 H2].
  assert (Hb1 : forall a b, psi_b1 a b = psi_a1 a (-b)).
  { intros a b. unfold psi_b1, psi_a1.
    replace (101+10*a+ -b) with (101+10*a-b) by ring. reflexivity. }
  assert (Hb2 : forall a b, psi_b2 a b = -psi_a2 a (-b)).
  { intros a b. unfold psi_b2, psi_a2.
    replace (101+10*a+ -b) with (101+10*a-b) by ring. unfold Rdiv. ring. }
  rewrite !Hb1, !Hb2.
  replace (-psi_a2 v (-w)- -psi_a2 v' (-w')) with
    (-(psi_a2 v (-w)-psi_a2 v' (-w'))) by ring.
  rewrite Rabs_Ropp. split; assumption.
Qed.

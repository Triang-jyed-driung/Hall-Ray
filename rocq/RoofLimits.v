From Stdlib Require Import Reals Psatz Lia FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra ReturnBranches ReturnIdentity StableBranches
  SymbolicCoding StableCoding TwoSidedCoding NormalizedFlow LatticeReturns
  MatrixLimits Matrix3Limits EllipticContinuity.
Open Scope R_scope.

Lemma unstable_code_branch_sign : forall z,
  (z 0%Z = true -> 0 < snd (u_code z)) /\
  (z 0%Z = false -> snd (u_code z) < 0).
Proof.
  intro z. pose proof (u_code_inside (bi_shift z)) as HU.
  rewrite u_code_recursion. split; intro Hb; unfold branch; rewrite Hb; simpl fst; simpl snd.
  - change (0 < 1/da (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z)))).
    apply Rdiv_lt_0_compat; [lra|]. pose proof (da_bounds _ _ HU); lra.
  - change (-1/db (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z))) < 0).
    pose proof (db_bounds _ _ HU).
    assert (0 < /db (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z)))) by
      (apply Rinv_0_lt_compat; lra). unfold Rdiv; nra.
Qed.

Lemma unstable_code_second_nonzero : forall z, snd (u_code z) <> 0.
Proof.
  intro z. destruct (unstable_code_branch_sign z) as [Ha Hb].
  destruct (z 0%Z) eqn:Hz; [specialize (Ha eq_refl)|specialize (Hb eq_refl)]; lra.
Qed.

Lemma code_branch_eventually_matches : forall z w,
  point_converges (fun i => u_code (z i)) (u_code w) ->
  exists N, forall i, (N <= i)%nat -> z i 0%Z = w 0%Z.
Proof.
  intros z w [_ Hcv]. destruct (unstable_code_branch_sign w) as [Ha Hb].
  destruct (w 0%Z) eqn:Hw.
  - specialize (Ha eq_refl). destruct (Hcv (snd (u_code w)/2) ltac:(lra)) as [N HN].
    exists N; intros i Hi. specialize (HN i Hi); unfold Rdist in HN; apply Rabs_def2 in HN.
    destruct (z i 0%Z) eqn:Hz; [reflexivity|].
    pose proof (proj2 (unstable_code_branch_sign (z i)) Hz); lra.
  - specialize (Hb eq_refl). destruct (Hcv (-snd (u_code w)/2) ltac:(lra)) as [N HN].
    exists N; intros i Hi. specialize (HN i Hi); unfold Rdist in HN; apply Rabs_def2 in HN.
    destruct (z i 0%Z) eqn:Hz; [|reflexivity].
    pose proof (proj1 (unstable_code_branch_sign (z i)) Hz); lra.
Qed.

Definition stable_roof_denominator (s : bool) (v : point) :=
  if s then sa (fst v) (snd v) else sb (fst v) (snd v).
Definition current_roof_scale (s : bool) (u v : point) :=
  positive_cube_root (stable_roof_denominator s v*sqrt (/Rabs (snd u))).

Theorem orbit_roof_from_current_codes : forall z,
  orbit_roof_scale z = current_roof_scale (z 0%Z) (u_code z) (v_code z).
Proof.
  intro z. pose proof (u_code_inside (bi_shift z)) as HU.
  unfold current_roof_scale, stable_roof_denominator, orbit_roof_scale.
  rewrite (u_code_recursion z). destruct (z 0%Z); unfold branch; simpl fst; simpl snd;
    unfold branch_roof_a, branch_roof_b, phi_a2, phi_b2, sa, sb.
  - assert (Hd : 0 < da (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z))))
      by (pose proof (da_bounds _ _ HU); lra).
    unfold u_code, coded in Hd; simpl in Hd.
    rewrite Rabs_right by (apply Rle_ge, Rlt_le, Rdiv_lt_0_compat; lra).
    replace (/(1/da (coded_x (future_of (bi_shift z))) (coded_y (future_of (bi_shift z))))) with
      (da (coded_x (future_of (bi_shift z))) (coded_y (future_of (bi_shift z)))) by (field; lra).
    reflexivity.
  - assert (Hd : 0 < db (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z))))
      by (pose proof (db_bounds _ _ HU); lra).
    assert (Hinv : 0 < /db (fst (u_code (bi_shift z))) (snd (u_code (bi_shift z))))
      by (apply Rinv_0_lt_compat; exact Hd).
    unfold u_code, coded in Hd,Hinv; simpl in Hd,Hinv.
    rewrite Rabs_left by (unfold Rdiv; nra).
    replace (/(-(-1/db (coded_x (future_of (bi_shift z))) (coded_y (future_of (bi_shift z)))))) with
      (db (coded_x (future_of (bi_shift z))) (coded_y (future_of (bi_shift z)))) by (field; lra).
    reflexivity.
Qed.

Lemma positive_cube_root_continuous : forall x,
  0 < x -> continuity_pt positive_cube_root x.
Proof.
  intros x Hx. unfold positive_cube_root. reg.
  apply derivable_continuous_pt. exists (/x); apply derivable_pt_lim_ln; exact Hx.
Qed.
Lemma positive_log_continuous : forall x, 0 < x -> continuity_pt ln x.
Proof.
  intros x Hx; apply derivable_continuous_pt. exists (/x); apply derivable_pt_lim_ln; exact Hx.
Qed.

Theorem current_roof_scale_sequence_limit : forall s u v a b,
  point_converges u a -> point_converges v b -> stable_inside b -> snd a <> 0 ->
  Un_cv (fun i => current_roof_scale s (u i) (v i)) (current_roof_scale s a b).
Proof.
  intros s u v a b [Hu1 Hu2] [Hv1 Hv2] Hb Ha.
  assert (Habs : Un_cv (fun i => Rabs (snd (u i))) (Rabs (snd a))).
  { apply continuity_seq; [reg|exact Hu2]. }
  assert (Hinv : Un_cv (fun i => /Rabs (snd (u i))) (/Rabs (snd a))).
  { apply scalar_cv_inverse; [exact Habs|apply Rabs_no_R0; exact Ha]. }
  assert (Hsqrt : Un_cv (fun i => sqrt (/Rabs (snd (u i)))) (sqrt (/Rabs (snd a)))).
  { apply scalar_cv_square_root; [exact Hinv|].
    apply Rlt_le, Rinv_0_lt_compat, Rabs_pos_lt; exact Ha. }
  assert (Hd : 0 < stable_roof_denominator s b).
  { unfold stable_roof_denominator; destruct s;
      [pose proof (sa_bounds _ _ Hb)|pose proof (sb_bounds _ _ Hb)]; lra. }
  assert (Hdenom : Un_cv (fun i => stable_roof_denominator s (v i)) (stable_roof_denominator s b)).
  { unfold stable_roof_denominator; destruct s; unfold sa,sb; scalar_cv_algebra. }
  unfold current_roof_scale. apply continuity_seq.
  - apply positive_cube_root_continuous, Rmult_lt_0_compat; [exact Hd|].
    apply sqrt_lt_R0, Rinv_0_lt_compat, Rabs_pos_lt; exact Ha.
  - apply CV_mult; assumption.
Qed.

Theorem orbit_roof_sequence_limit : forall z w,
  point_converges (fun i => u_code (z i)) (u_code w) ->
  point_converges (fun i => v_code (z i)) (v_code w) ->
  Un_cv (fun i => orbit_roof_time (z i)) (orbit_roof_time w).
Proof.
  intros z w Hu Hv.
  destruct (code_branch_eventually_matches z w Hu) as [N HN].
  assert (Hcurrent : Un_cv
    (fun i => current_roof_scale (w 0%Z) (u_code (z i)) (v_code (z i)))
    (current_roof_scale (w 0%Z) (u_code w) (v_code w))).
  { apply current_roof_scale_sequence_limit; try assumption;
      [apply v_code_inside|apply unstable_code_second_nonzero]. }
  assert (Hscale : Un_cv (fun i => orbit_roof_scale (z i)) (orbit_roof_scale w)).
  { rewrite orbit_roof_from_current_codes. eapply scalar_cv_eventual_agreement; [exact Hcurrent|].
    exists N; intros i Hi; rewrite orbit_roof_from_current_codes, HN by exact Hi; reflexivity. }
  unfold orbit_roof_time. apply continuity_seq; [|exact Hscale].
  apply positive_log_continuous. pose proof (orbit_roof_scale_bounds w); lra.
Qed.

Lemma scalar_limit_nonnegative : forall u l,
  Un_cv u l -> (forall i, 0 <= u i) -> 0 <= l.
Proof.
  intros u l Hu Hpos. destruct (Rle_dec 0 l) as [Hyes|Hno]; auto.
  destruct (Hu (-l/2) ltac:(lra)) as [N HN]. specialize (HN N ltac:(lia)).
  specialize (Hpos N). unfold Rdist in HN; apply Rabs_def2 in HN; lra.
Qed.

Theorem return_segment_time_closed_limit : forall z w ts t,
  point_converges (fun i => u_code (z i)) (u_code w) ->
  point_converges (fun i => v_code (z i)) (v_code w) -> Un_cv ts t ->
  (forall i, 0 <= ts i <= orbit_roof_time (z i)) ->
  0 <= t <= orbit_roof_time w.
Proof.
  intros z w ts t Hu Hv Ht Hinterval. split.
  - apply (scalar_limit_nonnegative ts t Ht); intro i; exact (proj1 (Hinterval i)).
  - assert (Hroof := orbit_roof_sequence_limit z w Hu Hv).
    pose proof (scalar_limit_nonnegative (fun i => orbit_roof_time (z i)-ts i)
      (orbit_roof_time w-t) (CV_minus _ _ _ _ Hroof Ht) ltac:(intro i; specialize (Hinterval i); lra)). lra.
Qed.

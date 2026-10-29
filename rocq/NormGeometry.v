From Stdlib Require Import Reals Psatz.
From HallRay Require Import PaperTarget.
Open Scope R_scope.

Definition norm_bound (nm : planar_norm) :=
  length2 nm (1,0)+length2 nm (0,1)+1.

Lemma norm_bound_positive : forall nm, 0 < norm_bound nm.
Proof.
  intro nm; unfold norm_bound.
  pose proof (length2_nonnegative nm (1,0)).
  pose proof (length2_nonnegative nm (0,1)). lra.
Qed.

Theorem planar_norm_upper : forall nm x y,
  length2 nm (x,y) <= norm_bound nm*(Rabs x+Rabs y).
Proof.
  intros nm x y.
  pose proof (length2_triangle nm (vscale x (1,0)) (vscale y (0,1))) as H.
  replace (vadd (vscale x (1,0)) (vscale y (0,1))) with (x,y) in H
    by (unfold vadd, vscale; simpl; f_equal; ring).
  rewrite !length2_homogeneous in H.
  unfold norm_bound. pose proof (length2_nonnegative nm (1,0)).
  pose proof (length2_nonnegative nm (0,1)).
  pose proof (Rabs_pos x). pose proof (Rabs_pos y). nra.
Qed.

Theorem planar_norm_lipschitz : forall nm x y u v,
  Rabs (length2 nm (x,y)-length2 nm (u,v)) <=
    norm_bound nm*(Rabs (x-u)+Rabs (y-v)).
Proof.
  intros nm x y u v.
  pose proof (length2_triangle nm (u,v) (x-u,y-v)) as H1.
  pose proof (length2_triangle nm (x,y) (u-x,v-y)) as H2.
  replace (vadd (u,v) (x-u,y-v)) with (x,y) in H1
    by (unfold vadd; simpl; f_equal; ring).
  replace (vadd (x,y) (u-x,v-y)) with (u,v) in H2
    by (unfold vadd; simpl; f_equal; ring).
  pose proof (planar_norm_upper nm (x-u) (y-v)) as H3.
  pose proof (planar_norm_upper nm (u-x) (v-y)) as H4.
  rewrite (Rabs_minus_sym u x), (Rabs_minus_sym v y) in H4.
  apply Rabs_le; split; lra.
Qed.

Definition norm_face (nm : planar_norm) (s : bool) (t : R) :=
  if s then length2 nm (1,t) else length2 nm (t,1).

Lemma norm_face_continuous : forall nm s, continuity (norm_face nm s).
Proof.
  intros nm s t. unfold continuity_pt, continue_in, limit1_in, limit_in; simpl.
  intros eps He. exists (eps/norm_bound nm). split.
  - apply Rdiv_lt_0_compat; [exact He|apply norm_bound_positive].
  - intros u [_ Hu].
    assert (Hlip : Rabs (norm_face nm s u-norm_face nm s t) <=
      norm_bound nm*Rabs (u-t)).
    { destruct s; unfold norm_face.
      - pose proof (planar_norm_lipschitz nm 1 u 1 t) as H.
        replace (1-1) with 0 in H by ring. rewrite Rabs_R0 in H; lra.
      - pose proof (planar_norm_lipschitz nm u 1 t 1) as H.
        replace (1-1) with 0 in H by ring. rewrite Rabs_R0 in H; lra. }
    assert (HC := norm_bound_positive nm).
    assert (Heq : norm_bound nm*(eps/norm_bound nm) = eps) by (field; lra).
    apply Rle_lt_trans with (norm_bound nm*Rabs (u-t)); [exact Hlip|].
    rewrite <- Heq. apply Rmult_lt_compat_l; assumption.
Qed.

Lemma norm_face_positive : forall nm s t, 0 < norm_face nm s t.
Proof.
  intros nm s t. destruct s; unfold norm_face.
  - pose proof (length2_nonnegative nm (1,t)) as Hn.
    destruct (Req_dec (length2 nm (1,t)) 0) as [Hz|Hz]; [|lra].
    pose proof (length2_definite nm (1,t) Hz) as Hd.
    apply (f_equal fst) in Hd. simpl in Hd. lra.
  - pose proof (length2_nonnegative nm (t,1)) as Hn.
    destruct (Req_dec (length2 nm (t,1)) 0) as [Hz|Hz]; [|lra].
    pose proof (length2_definite nm (t,1) Hz) as Hd.
    apply (f_equal snd) in Hd. simpl in Hd. lra.
Qed.

Theorem norm_faces_uniform_lower : forall nm,
  exists k, 0 < k /\ forall s t, -1 <= t <= 1 -> k <= norm_face nm s t.
Proof.
  intro nm.
  destruct (continuity_ab_min (norm_face nm true) (-1) 1 ltac:(lra)
    ltac:(intros; apply norm_face_continuous)) as [a [Ha Hain]].
  destruct (continuity_ab_min (norm_face nm false) (-1) 1 ltac:(lra)
    ltac:(intros; apply norm_face_continuous)) as [b [Hb Hbin]].
  exists (Rmin (norm_face nm true a) (norm_face nm false b)). split.
  - apply Rmin_glb_lt; apply norm_face_positive.
  - intros [] t Ht.
    + eapply Rle_trans; [apply Rmin_l|apply Ha; exact Ht].
    + eapply Rle_trans; [apply Rmin_r|apply Hb; exact Ht].
Qed.

Lemma quotient_in_unit_interval : forall x y,
  x <> 0 -> Rabs y <= Rabs x -> -1 <= y/x <= 1.
Proof.
  intros x y Hx Hle.
  assert (Habs : Rabs (y/x) <= 1).
  { unfold Rdiv. rewrite Rabs_mult, Rabs_inv. apply (Rmult_le_reg_r (Rabs x)).
    - apply Rabs_pos_lt; exact Hx.
    - replace (Rabs y* /Rabs x*Rabs x) with (Rabs y) by
        (field; apply Rabs_no_R0; exact Hx). lra. }
  destruct (Rcase_abs (y/x)); [rewrite Rabs_left in Habs by lra|rewrite Rabs_right in Habs by lra]; lra.
Qed.

Theorem planar_norm_equivalence : forall nm,
  exists k, 0 < k /\ forall x y,
    k*Rmax (Rabs x) (Rabs y) <= length2 nm (x,y).
Proof.
  intro nm. destruct (norm_faces_uniform_lower nm) as [k [Hk Hface]].
  exists k; split; [exact Hk|]. intros x y.
  destruct (Rle_dec (Rabs y) (Rabs x)) as [Hxy|Hxy].
  - rewrite Rmax_left by exact Hxy.
    destruct (Req_dec x 0) as [Hx|Hx].
    + subst x. rewrite Rabs_R0. pose proof (length2_nonnegative nm (0,y)); lra.
    + pose proof (Hface true (y/x) (quotient_in_unit_interval x y Hx Hxy)) as H.
      unfold norm_face in H.
      replace (x,y) with (vscale x (1,y/x)) by
        (unfold vscale; simpl; f_equal; field; assumption).
      rewrite length2_homogeneous. pose proof (Rabs_pos x). nra.
  - assert (Hyx : Rabs x <= Rabs y) by lra. rewrite Rmax_right by exact Hyx.
    assert (Hy : y <> 0).
    { intro H; subst y. rewrite Rabs_R0 in Hxy. pose proof (Rabs_pos x); lra. }
    pose proof (Hface false (x/y) (quotient_in_unit_interval y x Hy Hyx)) as H.
    unfold norm_face in H.
    replace (x,y) with (vscale y (x/y,1)) by
      (unfold vscale; simpl; f_equal; field; assumption).
    rewrite length2_homogeneous. pose proof (Rabs_pos y). nra.
Qed.

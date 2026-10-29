From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm ReturnBranches Contraction.
Open Scope R_scope.

Lemma sqrt_at_least_ten : forall d, 100 <= d -> 10 <= sqrt d.
Proof.
  intros d Hd. pose proof (sqrt_pos d).
  pose proof (Rsqr_sqrt d ltac:(lra)). unfold Rsqr in *. nra.
Qed.

Lemma normalized_b_reflection : forall x y,
  normalized_b x y = sign_conjugate (normalized_a x (-y)).
Proof.
  intros x y. unfold normalized_b, normalized_a.
  replace (101-x-10*(-y)) with (101-x+10*y) by ring.
  apply mat2_ext; unfold scale2, numerator_b, numerator_a, sign_conjugate; simpl; ring.
Qed.

Lemma inverse_sqrt_bound : forall d, 100 <= d -> 0 <= /sqrt d <= 1/10.
Proof.
  intros d Hd. pose proof (sqrt_at_least_ten d Hd) as Hs.
  split; [apply Rlt_le, Rinv_0_lt_compat; lra|].
  apply (Rmult_le_reg_r (sqrt d)); [lra|].
  replace (/sqrt d*sqrt d) with 1 by (field; lra). nra.
Qed.

Lemma inverse_sqrt_lipschitz : forall d d' eps,
  100 <= d -> 100 <= d' -> 0 <= eps -> Rabs (d-d') <= 11*eps ->
  Rabs (/sqrt d- /sqrt d') <= (11/2000)*eps.
Proof.
  intros d d' eps Hd Hd' He Hdiff.
  pose proof (sqrt_at_least_ten d Hd) as Hs.
  pose proof (sqrt_at_least_ten d' Hd') as Hs'.
  pose proof (Rsqr_sqrt d ltac:(lra)) as Hsq.
  pose proof (Rsqr_sqrt d' ltac:(lra)) as Hsq'. unfold Rsqr in Hsq, Hsq'.
  assert (Hden : 2000 <= sqrt d*sqrt d'*(sqrt d+sqrt d')).
  { assert (100 <= sqrt d*sqrt d') by nra.
    pose proof (Rmult_le_compat 100 (sqrt d*sqrt d') 20 (sqrt d+sqrt d')
                  ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra)). nra. }
  assert (Hid : sqrt d*sqrt d'*(sqrt d+sqrt d')*(/sqrt d- /sqrt d') = d'-d).
  { replace (d'-d) with (sqrt d'*sqrt d'-sqrt d*sqrt d) by lra.
    field; split; lra. }
  pose proof (f_equal Rabs Hid) as Habs.
  rewrite Rabs_mult in Habs.
  rewrite (Rabs_right (sqrt d*sqrt d'*(sqrt d+sqrt d'))) in Habs by lra.
  rewrite Rabs_minus_sym in Hdiff.
  assert (Hlow : 2000*Rabs (/sqrt d- /sqrt d') <=
    sqrt d*sqrt d'*(sqrt d+sqrt d')*Rabs (/sqrt d- /sqrt d')).
  { apply Rmult_le_compat_r; auto using Rabs_pos. }
  lra.
Qed.

Theorem numerator_a_op_bound : forall x y, in_U x y ->
  opnorm (numerator_a x y) <= 21/2 /\ opnorm (adj2 (numerator_a x y)) <= 21/2.
Proof.
  intros x y Hu.
  assert (Hdecomp : numerator_a x y = add2 base_numerator (Mat2 (-y) x 0 0)).
  { apply mat2_ext; unfold numerator_a, add2, base_numerator; simpl; ring. }
  assert (Hx : Rabs x <= 1/5) by (apply Rabs_le; unfold in_U in Hu; lra).
  assert (Hy : Rabs (-y) <= 1/5).
  { rewrite Rabs_Ropp. apply Rabs_le; unfold in_U in Hu; lra. }
  pose proof (sparse_row_bound (-y) x (1/5) ltac:(lra) Hy Hx).
  pose proof (sparse_adjugate_bound (-y) x (1/5) ltac:(lra) Hy Hx).
  pose proof base_numerator_bound. pose proof base_adjugate_bound.
  split.
  - rewrite Hdecomp. eapply Rle_trans; [apply opnorm_subadditive|]. lra.
  - rewrite Hdecomp, adj2_add. eapply Rle_trans; [apply opnorm_subadditive|]. lra.
Qed.

Lemma da_lipschitz : forall x y x' y' eps,
  Rabs (x-x') <= eps -> Rabs (y-y') <= eps ->
  Rabs (da x y-da x' y') <= 11*eps.
Proof.
  intros x y x' y' eps Hx Hy.
  replace (da x y-da x' y') with (-((x-x')+10*(y-y'))) by (unfold da; ring).
  rewrite Rabs_Ropp. eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_mult.
  rewrite (Rabs_right 10) by lra. lra.
Qed.

Theorem normalized_a_lipschitz : forall x y x' y' eps,
  in_U x y -> in_U x' y' -> 0 <= eps ->
  Rabs (x-x') <= eps -> Rabs (y-y') <= eps ->
  opnorm (sub2 (normalized_a x y) (normalized_a x' y')) <= (1/5)*eps.
Proof.
  intros x y x' y' eps Hu Hu' He Hx Hy.
  pose proof (da_bounds x y Hu) as Hd. pose proof (da_bounds x' y' Hu') as Hd'.
  assert (Hdecomp : sub2 (normalized_a x y) (normalized_a x' y') =
    add2 (scale2 (/sqrt (da x y)) (Mat2 (-(y-y')) (x-x') 0 0))
         (scale2 (/sqrt (da x y)- /sqrt (da x' y')) (numerator_a x' y'))).
  { apply mat2_ext; unfold sub2, add2, normalized_a, scale2, numerator_a, da; simpl; ring. }
  assert (Hdy : Rabs (-(y-y')) <= eps) by (rewrite Rabs_Ropp; exact Hy).
  pose proof (sparse_row_bound (-(y-y')) (x-x') eps He Hdy Hx) as Hsparse.
  pose proof (inverse_sqrt_bound (da x y) ltac:(lra)) as Hinv.
  pose proof (inverse_sqrt_lipschitz (da x y) (da x' y') eps ltac:(lra) ltac:(lra)
    He (da_lipschitz x y x' y' eps Hx Hy)) as Hdiff.
  destruct (numerator_a_op_bound x' y' Hu') as [HN HNadj].
  rewrite Hdecomp. eapply Rle_trans; [apply opnorm_subadditive|].
  pose proof (opnorm_scale_bound (/sqrt (da x y)) (Mat2 (-(y-y')) (x-x') 0 0)) as Hscale1.
  pose proof (opnorm_scale_bound (/sqrt (da x y)- /sqrt (da x' y')) (numerator_a x' y')) as Hscale2.
  rewrite (Rabs_right (/sqrt (da x y))) in Hscale1 by lra.
  assert (H1 : /sqrt (da x y)*opnorm (Mat2 (-(y-y')) (x-x') 0 0) <= (1/10)*((71/50)*eps)).
  { apply Rmult_le_compat; auto using opnorm_nonnegative; lra. }
  assert (H2 : Rabs (/sqrt (da x y)- /sqrt (da x' y'))*opnorm (numerator_a x' y') <=
                 ((11/2000)*eps)*(21/2)).
  { apply Rmult_le_compat; auto using Rabs_pos, opnorm_nonnegative. }
  nra.
Qed.

Theorem normalized_adja_lipschitz : forall x y x' y' eps,
  in_U x y -> in_U x' y' -> 0 <= eps ->
  Rabs (x-x') <= eps -> Rabs (y-y') <= eps ->
  opnorm (sub2 (adj2 (normalized_a x y)) (adj2 (normalized_a x' y'))) <= (1/5)*eps.
Proof.
  intros x y x' y' eps Hu Hu' He Hx Hy.
  pose proof (da_bounds x y Hu) as Hd. pose proof (da_bounds x' y' Hu') as Hd'.
  assert (Hdecomp : sub2 (adj2 (normalized_a x y)) (adj2 (normalized_a x' y')) =
    add2 (scale2 (/sqrt (da x y)) (adj2 (Mat2 (-(y-y')) (x-x') 0 0)))
         (scale2 (/sqrt (da x y)- /sqrt (da x' y')) (adj2 (numerator_a x' y')))).
  { apply mat2_ext; unfold sub2, add2, normalized_a, adj2, scale2, numerator_a, da; simpl; ring. }
  assert (Hdy : Rabs (-(y-y')) <= eps) by (rewrite Rabs_Ropp; exact Hy).
  pose proof (sparse_adjugate_bound (-(y-y')) (x-x') eps He Hdy Hx) as Hsparse.
  pose proof (inverse_sqrt_bound (da x y) ltac:(lra)) as Hinv.
  pose proof (inverse_sqrt_lipschitz (da x y) (da x' y') eps ltac:(lra) ltac:(lra)
    He (da_lipschitz x y x' y' eps Hx Hy)) as Hdiff.
  destruct (numerator_a_op_bound x' y' Hu') as [HN HNadj].
  rewrite Hdecomp. eapply Rle_trans; [apply opnorm_subadditive|].
  pose proof (opnorm_scale_bound (/sqrt (da x y)) (adj2 (Mat2 (-(y-y')) (x-x') 0 0))) as Hscale1.
  pose proof (opnorm_scale_bound (/sqrt (da x y)- /sqrt (da x' y')) (adj2 (numerator_a x' y'))) as Hscale2.
  rewrite (Rabs_right (/sqrt (da x y))) in Hscale1 by lra.
  assert (H1 : /sqrt (da x y)*opnorm (adj2 (Mat2 (-(y-y')) (x-x') 0 0)) <= (1/10)*((71/50)*eps)).
  { apply Rmult_le_compat; auto using opnorm_nonnegative; lra. }
  assert (H2 : Rabs (/sqrt (da x y)- /sqrt (da x' y'))*opnorm (adj2 (numerator_a x' y')) <=
                 ((11/2000)*eps)*(21/2)).
  { apply Rmult_le_compat; auto using Rabs_pos, opnorm_nonnegative. }
  nra.
Qed.

Lemma normalized_origin_orthogonal :
  orthogonal2 (normalized_a 0 0) /\ orthogonal2 (adj2 (normalized_a 0 0)).
Proof.
  pose proof (sqrt_pos 101) as Hs.
  pose proof (Rsqr_sqrt 101 ltac:(lra)) as Hsq. unfold Rsqr in Hsq.
  replace (101-0-10*0) with 101 by ring.
  split; unfold orthogonal2; apply mat2_ext;
    unfold normalized_a, numerator_a, mul2, transpose2, scale2, adj2, id2; simpl;
    replace (101-0-10*0) with 101 by ring;
    field_simplify; try rewrite pow2_sqrt by lra; try field; nra.
Qed.

Lemma matrix_difference_decomposition : forall A B, A = add2 (sub2 A B) B.
Proof. intros [] []; apply mat2_ext; unfold add2, sub2, scale2; simpl; ring. Qed.

Theorem normalized_a_uniform_bounds : forall x y, in_U x y ->
  opnorm (normalized_a x y) <= 26/25 /\
  opnorm (adj2 (normalized_a x y)) <= 26/25.
Proof.
  intros x y Hu.
  assert (Horigin : in_U 0 0) by (unfold in_U; lra).
  assert (Hx : Rabs (x-0) <= 1/5) by (apply Rabs_le; unfold in_U in Hu; lra).
  assert (Hy : Rabs (y-0) <= 1/5) by (apply Rabs_le; unfold in_U in Hu; lra).
  pose proof (normalized_a_lipschitz x y 0 0 (1/5) Hu Horigin ltac:(lra) Hx Hy) as HL.
  pose proof (normalized_adja_lipschitz x y 0 0 (1/5) Hu Horigin ltac:(lra) Hx Hy) as HLadj.
  destruct normalized_origin_orthogonal as [Ho Ho'].
  pose proof (orthogonal_opnorm _ Ho) as Hnorm.
  pose proof (orthogonal_opnorm _ Ho') as Hnorm'.
  split.
  - rewrite (matrix_difference_decomposition (normalized_a x y) (normalized_a 0 0)).
    eapply Rle_trans; [apply opnorm_subadditive|]. lra.
  - rewrite (matrix_difference_decomposition (adj2 (normalized_a x y)) (adj2 (normalized_a 0 0))).
    eapply Rle_trans; [apply opnorm_subadditive|]. lra.
Qed.

Theorem normalized_b_lipschitz : forall x y x' y' eps,
  in_U x y -> in_U x' y' -> 0 <= eps ->
  Rabs (x-x') <= eps -> Rabs (y-y') <= eps ->
  opnorm (sub2 (normalized_b x y) (normalized_b x' y')) <= (1/5)*eps.
Proof.
  intros x y x' y' eps Hu Hu' He Hx Hy.
  rewrite !normalized_b_reflection, sign_conjugate_sub, sign_conjugate_opnorm.
  apply normalized_a_lipschitz; auto using reflect_U.
  replace (-y- -y') with (-(y-y')) by ring. rewrite Rabs_Ropp. exact Hy.
Qed.

Theorem normalized_b_uniform_bounds : forall x y, in_U x y ->
  opnorm (normalized_b x y) <= 26/25 /\
  opnorm (adj2 (normalized_b x y)) <= 26/25.
Proof.
  intros x y Hu. rewrite normalized_b_reflection, sign_conjugate_adjugate,
    !sign_conjugate_opnorm. apply normalized_a_uniform_bounds, reflect_U; exact Hu.
Qed.

Definition fiber_matrix (s : bool) (x y : R) :=
  if s then normalized_a x y else normalized_b x y.

Theorem fiber_matrix_unimodular : forall s x y,
  in_U x y -> det2 (fiber_matrix s x y) = 1.
Proof.
  intros [] x y Hu; unfold fiber_matrix.
  - apply normalized_a_unimodular. pose proof (da_bounds x y Hu). unfold da in *; lra.
  - apply normalized_b_unimodular. pose proof (db_bounds x y Hu). unfold db in *; lra.
Qed.

Theorem fiber_matrix_uniform_bounds : forall s x y, in_U x y ->
  opnorm (fiber_matrix s x y) <= 26/25 /\
  opnorm (adj2 (fiber_matrix s x y)) <= 26/25.
Proof.
  intros [] x y Hu; unfold fiber_matrix;
    auto using normalized_a_uniform_bounds, normalized_b_uniform_bounds.
Qed.

Theorem fiber_matrix_lipschitz : forall s x y x' y' eps,
  in_U x y -> in_U x' y' -> 0 <= eps ->
  Rabs (x-x') <= eps -> Rabs (y-y') <= eps ->
  opnorm (sub2 (fiber_matrix s x y) (fiber_matrix s x' y')) <= (1/5)*eps.
Proof.
  intros [] x y x' y' eps Hu Hu' He Hx Hy; unfold fiber_matrix;
    auto using normalized_a_lipschitz, normalized_b_lipschitz.
Qed.

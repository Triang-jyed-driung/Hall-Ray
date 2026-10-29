From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import MatrixAlgebra ScalarEstimates FiberProducts EuclideanNorm.
Open Scope R_scope.

Lemma a11_sub : forall A B, a11 (sub2 A B) = a11 A-a11 B.
Proof. intros [] []; unfold sub2, add2, scale2; simpl; ring. Qed.
Lemma a12_sub : forall A B, a12 (sub2 A B) = a12 A-a12 B.
Proof. intros [] []; unfold sub2, add2, scale2; simpl; ring. Qed.
Lemma a21_sub : forall A B, a21 (sub2 A B) = a21 A-a21 B.
Proof. intros [] []; unfold sub2, add2, scale2; simpl; ring. Qed.
Lemma a22_sub : forall A B, a22 (sub2 A B) = a22 A-a22 B.
Proof. intros [] []; unfold sub2, add2, scale2; simpl; ring. Qed.

Lemma opnorm_entries : forall A,
  Rabs (a11 A) <= opnorm A /\ Rabs (a12 A) <= opnorm A /\
  Rabs (a21 A) <= opnorm A /\ Rabs (a22 A) <= opnorm A.
Proof.
  intro A.
  assert (H10 : action A (1,0) = (a11 A,a21 A))
    by (unfold action; simpl; f_equal; ring).
  assert (H01 : action A (0,1) = (a12 A,a22 A))
    by (unfold action; simpl; f_equal; ring).
  assert (Hunit01 : enorm (0,1) = 1).
  { unfold enorm; simpl. replace (0*0+1*1) with 1 by ring. apply sqrt_1. }
  pose proof (opnorm_lower A (1,0) ltac:(rewrite enorm_unit; lra)) as H1.
  pose proof (opnorm_lower A (0,1) ltac:(rewrite Hunit01; lra)) as H2.
  rewrite H10 in H1. rewrite H01 in H2.
  destruct (enorm_coordinates (a11 A) (a21 A)).
  destruct (enorm_coordinates (a12 A) (a22 A)). repeat split; lra.
Qed.

Lemma real_constant_cv : forall c, Un_cv (fun _ : nat => c) c.
Proof.
  intros c eps He. exists O. intros n Hn.
  unfold Rdist. replace (c-c) with 0 by ring. rewrite Rabs_R0. exact He.
Qed.

Definition matrix_cv (U : nat -> mat2) (L : mat2) :=
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
    opnorm (sub2 (U n) L) < eps.
Definition matrix_cauchy (U : nat -> mat2) :=
  forall eps, 0 < eps -> exists N, forall n m,
    (N <= n)%nat -> (N <= m)%nat -> opnorm (sub2 (U n) (U m)) < eps.
Definition coordinate_cv (U : nat -> mat2) (L : mat2) :=
  Un_cv (fun n => a11 (U n)) (a11 L) /\
  Un_cv (fun n => a12 (U n)) (a12 L) /\
  Un_cv (fun n => a21 (U n)) (a21 L) /\
  Un_cv (fun n => a22 (U n)) (a22 L).

Lemma matrix_cv_coordinates : forall U L, matrix_cv U L -> coordinate_cv U L.
Proof.
  intros U L H. repeat split; intros eps He;
    destruct (H eps He) as [N HN]; exists N; intros n Hn;
    specialize (HN n Hn); pose proof (opnorm_entries (sub2 (U n) L)) as HB;
    rewrite a11_sub, a12_sub, a21_sub, a22_sub in HB; unfold Rdist; lra.
Qed.

Lemma coordinates_matrix_cv : forall U L, coordinate_cv U L -> matrix_cv U L.
Proof.
  intros U L [H11 [H12 [H21 H22]]] eps He.
  destruct (H11 (eps/8) ltac:(lra)) as [N11 HN11].
  destruct (H12 (eps/8) ltac:(lra)) as [N12 HN12].
  destruct (H21 (eps/8) ltac:(lra)) as [N21 HN21].
  destruct (H22 (eps/8) ltac:(lra)) as [N22 HN22].
  exists (Nat.max (Nat.max N11 N12) (Nat.max N21 N22)). intros n Hn.
  specialize (HN11 n ltac:(lia)). specialize (HN12 n ltac:(lia)).
  specialize (HN21 n ltac:(lia)). specialize (HN22 n ltac:(lia)).
  unfold Rdist in *.
  pose proof (opnorm_upper (sub2 (U n) L) (entry_bound (sub2 (U n) L))) as HB.
  assert (Hbound : opnorm (sub2 (U n) L) <= entry_bound (sub2 (U n) L)).
  { apply HB. intros v Hv. pose proof (action_entry_bound (sub2 (U n) L) v).
    pose proof (entry_bound_nonnegative (sub2 (U n) L)). nra. }
  unfold entry_bound in Hbound. rewrite a11_sub, a12_sub, a21_sub, a22_sub in Hbound. lra.
Qed.

Theorem euclidean_matrix_complete : forall U,
  matrix_cauchy U -> { L : mat2 | matrix_cv U L }.
Proof.
  intros U HC.
  assert (HC11 : Cauchy_crit (fun n => a11 (U n))).
  { intros eps He. destruct (HC eps He) as [N HN]. exists N. intros n m Hn Hm.
    specialize (HN n m Hn Hm). pose proof (opnorm_entries (sub2 (U n) (U m))) as HB.
    rewrite a11_sub in HB. unfold Rdist; lra. }
  assert (HC12 : Cauchy_crit (fun n => a12 (U n))).
  { intros eps He. destruct (HC eps He) as [N HN]. exists N. intros n m Hn Hm.
    specialize (HN n m Hn Hm). pose proof (opnorm_entries (sub2 (U n) (U m))) as HB.
    rewrite a12_sub in HB. unfold Rdist; lra. }
  assert (HC21 : Cauchy_crit (fun n => a21 (U n))).
  { intros eps He. destruct (HC eps He) as [N HN]. exists N. intros n m Hn Hm.
    specialize (HN n m Hn Hm). pose proof (opnorm_entries (sub2 (U n) (U m))) as HB.
    rewrite a21_sub in HB. unfold Rdist; lra. }
  assert (HC22 : Cauchy_crit (fun n => a22 (U n))).
  { intros eps He. destruct (HC eps He) as [N HN]. exists N. intros n m Hn Hm.
    specialize (HN n m Hn Hm). pose proof (opnorm_entries (sub2 (U n) (U m))) as HB.
    rewrite a22_sub in HB. unfold Rdist; lra. }
  destruct (R_complete _ HC11) as [x Hx]. destruct (R_complete _ HC12) as [y Hy].
  destruct (R_complete _ HC21) as [z Hz]. destruct (R_complete _ HC22) as [t Ht].
  exists (Mat2 x y z t). apply coordinates_matrix_cv. repeat split; assumption.
Qed.

Theorem matrix_cv_unique : forall U A B, matrix_cv U A -> matrix_cv U B -> A = B.
Proof.
  intros U A B HA HB. apply matrix_cv_coordinates in HA, HB.
  destruct HA as [HA11 [HA12 [HA21 HA22]]].
  destruct HB as [HB11 [HB12 [HB21 HB22]]].
  apply mat2_ext; eapply UL_sequence; eassumption.
Qed.

Lemma opnorm_negative : forall A, opnorm (scale2 (-1) A) = opnorm A.
Proof.
  assert (Hle : forall A, opnorm (scale2 (-1) A) <= opnorm A).
  { intro A. pose proof (opnorm_scale_bound (-1) A) as H.
    rewrite (Rabs_left (-1)) in H by lra. nra. }
  intro A. apply Rle_antisym; [apply Hle|].
  pose proof (Hle (scale2 (-1) A)) as H.
  assert (Hopp : scale2 (-1) (scale2 (-1) A) = A)
    by (destruct A; apply mat2_ext; unfold scale2; simpl; ring).
  rewrite Hopp in H. exact H.
Qed.

Lemma opnorm_difference_symmetric : forall A B, opnorm (sub2 A B) = opnorm (sub2 B A).
Proof.
  intros A B.
  assert (Hopp : sub2 A B = scale2 (-1) (sub2 B A)).
  { destruct A, B; apply mat2_ext; unfold sub2, add2, scale2; simpl; ring. }
  rewrite Hopp, opnorm_negative. reflexivity.
Qed.

Lemma opnorm_difference_triangle : forall A B C,
  opnorm (sub2 A C) <= opnorm (sub2 A B)+opnorm (sub2 B C).
Proof.
  intros A B C.
  assert (Hsum : sub2 A C = add2 (sub2 A B) (sub2 B C)).
  { destruct A, B, C; apply mat2_ext; unfold sub2, add2, scale2; simpl; ring. }
  rewrite Hsum. apply opnorm_subadditive.
Qed.

Theorem matrix_limit_closed_bound : forall U L Q b N,
  matrix_cv U L ->
  (forall n, (N <= n)%nat -> opnorm (sub2 (U n) Q) <= b) ->
  opnorm (sub2 L Q) <= b.
Proof.
  intros U L Q b N HC HB.
  destruct (Rle_dec (opnorm (sub2 L Q)) b); auto.
  destruct (HC ((opnorm (sub2 L Q)-b)/2) ltac:(lra)) as [K HK].
  specialize (HK (Nat.max N K) (Nat.le_max_r N K)).
  specialize (HB (Nat.max N K) (Nat.le_max_l N K)).
  pose proof (opnorm_difference_triangle L (U (Nat.max N K)) Q) as HT.
  rewrite (opnorm_difference_symmetric L (U (Nat.max N K))) in HT. lra.
Qed.

Theorem matrix_cv_determinant : forall U L,
  matrix_cv U L -> Un_cv (fun n => det2 (U n)) (det2 L).
Proof.
  intros U L HC. apply matrix_cv_coordinates in HC.
  destruct HC as [H11 [H12 [H21 H22]]].
  unfold det2. apply CV_minus; apply CV_mult; assumption.
Qed.

Theorem unimodular_limit : forall U L,
  matrix_cv U L -> (forall n, det2 (U n) = 1) -> det2 L = 1.
Proof.
  intros U L HC Hd. apply (UL_sequence (fun n => det2 (U n)) (det2 L) 1).
  - apply matrix_cv_determinant; exact HC.
  - intros eps He. exists O. intros n Hn. unfold Rdist. rewrite Hd.
    replace (1-1) with 0 by ring. rewrite Rabs_R0. exact He.
Qed.

Theorem matrix_cv_right_product : forall U L B,
  matrix_cv U L -> matrix_cv (fun n => mul2 (U n) B) (mul2 L B).
Proof.
  intros U L B HC. apply matrix_cv_coordinates in HC.
  destruct HC as [H11 [H12 [H21 H22]]].
  apply coordinates_matrix_cv. unfold coordinate_cv, mul2; simpl.
  repeat split; apply CV_plus; apply CV_mult; auto using real_constant_cv.
Qed.

Theorem matrix_cv_left_product : forall U L B,
  matrix_cv U L -> matrix_cv (fun n => mul2 B (U n)) (mul2 B L).
Proof.
  intros U L B HC. apply matrix_cv_coordinates in HC.
  destruct HC as [H11 [H12 [H21 H22]]].
  apply coordinates_matrix_cv. unfold coordinate_cv, mul2; simpl.
  repeat split; apply CV_plus; apply CV_mult; auto using real_constant_cv.
Qed.

Theorem matrix_cv_trace : forall U L,
  matrix_cv U L -> Un_cv (fun n => trace2 (U n)) (trace2 L).
Proof.
  intros U L HC. apply matrix_cv_coordinates in HC.
  destruct HC as [H11 [H12 [H21 H22]]]. unfold trace2.
  apply CV_plus; assumption.
Qed.

Lemma geometric_matrix_segment : forall U C r,
  0 <= C -> 0 <= r < 1 ->
  (forall j, opnorm (sub2 (U (S j)) (U j)) <= C*r^j) ->
  forall n k, opnorm (sub2 (U (n+k)%nat) (U n)) <= C*r^n*geometric_sum r k.
Proof.
  intros U C r HC Hr Hstep n k. induction k as [|k IH].
  - simpl. rewrite Nat.add_0_r.
    assert (H0 : sub2 (U n) (U n) = zero2)
      by (destruct (U n); apply mat2_ext; unfold sub2, add2, scale2, zero2; simpl; ring).
    rewrite H0, opnorm_zero. nra.
  - replace (n+S k)%nat with (S (n+k)) by lia.
    eapply Rle_trans; [apply (opnorm_difference_triangle _ (U (n+k)%nat))|].
    pose proof (Hstep (n+k)%nat) as HS. rewrite pow_add in HS.
    rewrite geometric_sum_last. nra.
Qed.

Lemma geometric_matrix_tail : forall U C r,
  0 <= C -> 0 <= r < 1 ->
  (forall j, opnorm (sub2 (U (S j)) (U j)) <= C*r^j) ->
  forall n m, (n <= m)%nat ->
    opnorm (sub2 (U m) (U n)) <= (C/(1-r))*r^n.
Proof.
  intros U C r HC Hr HS n m Hnm.
  pose proof (geometric_matrix_segment U C r HC Hr HS n (m-n)) as H.
  replace (n+(m-n))%nat with m in H by lia.
  pose proof (geometric_sum_bound r (m-n) Hr) as HG.
  assert (Hpos : 0 <= C*r^n) by (apply Rmult_le_pos; auto; apply pow_le; lra).
  pose proof (Rmult_le_compat_l (C*r^n) _ _ Hpos HG).
  unfold Rdiv. nra.
Qed.

Theorem geometric_matrix_convergence : forall U C r,
  0 <= C -> 0 <= r < 1 ->
  (forall j, opnorm (sub2 (U (S j)) (U j)) <= C*r^j) ->
  { L : mat2 | matrix_cv U L /\
    forall n, opnorm (sub2 (U n) L) <= (C/(1-r))*r^n }.
Proof.
  intros U C r HC Hr HS.
  set (K := C/(1-r)).
  assert (HK : 0 <= K).
  { unfold K, Rdiv. apply Rmult_le_pos; [exact HC|].
    apply Rlt_le, Rinv_0_lt_compat; lra. }
  assert (HCauchy : matrix_cauchy U).
  { intros eps He.
    destruct (pow_lt_1_zero r ltac:(rewrite Rabs_right; lra)
      (eps/(2*(K+1))) ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
    exists N. intros n m Hn Hm.
    pose proof (geometric_matrix_tail U C r HC Hr HS N n Hn) as HNn.
    pose proof (geometric_matrix_tail U C r HC Hr HS N m Hm) as HNm.
    change (opnorm (sub2 (U n) (U N)) <= K*r^N) in HNn.
    change (opnorm (sub2 (U m) (U N)) <= K*r^N) in HNm.
    pose proof (opnorm_difference_triangle (U n) (U N) (U m)) as HT.
    rewrite (opnorm_difference_symmetric (U N) (U m)) in HT.
    specialize (HN N (Nat.le_refl N)).
    rewrite Rabs_right in HN by (apply Rle_ge, pow_le; lra).
    assert (Hsmall : 2*(K+1)*r^N < eps).
    { pose proof (Rmult_lt_compat_l (2*(K+1)) _ _ ltac:(lra) HN) as HM.
      replace (2*(K+1)*(eps/(2*(K+1)))) with eps in HM by (field; lra).
      exact HM. }
    pose proof (pow_le r N ltac:(lra)). nra. }
  destruct (euclidean_matrix_complete U HCauchy) as [L HL]. exists L. split; auto.
  intro n. rewrite opnorm_difference_symmetric.
  apply (matrix_limit_closed_bound U L (U n) _ n HL).
  intros m Hm. apply geometric_matrix_tail; auto.
Qed.

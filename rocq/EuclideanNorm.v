From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra FiberProducts.
Open Scope R_scope.

(* The actual induced Euclidean operator norm, constructed as a supremum.
   In particular the matrix_norm interface in FiberProducts is inhabited
   by the norm used in the paper, rather than by a postulated instance. *)
Definition evec := (R*R)%type.
Definition evadd (u v : evec) : evec := (fst u+fst v, snd u+snd v).
Definition evscale (r : R) (v : evec) : evec := (r*fst v,r*snd v).
Definition enorm (v : evec) := sqrt (fst v*fst v+snd v*snd v).
Definition action (A : mat2) (v : evec) : evec :=
  (a11 A*fst v+a12 A*snd v, a21 A*fst v+a22 A*snd v).

Lemma enorm_nonnegative : forall v, 0 <= enorm v.
Proof. intro v; apply sqrt_pos. Qed.
Lemma enorm_squared : forall v,
  enorm v*enorm v = fst v*fst v+snd v*snd v.
Proof.
  intros [x y]. unfold enorm; simpl.
  apply sqrt_sqrt. nra.
Qed.
Lemma enorm_zero : enorm (0,0) = 0.
Proof. unfold enorm; simpl. replace (0*0+0*0) with 0 by ring. apply sqrt_0. Qed.
Lemma enorm_unit : enorm (1,0) = 1.
Proof. unfold enorm; simpl. replace (1*1+0*0) with 1 by ring. apply sqrt_1. Qed.
Lemma enorm_definite : forall v, enorm v = 0 -> v = (0,0).
Proof.
  intros [x y] H. pose proof (enorm_squared (x,y)) as Hsq.
  simpl in Hsq. rewrite H in Hsq.
  assert (x=0) by nra. assert (y=0) by nra. subst; reflexivity.
Qed.

Lemma enorm_scale : forall r v, enorm (evscale r v) = Rabs r*enorm v.
Proof.
  intros r [x y]. unfold enorm, evscale; simpl.
  replace (r*x*(r*x)+r*y*(r*y)) with ((r*r)*(x*x+y*y)) by ring.
  rewrite sqrt_mult; try nra.
  replace (sqrt (r*r)) with (Rabs r).
  - reflexivity.
  - symmetry. apply sqrt_Rsqr_abs.
Qed.

Lemma enorm_triangle : forall u v,
  enorm (evadd u v) <= enorm u+enorm v.
Proof.
  intros [x y] [a b].
  pose proof (sqrt_cauchy x y a b) as Hc.
  change (x*a+y*b <= enorm (x,y)*enorm (a,b)) in Hc.
  pose proof (enorm_squared (x,y)) as Hx.
  pose proof (enorm_squared (a,b)) as Ha.
  pose proof (enorm_squared (evadd (x,y) (a,b))) as Hsum.
  pose proof (enorm_nonnegative (x,y)).
  pose proof (enorm_nonnegative (a,b)).
  pose proof (enorm_nonnegative (evadd (x,y) (a,b))).
  unfold evadd in *. simpl fst in *. simpl snd in *. nra.
Qed.

Lemma abs_square : forall x, Rabs x*Rabs x = x*x.
Proof. intro x. pose proof (Rsqr_abs x); unfold Rsqr in *; lra. Qed.

Lemma enorm_coordinates : forall x y,
  Rabs x <= enorm (x,y) /\ Rabs y <= enorm (x,y).
Proof.
  intros x y. pose proof (enorm_squared (x,y)) as Hsq. simpl in Hsq.
  pose proof (enorm_nonnegative (x,y)).
  pose proof (Rabs_pos x). pose proof (Rabs_pos y).
  pose proof (abs_square x). pose proof (abs_square y).
  split; nra.
Qed.

Lemma enorm_l1_bound : forall x y, enorm (x,y) <= Rabs x+Rabs y.
Proof.
  intros x y. pose proof (enorm_squared (x,y)) as Hsq. simpl in Hsq.
  pose proof (enorm_nonnegative (x,y)).
  pose proof (Rabs_pos x). pose proof (Rabs_pos y).
  pose proof (abs_square x). pose proof (abs_square y).
  pose proof (Rmult_le_pos (Rabs x) (Rabs y) (Rabs_pos x) (Rabs_pos y)). nra.
Qed.

Definition entry_bound (A : mat2) := Rabs (a11 A)+Rabs (a12 A)+Rabs (a21 A)+Rabs (a22 A).
Lemma entry_bound_nonnegative : forall A, 0 <= entry_bound A.
Proof.
  intros [a b c d]. unfold entry_bound; simpl.
  pose proof (Rabs_pos a). pose proof (Rabs_pos b).
  pose proof (Rabs_pos c). pose proof (Rabs_pos d). lra.
Qed.

Lemma action_entry_bound : forall A v,
  enorm (action A v) <= entry_bound A*enorm v.
Proof.
  intros [a b c d] [x y]. unfold action; simpl.
  eapply Rle_trans; [apply enorm_l1_bound|].
  pose proof (Rabs_triang (a*x) (b*y)). pose proof (Rabs_triang (c*x) (d*y)).
  rewrite !Rabs_mult in *.
  destruct (enorm_coordinates x y) as [Hx Hy].
  assert (Ha : Rabs a*Rabs x <= Rabs a*enorm (x,y))
    by (apply Rmult_le_compat_l; auto using Rabs_pos).
  assert (Hb : Rabs b*Rabs y <= Rabs b*enorm (x,y))
    by (apply Rmult_le_compat_l; auto using Rabs_pos).
  assert (Hc : Rabs c*Rabs x <= Rabs c*enorm (x,y))
    by (apply Rmult_le_compat_l; auto using Rabs_pos).
  assert (Hd : Rabs d*Rabs y <= Rabs d*enorm (x,y))
    by (apply Rmult_le_compat_l; auto using Rabs_pos).
  unfold entry_bound; simpl. nra.
Qed.

Definition ball_image (A : mat2) (r : R) :=
  exists v, enorm v <= 1 /\ r = enorm (action A v).

Lemma ball_image_nonempty : forall A, exists r, ball_image A r.
Proof. intro A. exists (enorm (action A (0,0))), (0,0). split; [rewrite enorm_zero; lra|reflexivity]. Qed.
Lemma ball_image_bounded : forall A, bound (ball_image A).
Proof.
  intro A. exists (entry_bound A). intros r [v [Hv Hr]]. subst r.
  eapply Rle_trans; [apply action_entry_bound|].
  pose proof (entry_bound_nonnegative A). nra.
Qed.

Definition opnorm (A : mat2) :=
  proj1_sig (completeness (ball_image A) (ball_image_bounded A) (ball_image_nonempty A)).
Lemma opnorm_lub : forall A, is_lub (ball_image A) (opnorm A).
Proof. intro A; exact (proj2_sig (completeness _ (ball_image_bounded A) (ball_image_nonempty A))). Qed.

Lemma opnorm_lower : forall A v, enorm v <= 1 -> enorm (action A v) <= opnorm A.
Proof.
  intros A v Hv. apply (proj1 (opnorm_lub A)). exists v. auto.
Qed.
Lemma opnorm_upper : forall A c,
  (forall v, enorm v <= 1 -> enorm (action A v) <= c) -> opnorm A <= c.
Proof.
  intros A c H. apply (proj2 (opnorm_lub A)). intros r [v [Hv Hr]]. subst; auto.
Qed.

Lemma action_zero : forall A, action A (0,0) = (0,0).
Proof. intros []; unfold action; simpl; f_equal; ring. Qed.
Lemma opnorm_nonnegative : forall A, 0 <= opnorm A.
Proof.
  intro A. pose proof (opnorm_lower A (0,0) ltac:(rewrite enorm_zero; lra)) as H.
  rewrite action_zero, enorm_zero in H. exact H.
Qed.
Lemma action_identity : forall v, action id2 v = v.
Proof. intros [x y]; unfold action, id2; simpl; f_equal; ring. Qed.
Lemma action_product : forall A B v, action (mul2 A B) v = action A (action B v).
Proof. intros [] [] [x y]; unfold action, mul2; simpl; f_equal; ring. Qed.
Lemma action_add : forall A B v, action (add2 A B) v = evadd (action A v) (action B v).
Proof. intros [] [] [x y]; unfold action, add2, evadd; simpl; f_equal; ring. Qed.
Lemma action_vector_scale : forall A r v, action A (evscale r v) = evscale r (action A v).
Proof. intros [] r [x y]; unfold action, evscale; simpl; f_equal; ring. Qed.
Lemma action_matrix_scale : forall A r v, action (scale2 r A) v = evscale r (action A v).
Proof. intros [] r [x y]; unfold action, scale2, evscale; simpl; f_equal; ring. Qed.

Theorem opnorm_action_bound : forall A v,
  enorm (action A v) <= opnorm A*enorm v.
Proof.
  intros A v. destruct (Req_dec (enorm v) 0) as [Hz|Hz].
  - pose proof (enorm_definite v Hz) as Hv. subst v.
    rewrite action_zero, !enorm_zero. nra.
  - pose proof (enorm_nonnegative v) as Hvnonneg.
    assert (Hv : 0 < enorm v) by lra.
    assert (Hunit : enorm (evscale (/enorm v) v) = 1).
    { rewrite enorm_scale, Rabs_right; [field; exact Hz|].
      apply Rle_ge, Rlt_le, Rinv_0_lt_compat; exact Hv. }
    pose proof (opnorm_lower A (evscale (/enorm v) v) ltac:(rewrite Hunit; lra)) as H.
    rewrite action_vector_scale, enorm_scale, Rabs_right in H;
      [|apply Rle_ge, Rlt_le, Rinv_0_lt_compat; exact Hv].
    apply (Rmult_le_reg_l (/enorm v)); [apply Rinv_0_lt_compat; exact Hv|].
    replace (/enorm v*(opnorm A*enorm v)) with (opnorm A) by (field; exact Hz).
    exact H.
Qed.

Lemma opnorm_identity : opnorm id2 = 1.
Proof.
  apply Rle_antisym.
  - apply opnorm_upper. intros v Hv. rewrite action_identity. exact Hv.
  - pose proof (opnorm_lower id2 (1,0) ltac:(rewrite enorm_unit; lra)) as H.
    rewrite action_identity, enorm_unit in H. exact H.
Qed.
Lemma opnorm_zero : opnorm zero2 = 0.
Proof.
  apply Rle_antisym; [|apply opnorm_nonnegative]. apply opnorm_upper.
  intros [x y] Hv. unfold action, zero2; simpl.
  replace (0*x+0*y) with 0 by ring. rewrite enorm_zero. lra.
Qed.

Theorem opnorm_submultiplicative : forall A B,
  opnorm (mul2 A B) <= opnorm A*opnorm B.
Proof.
  intros A B. apply opnorm_upper. intros v Hv. rewrite action_product.
  eapply Rle_trans; [apply opnorm_action_bound|].
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [apply opnorm_nonnegative|apply opnorm_action_bound].
  - pose proof (opnorm_nonnegative A). pose proof (opnorm_nonnegative B).
    assert (0 <= opnorm A*opnorm B) by (apply Rmult_le_pos; assumption). nra.
Qed.
Theorem opnorm_subadditive : forall A B,
  opnorm (add2 A B) <= opnorm A+opnorm B.
Proof.
  intros A B. apply opnorm_upper. intros v Hv. rewrite action_add.
  eapply Rle_trans; [apply enorm_triangle|].
  pose proof (opnorm_action_bound A v). pose proof (opnorm_action_bound B v).
  pose proof (opnorm_nonnegative A). pose proof (opnorm_nonnegative B).
  assert (opnorm A*enorm v <= opnorm A) by nra.
  assert (opnorm B*enorm v <= opnorm B) by nra. lra.
Qed.

Definition euclidean_matrix_norm : matrix_norm :=
  {| mnorm := opnorm;
     mnorm_nonnegative := opnorm_nonnegative;
     mnorm_identity := opnorm_identity;
     mnorm_zero := opnorm_zero;
     mnorm_submultiplicative := opnorm_submultiplicative;
     mnorm_subadditive := opnorm_subadditive |}.

Lemma opnorm_pointwise_bound : forall A c,
  0 <= c -> (forall v, enorm (action A v) <= c*enorm v) -> opnorm A <= c.
Proof.
  intros A c Hc H. apply opnorm_upper. intros v Hv.
  specialize (H v). nra.
Qed.

Lemma opnorm_scale_bound : forall r A, opnorm (scale2 r A) <= Rabs r*opnorm A.
Proof.
  intros r A. apply opnorm_upper. intros v Hv.
  rewrite action_matrix_scale, enorm_scale.
  pose proof (opnorm_lower A v Hv).
  apply Rmult_le_compat_l; auto using Rabs_pos.
Qed.

Lemma opnorm_quadratic_bound : forall A c,
  0 <= c ->
  (forall x y, (a11 A*x+a12 A*y)^2+(a21 A*x+a22 A*y)^2 <= c^2*(x*x+y*y)) ->
  opnorm A <= c.
Proof.
  intros A c Hc Hquad. apply opnorm_pointwise_bound; auto.
  intros [x y]. specialize (Hquad x y).
  pose proof (enorm_squared (action A (x,y))) as HA.
  pose proof (enorm_squared (x,y)) as Hv.
  pose proof (enorm_nonnegative (action A (x,y))).
  pose proof (enorm_nonnegative (x,y)).
  unfold action in *. simpl fst in *. simpl snd in *.
  assert (Hcn : 0 <= c*enorm (x,y)) by (apply Rmult_le_pos; assumption).
  nra.
Qed.

Definition frobenius (A : mat2) :=
  sqrt (a11 A*a11 A+a12 A*a12 A+a21 A*a21 A+a22 A*a22 A).

Theorem opnorm_frobenius_bound : forall A, opnorm A <= frobenius A.
Proof.
  intros [a b c d]. apply opnorm_quadratic_bound; [apply sqrt_pos|].
  intros x y. unfold frobenius; simpl.
  pose proof (Rsqr_sqrt (a*a+b*b+c*c+d*d) ltac:(nra)) as Hs.
  unfold Rsqr in Hs.
  pose proof (pow2_ge_0 (a*y-b*x)). pose proof (pow2_ge_0 (c*y-d*x)). nra.
Qed.

Lemma frobenius_adjugate : forall A, frobenius (adj2 A) = frobenius A.
Proof.
  intros [a b c d]. unfold frobenius, adj2; simpl.
  f_equal; ring.
Qed.

Theorem sparse_row_bound : forall a b e,
  0 <= e -> Rabs a <= e -> Rabs b <= e ->
  opnorm (Mat2 a b 0 0) <= (71/50)*e.
Proof.
  intros a b e He Ha Hb. eapply Rle_trans; [apply opnorm_frobenius_bound|].
  unfold frobenius; simpl.
  pose proof (sqrt_pos (a*a+b*b+0*0+0*0)) as Hs.
  pose proof (Rsqr_sqrt (a*a+b*b+0*0+0*0) ltac:(nra)) as Hsq.
  pose proof (Rabs_pos a). pose proof (Rabs_pos b).
  pose proof (abs_square a). pose proof (abs_square b).
  unfold Rsqr in Hsq. nra.
Qed.

Theorem sparse_adjugate_bound : forall a b e,
  0 <= e -> Rabs a <= e -> Rabs b <= e ->
  opnorm (adj2 (Mat2 a b 0 0)) <= (71/50)*e.
Proof.
  intros a b e He Ha Hb. eapply Rle_trans; [apply opnorm_frobenius_bound|].
  rewrite frobenius_adjugate. unfold frobenius; simpl.
  pose proof (sqrt_pos (a*a+b*b+0*0+0*0)) as Hs.
  pose proof (Rsqr_sqrt (a*a+b*b+0*0+0*0) ltac:(nra)) as Hsq.
  pose proof (Rabs_pos a). pose proof (Rabs_pos b).
  pose proof (abs_square a). pose proof (abs_square b).
  unfold Rsqr in Hsq. nra.
Qed.

Definition base_numerator := Mat2 10 (-1) 1 10.
Theorem base_numerator_bound : opnorm base_numerator <= 201/20.
Proof.
  apply opnorm_quadratic_bound; [lra|]. intros x y.
  unfold base_numerator; simpl. nra.
Qed.
Theorem base_adjugate_bound : opnorm (adj2 base_numerator) <= 201/20.
Proof.
  apply opnorm_quadratic_bound; [lra|]. intros x y.
  unfold adj2, base_numerator; simpl. nra.
Qed.

Lemma adj2_add : forall A B, adj2 (add2 A B) = add2 (adj2 A) (adj2 B).
Proof. intros [] []; apply mat2_ext; unfold adj2, add2; simpl; ring. Qed.
Lemma adj2_scale : forall r A, adj2 (scale2 r A) = scale2 r (adj2 A).
Proof. intros r []; apply mat2_ext; unfold adj2, scale2; simpl; ring. Qed.

Theorem orthogonal_enorm : forall A v, orthogonal2 A -> enorm (action A v) = enorm v.
Proof.
  intros [a b c d] [x y] H.
  pose proof (f_equal a11 H) as H11.
  pose proof (f_equal a12 H) as H12.
  pose proof (f_equal a22 H) as H22.
  unfold orthogonal2, mul2, transpose2, id2 in H11, H12, H22; simpl in H11, H12, H22.
  unfold enorm, action; simpl. f_equal.
  replace ((a*x+b*y)*(a*x+b*y)+(c*x+d*y)*(c*x+d*y)) with
    ((a*a+c*c)*x*x+2*(a*b+c*d)*x*y+(b*b+d*d)*y*y) by ring.
  rewrite H11, H12, H22. ring.
Qed.

Theorem orthogonal_opnorm : forall A, orthogonal2 A -> opnorm A = 1.
Proof.
  intros A HA. apply Rle_antisym.
  - apply opnorm_upper. intros v Hv. rewrite (orthogonal_enorm A v HA). exact Hv.
  - pose proof (opnorm_lower A (1,0) ltac:(rewrite enorm_unit; lra)) as H.
    rewrite (orthogonal_enorm A (1,0) HA), enorm_unit in H. exact H.
Qed.

Definition sign_conjugate (A : mat2) := Mat2 (a11 A) (-a12 A) (-a21 A) (a22 A).
Definition sign_vector (v : evec) : evec := (fst v,-snd v).

Lemma sign_vector_enorm : forall v, enorm (sign_vector v) = enorm v.
Proof. intros [x y]; unfold enorm, sign_vector; simpl; f_equal; ring. Qed.
Lemma sign_conjugate_action : forall A v,
  action (sign_conjugate A) v = sign_vector (action A (sign_vector v)).
Proof. intros [] [x y]; unfold action, sign_conjugate, sign_vector; simpl; f_equal; ring. Qed.
Lemma sign_conjugate_involution : forall A, sign_conjugate (sign_conjugate A) = A.
Proof. intros []; apply mat2_ext; unfold sign_conjugate; simpl; ring. Qed.

Theorem sign_conjugate_opnorm : forall A, opnorm (sign_conjugate A) = opnorm A.
Proof.
  assert (Hle : forall A, opnorm (sign_conjugate A) <= opnorm A).
  { intro A. apply opnorm_pointwise_bound; [apply opnorm_nonnegative|].
    intro v. rewrite sign_conjugate_action, sign_vector_enorm.
    pose proof (opnorm_action_bound A (sign_vector v)) as H.
    rewrite sign_vector_enorm in H. exact H. }
  intro A. apply Rle_antisym; [apply Hle|].
  pose proof (Hle (sign_conjugate A)). rewrite sign_conjugate_involution in H. exact H.
Qed.

Lemma sign_conjugate_sub : forall A B,
  sub2 (sign_conjugate A) (sign_conjugate B) = sign_conjugate (sub2 A B).
Proof. intros [] []; apply mat2_ext; unfold sign_conjugate, sub2, add2, scale2; simpl; ring. Qed.
Lemma sign_conjugate_adjugate : forall A,
  adj2 (sign_conjugate A) = sign_conjugate (adj2 A).
Proof. intros []; apply mat2_ext; unfold sign_conjugate, adj2; simpl; ring. Qed.

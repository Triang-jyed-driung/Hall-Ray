From Stdlib Require Import Reals Psatz Lia Arith ClassicalChoice FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  ConcreteCocycle DefectLimit EllipticConjugacy EllipticPowers EllipticRecurrence
  PeriodicReturns Matrix3Limits CompactMatrices.
Open Scope R_scope.

Lemma scalar_cv_inverse : forall u l,
  Un_cv u l -> l <> 0 -> Un_cv (fun n => /u n) (/l).
Proof.
  intros u l Hu Hl. apply continuity_seq; [apply continuity_pt_inv; [reg|exact Hl]|exact Hu].
Qed.
Lemma scalar_cv_square_root : forall u l,
  Un_cv u l -> 0 <= l -> Un_cv (fun n => sqrt (u n)) (sqrt l).
Proof.
  intros u l Hu Hl. apply continuity_seq; [apply continuity_pt_sqrt; exact Hl|exact Hu].
Qed.
Lemma scalar_cv_eventual_agreement : forall u v l,
  Un_cv v l -> (exists N, forall n, (N <= n)%nat -> u n = v n) -> Un_cv u l.
Proof.
  intros u v l Hv [N Hsame] eps He. destruct (Hv eps He) as [I HI].
  exists (Nat.max N I); intros n Hn. rewrite Hsame by lia. apply HI; lia.
Qed.
Lemma matrix_cv_eventual_agreement : forall U V L,
  matrix_cv V L -> (exists N, forall n, (N <= n)%nat -> U n = V n) -> matrix_cv U L.
Proof.
  intros U V L HV [N Hsame] eps He. destruct (HV eps He) as [I HI].
  exists (Nat.max N I); intros n Hn. rewrite Hsame by lia. apply HI; lia.
Qed.

Theorem elliptic_basis_sequence_limit : forall U A,
  matrix_cv U A -> Rabs (trace2 A) < 2 -> 0 < a21 A ->
  matrix_cv (fun n => elliptic_basis (U n)) (elliptic_basis A).
Proof.
  intros U A HU Hell Hc.
  pose proof (elliptic_sine_positive A Hell) as Hs.
  pose proof (elliptic_scale_positive A Hell Hc) as Hp.
  pose proof (matrix_cv_trace U A HU) as Htrace.
  apply matrix_cv_coordinates in HU. destruct HU as (H11&H12&H21&H22).
  assert (Hcos : Un_cv (fun n => elliptic_cosine (U n)) (elliptic_cosine A)).
  { unfold elliptic_cosine, Rdiv; scalar_cv_algebra. }
  assert (Hsin : Un_cv (fun n => elliptic_sine (U n)) (elliptic_sine A)).
  { unfold elliptic_sine. apply scalar_cv_square_root.
    - replace (fun n => 1-elliptic_cosine (U n)^2) with
        (fun n => 1-elliptic_cosine (U n)*elliptic_cosine (U n)) by
        (apply functional_extensionality; intro n; simpl; ring).
      replace (1-elliptic_cosine A^2) with (1-elliptic_cosine A*elliptic_cosine A) by (simpl; ring).
      scalar_cv_algebra.
    - pose proof (elliptic_cosine_range A Hell); nra. }
  assert (Hscale : Un_cv (fun n => elliptic_scale (U n)) (elliptic_scale A)).
  { unfold elliptic_scale. apply scalar_cv_square_root.
    - unfold Rdiv. apply CV_mult; [exact Hsin|apply scalar_cv_inverse; [exact H21|lra]].
    - apply Rlt_le, Rdiv_lt_0_compat; assumption. }
  pose proof (scalar_cv_inverse _ _ Hsin ltac:(lra)) as Hsinv.
  pose proof (scalar_cv_inverse _ _ Hscale ltac:(lra)) as Hpinv.
  apply coordinates_matrix_cv. unfold coordinate_cv, elliptic_basis; simpl.
  unfold Rdiv. repeat split; scalar_cv_algebra.
Qed.

Lemma matrix_cv_sign_conjugate : forall U A,
  matrix_cv U A -> matrix_cv (fun n => sign_conjugate (U n)) (sign_conjugate A).
Proof.
  intros U A HU. apply matrix_cv_coordinates in HU. destruct HU as (H11&H12&H21&H22).
  apply coordinates_matrix_cv. unfold coordinate_cv, sign_conjugate; simpl.
  repeat split; scalar_cv_algebra.
Qed.

Theorem oriented_elliptic_basis_sequence_limit : forall U A,
  matrix_cv U A -> det2 A = 1 -> Rabs (trace2 A) < 2 ->
  matrix_cv (fun n => oriented_elliptic_basis (U n)) (oriented_elliptic_basis A).
Proof.
  intros U A HU HA Hell.
  pose proof (matrix_cv_coordinates U A HU) as Hcoords.
  destruct Hcoords as (H11&H12&H21&H22).
  pose proof (elliptic_lower_left_nonzero A HA Hell) as Hnz.
  unfold oriented_elliptic_basis at 2. destruct (Rlt_dec 0 (a21 A)) as [Hpos|Hneg].
  - apply (matrix_cv_eventual_agreement _ (fun n => elliptic_basis (U n))).
    + apply elliptic_basis_sequence_limit; assumption.
    + destruct (H21 (a21 A/2) ltac:(lra)) as [N HN]. exists N; intros n Hn.
      specialize (HN n Hn); unfold Rdist in HN; apply Rabs_def2 in HN.
      unfold oriented_elliptic_basis; destruct (Rlt_dec 0 (a21 (U n))); [reflexivity|lra].
  - apply (matrix_cv_eventual_agreement _ (fun n => sign_conjugate (elliptic_basis (sign_conjugate (U n))))).
    + apply matrix_cv_sign_conjugate, elliptic_basis_sequence_limit.
      * apply matrix_cv_sign_conjugate; exact HU.
      * rewrite sign_conjugate_trace; exact Hell.
      * unfold sign_conjugate; simpl; lra.
    + destruct (H21 (-a21 A/2) ltac:(lra)) as [N HN]. exists N; intros n Hn.
      specialize (HN n Hn); unfold Rdist in HN; apply Rabs_def2 in HN.
      unfold oriented_elliptic_basis; destruct (Rlt_dec 0 (a21 (U n))); [lra|reflexivity].
Qed.

Lemma finite_matrix_norm_bound : forall U N,
  exists M, 0 <= M /\ forall n, (n < N)%nat -> opnorm (U n) <= M.
Proof.
  intros U N. induction N as [|N [M [HM Hb]]].
  - exists 0; split; [lra|intros; lia].
  - exists (M+opnorm (U N)); split; [pose proof (opnorm_nonnegative (U N)); lra|].
    intros n Hn. destruct (Nat.eq_dec n N) as [Hsame|Hdiff].
    + subst n; lra.
    + specialize (Hb n ltac:(lia)); pose proof (opnorm_nonnegative (U N)); lra.
Qed.

Theorem convergent_matrix_norm_bounded : forall U A,
  matrix_cv U A -> exists M, 0 < M /\ forall n, opnorm (U n) <= M.
Proof.
  intros U A HU. destruct (HU 1 ltac:(lra)) as [N HN].
  destruct (finite_matrix_norm_bound U N) as [M [HM Hb]].
  exists (M+opnorm A+1); split; [pose proof (opnorm_nonnegative A); lra|]. intros n.
  destruct (lt_dec n N) as [Hsmall|Hlarge].
  - specialize (Hb n Hsmall); pose proof (opnorm_nonnegative A); lra.
  - specialize (HN n ltac:(lia)).
    rewrite (matrix_difference_decomposition (U n) A).
    pose proof (opnorm_subadditive (sub2 (U n) A) A); lra.
Qed.

Definition elliptic_circle A R := mul2
  (mul2 (oriented_elliptic_basis A) R) (adj2 (oriented_elliptic_basis A)).
Definition in_elliptic_circle A E := exists R,
  det2 R = 1 /\ orthogonal2 R /\ E = elliptic_circle A R.

Theorem elliptic_circle_sequence_limit : forall U A R Q,
  matrix_cv U A -> det2 A = 1 -> Rabs (trace2 A) < 2 -> matrix_cv R Q ->
  matrix_cv (fun n => elliptic_circle (U n) (R n)) (elliptic_circle A Q).
Proof.
  intros U A R Q HU HA Hell HR. unfold elliptic_circle.
  pose proof (oriented_elliptic_basis_sequence_limit U A HU HA Hell) as HG.
  apply matrix_cv_product; [apply matrix_cv_product; assumption|apply matrix_cv_adjugate; exact HG].
Qed.

Theorem elliptic_circles_uniformly_bounded : forall U A,
  matrix_cv U A -> det2 A = 1 -> Rabs (trace2 A) < 2 ->
  exists M, 0 < M /\ forall n E, in_elliptic_circle (U n) E -> opnorm E <= M.
Proof.
  intros U A HU HA Hell.
  pose proof (oriented_elliptic_basis_sequence_limit U A HU HA Hell) as HG.
  destruct (convergent_matrix_norm_bounded _ _ HG) as [C [HC Hb]].
  destruct (convergent_matrix_norm_bounded _ _ (matrix_cv_adjugate _ _ HG)) as [D [HD Hd]].
  exists (C*D); split; [nra|]. intros n E [R [HRd [HRo HE]]]. subst E; unfold elliptic_circle.
  pose proof (opnorm_submultiplicative (mul2 (oriented_elliptic_basis (U n)) R)
    (adj2 (oriented_elliptic_basis (U n)))) as H1.
  pose proof (opnorm_submultiplicative (oriented_elliptic_basis (U n)) R) as H2.
  rewrite (orthogonal_opnorm R HRo) in H2.
  assert (Hprod : opnorm (mul2 (oriented_elliptic_basis (U n)) R)*
    opnorm (adj2 (oriented_elliptic_basis (U n))) <= C*D).
  { apply Rmult_le_compat; [apply opnorm_nonnegative|apply opnorm_nonnegative|specialize (Hb n); lra|apply Hd]. }
  lra.
Qed.

Theorem elliptic_circles_upper_limit : forall U A E,
  matrix_cv U A -> det2 A = 1 -> Rabs (trace2 A) < 2 ->
  (forall n, in_elliptic_circle (U n) (E n)) ->
  exists ns F, indices_tend_to_infinity ns /\ in_elliptic_circle A F /\ matrix_cv (fun i => E (ns i)) F.
Proof.
  intros U A E HU HA Hell HE.
  destruct (@choice nat mat2 (fun n R => det2 R = 1 /\ orthogonal2 R /\ E n = elliptic_circle (U n) R) HE)
    as [R HR].
  destruct (special_orthogonal_subsequence R ltac:(intro n; exact (proj1 (HR n)))
    ltac:(intro n; exact (proj1 (proj2 (HR n))))) as [ns [Q [Hns [HQd [HQo HQ]]]]].
  exists ns, (elliptic_circle A Q); split; [exact Hns|]. split.
  - exists Q; auto.
  - assert (Hsame : (fun i => E (ns i)) = (fun i => elliptic_circle (U (ns i)) (R (ns i)))).
    { apply functional_extensionality; intro i; exact (proj2 (proj2 (HR (ns i)))). }
    rewrite Hsame. apply elliptic_circle_sequence_limit; try assumption.
    exact (matrix_cv_subsequence _ _ ns HU Hns).
Qed.

Lemma conjugated_circle_product : forall G R Q,
  det2 G = 1 ->
  mul2 (mul2 (mul2 G R) (adj2 G)) (mul2 (mul2 G Q) (adj2 G)) =
    mul2 (mul2 G (mul2 R Q)) (adj2 G).
Proof.
  intros G R Q HG. rewrite !mul2_assoc.
  rewrite <- (mul2_assoc (adj2 G) G (mul2 Q (adj2 G))),
    (adjugate_left_identity G HG), mul2_id_left; reflexivity.
Qed.

Theorem elliptic_circle_unimodular : forall A E,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> in_elliptic_circle A E -> det2 E = 1.
Proof.
  intros A E HA Hell [R [HR [Ho HE]]]. rewrite HE. unfold elliptic_circle.
  pose proof (proj1 (oriented_elliptic_basis_valid A HA Hell)) as HG.
  rewrite !det2_mul, adjugate_determinant, HG, HR; ring.
Qed.

Theorem elliptic_circle_product : forall A E F,
  det2 A = 1 -> Rabs (trace2 A) < 2 ->
  in_elliptic_circle A E -> in_elliptic_circle A F -> in_elliptic_circle A (mul2 E F).
Proof.
  intros A E F HA Hell [R [HRd [HRo HE]]] [Q [HQd [HQo HF]]].
  exists (mul2 R Q); split; [rewrite det2_mul, HRd,HQd; ring|].
  split; [apply orthogonal_product; assumption|].
  rewrite HE,HF. unfold elliptic_circle. apply conjugated_circle_product.
  exact (proj1 (oriented_elliptic_basis_valid A HA Hell)).
Qed.

Theorem elliptic_return_in_circle : forall A,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> in_elliptic_circle A A.
Proof.
  intros A HA Hell.
  destruct (oriented_elliptic_basis_valid A HA Hell) as [HG HR].
  exists (mul2 (mul2 (adj2 (oriented_elliptic_basis A)) A) (oriented_elliptic_basis A)).
  split.
  - rewrite !det2_mul, adjugate_determinant, HG, HA; ring.
  - split; [exact HR|]. unfold elliptic_circle. symmetry; apply undo_conjugation; exact HG.
Qed.

Theorem elliptic_circle_right_return : forall A E,
  det2 A = 1 -> Rabs (trace2 A) < 2 ->
  in_elliptic_circle A E -> in_elliptic_circle A (mul2 E A).
Proof.
  intros A E HA Hell HE. apply elliptic_circle_product; try assumption.
  apply elliptic_return_in_circle; assumption.
Qed.

Theorem elliptic_circles_lower_limit : forall U A F,
  matrix_cv U A -> det2 A = 1 -> Rabs (trace2 A) < 2 -> in_elliptic_circle A F ->
  exists E, (forall n, in_elliptic_circle (U n) (E n)) /\ matrix_cv E F.
Proof.
  intros U A F HU HA Hell [R [HRd [HRo HF]]].
  exists (fun n => elliptic_circle (U n) R); split.
  - intro n; exists R; auto.
  - rewrite HF. apply elliptic_circle_sequence_limit; try assumption. apply matrix_cv_constant.
Qed.

Theorem elliptic_circle_closed_limit : forall U A E F,
  matrix_cv U A -> det2 A = 1 -> Rabs (trace2 A) < 2 ->
  (forall n, in_elliptic_circle (U n) (E n)) -> matrix_cv E F -> in_elliptic_circle A F.
Proof.
  intros U A E F HU HA Hell Hmember HE.
  destruct (elliptic_circles_upper_limit U A E HU HA Hell Hmember) as [ns [Q [Hns [HQ Hcv]]]].
  assert (Heq : F = Q) by (apply (matrix_cv_unique _ _ _ (matrix_cv_subsequence E F ns HE Hns) Hcv)).
  rewrite Heq; exact HQ.
Qed.

Theorem elliptic_circle_identity : forall A,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> in_elliptic_circle A id2.
Proof.
  intros A HA Hell. exists id2; split; [unfold det2,id2; simpl; ring|].
  split.
  - unfold orthogonal2; apply mat2_ext; unfold transpose2,mul2,id2; simpl; ring.
  - unfold elliptic_circle. rewrite mul2_id_right. symmetry; apply unimodular_right_inverse.
    exact (proj1 (oriented_elliptic_basis_valid A HA Hell)).
Qed.

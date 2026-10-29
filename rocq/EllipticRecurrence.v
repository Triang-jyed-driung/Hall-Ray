From Stdlib Require Import Reals Psatz Lia.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  DefectLimit EllipticConjugacy PeriodicReturns EllipticPowers ReturnInfiniteOrder RotationDensity.
Open Scope R_scope.

Lemma sign_conjugate_identity : sign_conjugate id2 = id2.
Proof. apply mat2_ext; unfold sign_conjugate, id2; simpl; ring. Qed.
Lemma sign_conjugate_determinant : forall A, det2 (sign_conjugate A) = det2 A.
Proof. intros []; unfold det2, sign_conjugate; simpl; ring. Qed.
Lemma sign_conjugate_trace : forall A, trace2 (sign_conjugate A) = trace2 A.
Proof. reflexivity. Qed.
Lemma sign_conjugate_transpose : forall A,
  transpose2 (sign_conjugate A) = sign_conjugate (transpose2 A).
Proof. reflexivity. Qed.
Lemma sign_conjugate_orthogonal : forall A, orthogonal2 A -> orthogonal2 (sign_conjugate A).
Proof.
  intros A H. unfold orthogonal2 in *.
  rewrite sign_conjugate_transpose, <- sign_conjugate_product, H, sign_conjugate_identity. reflexivity.
Qed.
Lemma sign_conjugation_identity : forall G A,
  mul2 (mul2 (adj2 (sign_conjugate G)) A) (sign_conjugate G) =
  sign_conjugate (mul2 (mul2 (adj2 G) (sign_conjugate A)) G).
Proof. intros [] []; apply mat2_ext; unfold mul2, adj2, sign_conjugate; simpl; ring. Qed.

(* A concrete SL2 basis on both connected elliptic components. *)
Definition oriented_elliptic_basis (A : mat2) :=
  if Rlt_dec 0 (a21 A) then elliptic_basis A
  else sign_conjugate (elliptic_basis (sign_conjugate A)).

Theorem oriented_elliptic_basis_valid : forall A,
  det2 A = 1 -> Rabs (trace2 A) < 2 ->
  det2 (oriented_elliptic_basis A) = 1 /\
  orthogonal2 (mul2 (mul2 (adj2 (oriented_elliptic_basis A)) A) (oriented_elliptic_basis A)).
Proof.
  intros A Hd Ht. unfold oriented_elliptic_basis. destruct (Rlt_dec 0 (a21 A)) as [Hc|Hc].
  - split; [apply elliptic_basis_unimodular; assumption|].
    rewrite (elliptic_conjugacy A Hd Ht Hc).
    exact (proj2 (elliptic_rotation_special_orthogonal A Ht)).
  - pose proof (elliptic_lower_left_nonzero A Hd Ht) as Hnz.
    assert (Hrd : det2 (sign_conjugate A) = 1) by (rewrite sign_conjugate_determinant; exact Hd).
    assert (Hrt : Rabs (trace2 (sign_conjugate A)) < 2) by (rewrite sign_conjugate_trace; exact Ht).
    assert (Hrc : 0 < a21 (sign_conjugate A)) by (unfold sign_conjugate; simpl; lra).
    split.
    + rewrite sign_conjugate_determinant. apply elliptic_basis_unimodular; assumption.
    + rewrite sign_conjugation_identity. apply sign_conjugate_orthogonal.
      rewrite (elliptic_conjugacy (sign_conjugate A) Hrd Hrt Hrc).
      exact (proj2 (elliptic_rotation_special_orthogonal _ Hrt)).
Qed.

Lemma any_conjugation_power_reconstruction : forall A G n, det2 G = 1 ->
  matrix_power A n = mul2 (mul2 G
    (matrix_power (mul2 (mul2 (adj2 G) A) G) n)) (adj2 G).
Proof.
  intros A G n HG. rewrite <- (conjugation_power G A n HG).
  symmetry; apply undo_conjugation; exact HG.
Qed.

Lemma conjugation_preserves_infinite_order : forall A G,
  det2 G = 1 -> (forall n, (0 < n)%nat -> matrix_power A n <> id2) ->
  forall n, (0 < n)%nat -> matrix_power (mul2 (mul2 (adj2 G) A) G) n <> id2.
Proof.
  intros A G HG Hinf n Hn Hfinite. apply (Hinf n Hn).
  rewrite (any_conjugation_power_reconstruction A G n HG), Hfinite, mul2_id_right.
  apply unimodular_right_inverse; exact HG.
Qed.

Lemma conjugated_difference_bound : forall G R S,
  opnorm (sub2 (mul2 (mul2 G R) (adj2 G)) (mul2 (mul2 G S) (adj2 G))) <=
    (opnorm G*opnorm (adj2 G))*opnorm (sub2 R S).
Proof.
  intros G R S. rewrite <- matrix_multiply_difference_left, <- matrix_multiply_difference_right.
  pose proof (opnorm_submultiplicative (mul2 G (sub2 R S)) (adj2 G)) as H1.
  pose proof (opnorm_submultiplicative G (sub2 R S)) as H2.
  pose proof (Rmult_le_compat_r (opnorm (adj2 G)) _ _ (opnorm_nonnegative _) H2). nra.
Qed.

Theorem conjugated_orthogonal_powers_dense_late : forall A G,
  det2 A = 1 -> det2 G = 1 ->
  orthogonal2 (mul2 (mul2 (adj2 G) A) G) ->
  (forall n, (0 < n)%nat -> matrix_power A n <> id2) ->
  forall S eps N, det2 S = 1 -> orthogonal2 S -> 0 < eps ->
  exists n, (N <= n)%nat /\
    opnorm (sub2 (matrix_power A n) (mul2 (mul2 G S) (adj2 G))) < eps.
Proof.
  intros A G HA HG HR Hinf S eps N HSd HSo He.
  set (C := opnorm G*opnorm (adj2 G)).
  assert (HC : 0 <= C) by (unfold C; apply Rmult_le_pos; apply opnorm_nonnegative).
  assert (Hdet : det2 (mul2 (mul2 (adj2 G) A) G) = 1).
  { rewrite !det2_mul, adjugate_determinant, HG, HA; ring. }
  destruct (special_orthogonal_powers_dense_late _ Hdet HR
    (conjugation_preserves_infinite_order A G HG Hinf) S (eps/(C+1)) N HSd HSo
    ltac:(apply Rdiv_lt_0_compat; lra)) as [n [Hn Hnear]].
  exists n. split; [exact Hn|]. rewrite (any_conjugation_power_reconstruction A G n HG).
  pose proof (conjugated_difference_bound G
    (matrix_power (mul2 (mul2 (adj2 G) A) G) n) S) as Hbound.
  change (opnorm (sub2
    (mul2 (mul2 G (matrix_power (mul2 (mul2 (adj2 G) A) G) n)) (adj2 G))
    (mul2 (mul2 G S) (adj2 G))) <= C*opnorm (sub2
      (matrix_power (mul2 (mul2 (adj2 G) A) G) n) S)) in Hbound.
  assert (HCbound : C*opnorm (sub2 (matrix_power (mul2 (mul2 (adj2 G) A) G) n) S) <= C*(eps/(C+1))).
  { apply Rmult_le_compat_l; [exact HC|lra]. }
  assert (Hfinal : C*(eps/(C+1)) < eps).
  { apply (Rmult_lt_reg_r (C+1)); [lra|].
    replace (C*(eps/(C+1))*(C+1)) with (C*eps) by (field; lra). nra. }
  lra.
Qed.

Theorem elliptic_powers_recurrent : forall A,
  det2 A = 1 -> Rabs (trace2 A) < 2 ->
  (forall n, (0 < n)%nat -> matrix_power A n <> id2) ->
  forall eps N, 0 < eps -> exists n, (N <= n)%nat /\
    opnorm (sub2 (matrix_power A n) id2) < eps.
Proof.
  intros A HA Ht Hinf eps N He.
  destruct (oriented_elliptic_basis_valid A HA Ht) as [HG HR].
  destruct (conjugated_orthogonal_powers_dense_late A (oriented_elliptic_basis A) HA HG HR Hinf
    id2 eps N (proj1 identity_special_orthogonal) (proj2 identity_special_orthogonal) He)
    as [n [Hn Hnear]].
  rewrite mul2_id_right, (unimodular_right_inverse _ HG) in Hnear.
  exists n; auto.
Qed.

Theorem periodic_return_recurrent : forall k,
  Rabs (trace2 (periodic_return k)) < 2 -> forall eps N,
  0 < eps -> exists n, (N <= n)%nat /\
    opnorm (sub2 (matrix_power (periodic_return k) n) id2) < eps.
Proof.
  intros k Hk eps N He.
  apply elliptic_powers_recurrent; auto using periodic_return_unimodular, periodic_return_infinite_order.
Qed.

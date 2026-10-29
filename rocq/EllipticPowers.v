From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  SymbolicCoding ConcreteCocycle SymbolicCocycle DefectLimit ConstantCoding
  EllipticConjugacy PeriodicReturns.
Open Scope R_scope.

Theorem conjugate_orthogonal_powers_bounded : forall A G,
  det2 G = 1 -> orthogonal2 (mul2 (mul2 (adj2 G) A) G) ->
  exists K, 0 < K /\ forall n, opnorm (matrix_power A n) <= K.
Proof.
  intros A G HG HR.
  exists (opnorm G*opnorm (adj2 G)+1). split.
  - pose proof (Rmult_le_pos (opnorm G) (opnorm (adj2 G))
      (opnorm_nonnegative G) (opnorm_nonnegative (adj2 G))). lra.
  - intro n.
    assert (Hrec : matrix_power A n = mul2
      (mul2 G (matrix_power (mul2 (mul2 (adj2 G) A) G) n)) (adj2 G)).
    { rewrite <- (conjugation_power G A n HG). symmetry; apply undo_conjugation; exact HG. }
    assert (Hrot : opnorm (matrix_power (mul2 (mul2 (adj2 G) A) G) n) = 1)
      by (apply orthogonal_opnorm, orthogonal_power; exact HR).
    rewrite Hrec.
    pose proof (opnorm_submultiplicative
      (mul2 G (matrix_power (mul2 (mul2 (adj2 G) A) G) n)) (adj2 G)) as H1.
    pose proof (opnorm_submultiplicative G
      (matrix_power (mul2 (mul2 (adj2 G) A) G) n)) as H2.
    rewrite Hrot in H2.
    pose proof (Rmult_le_compat_r (opnorm (adj2 G)) _ _ (opnorm_nonnegative _) H2). nra.
Qed.

Lemma sign_conjugate_product : forall A B,
  sign_conjugate (mul2 A B) = mul2 (sign_conjugate A) (sign_conjugate B).
Proof. intros [] []; apply mat2_ext; unfold sign_conjugate, mul2; simpl; ring. Qed.
Lemma sign_conjugate_power : forall A n,
  matrix_power (sign_conjugate A) n = sign_conjugate (matrix_power A n).
Proof.
  intros A n. induction n.
  - simpl; apply mat2_ext; unfold sign_conjugate, id2; simpl; ring.
  - change (mul2 (sign_conjugate A) (matrix_power (sign_conjugate A) n) =
      sign_conjugate (mul2 A (matrix_power A n))).
    rewrite IHn, sign_conjugate_product. reflexivity.
Qed.

Lemma elliptic_lower_left_nonzero : forall A,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> a21 A <> 0.
Proof.
  intros [a b c d] Hd Ht Hz.
  unfold det2, trace2 in *; simpl in *. apply Rabs_def2 in Ht.
  pose proof (pow2_ge_0 (a-d)). subst c. nra.
Qed.

Lemma positive_elliptic_powers_bounded : forall A,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> 0 < a21 A ->
  exists K, 0 < K /\ forall n, opnorm (matrix_power A n) <= K.
Proof.
  intros A Hd Ht Hc. apply (conjugate_orthogonal_powers_bounded A (elliptic_basis A)).
  - apply elliptic_basis_unimodular; assumption.
  - rewrite (elliptic_conjugacy A Hd Ht Hc).
    exact (proj2 (elliptic_rotation_special_orthogonal A Ht)).
Qed.

Theorem elliptic_powers_bounded : forall A,
  det2 A = 1 -> Rabs (trace2 A) < 2 ->
  exists K, 0 < K /\ forall n, opnorm (matrix_power A n) <= K.
Proof.
  intros A Hd Ht. pose proof (elliptic_lower_left_nonzero A Hd Ht) as Hnz.
  destruct (Rlt_dec 0 (a21 A)) as [Hpos|Hneg].
  - apply positive_elliptic_powers_bounded; assumption.
  - assert (Hdet : det2 (sign_conjugate A) = 1).
    { unfold det2, sign_conjugate in *; simpl in *; nra. }
    assert (Htrace : Rabs (trace2 (sign_conjugate A)) < 2).
    { change (Rabs (trace2 A) < 2). exact Ht. }
    assert (Hc : 0 < a21 (sign_conjugate A)) by (unfold sign_conjugate; simpl; lra).
    destruct (positive_elliptic_powers_bounded _ Hdet Htrace Hc) as [K [HK Hbound]].
    exists K. split; [exact HK|]. intro n. specialize (Hbound n).
    rewrite sign_conjugate_power, sign_conjugate_opnorm in Hbound. exact Hbound.
Qed.

Theorem opnorm_adjugate_bound : forall A, opnorm (adj2 A) <= 2*opnorm A.
Proof.
  intros [a b c d].
  pose proof (opnorm_frobenius_bound (adj2 (Mat2 a b c d))) as HB.
  rewrite frobenius_adjugate in HB.
  pose proof (opnorm_entries (Mat2 a b c d)) as HE.
  pose proof (opnorm_nonnegative (Mat2 a b c d)) as HN.
  pose proof (sqrt_pos (a*a+b*b+c*c+d*d)) as HS.
  pose proof (Rsqr_sqrt (a*a+b*b+c*c+d*d) ltac:(nra)) as HS2.
  pose proof (abs_square a). pose proof (abs_square b).
  pose proof (abs_square c). pose proof (abs_square d).
  pose proof (Rabs_pos a). pose proof (Rabs_pos b).
  pose proof (Rabs_pos c). pose proof (Rabs_pos d).
  unfold Rsqr in HS2. unfold frobenius in HB; simpl in HB, HE. nra.
Qed.

Lemma periodic_shift_by_cycles : forall n k j,
  shift_by (k*S n) (periodic_future n) j = periodic_future n j.
Proof.
  intros n k j. unfold shift_by, periodic_future.
  replace (k*S n+j)%nat with (j+k*S n)%nat by lia.
  rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Theorem periodic_product_remainder : forall n j,
  fiber_product j (periodic_future n) =
  mul2 (matrix_power (periodic_return n) (j/S n))
       (fiber_product (j mod S n) (periodic_future n)).
Proof.
  intros n j.
  assert (Hdecomp : (j = (j/S n)*S n+j mod S n)%nat).
  { pose proof (Nat.div_mod j (S n) ltac:(lia)). nia. }
  rewrite Hdecomp at 1. rewrite fiber_product_concatenation, periodic_cycle_products.
  f_equal. apply fiber_product_extensional. intro k. apply periodic_shift_by_cycles.
Qed.

(* The bounded lifted cocycle for every elliptic periodic return. *)
Theorem elliptic_periodic_fibers_bounded : forall n,
  Rabs (trace2 (periodic_return n)) < 2 -> exists K, 0 < K /\ forall j,
    opnorm (fiber_product j (periodic_future n))+
    opnorm (adj2 (fiber_product j (periodic_future n))) <= K.
Proof.
  intros n Hn.
  destruct (elliptic_powers_bounded (periodic_return n) (periodic_return_unimodular n) Hn)
    as [C [HC Hpowers]].
  exists (6*C*constant_power_bound+1). split.
  - pose proof constant_power_bound_nonnegative as Hbase.
    pose proof (Rmult_le_pos C constant_power_bound ltac:(lra) Hbase). nra.
  - intro j.
    assert (Hrem : (j mod S n <= n)%nat) by (pose proof (Nat.mod_upper_bound j (S n) ltac:(lia)); lia).
    pose proof (partial_period_uniform_bound n (j mod S n) Hrem) as Hr.
    assert (Hbound : opnorm (fiber_product j (periodic_future n)) <= 2*C*constant_power_bound).
    { rewrite periodic_product_remainder.
      eapply Rle_trans; [apply opnorm_submultiplicative|].
      replace (2*C*constant_power_bound) with (C*(2*constant_power_bound)) by ring.
      apply Rmult_le_compat; auto using opnorm_nonnegative. }
    pose proof (opnorm_adjugate_bound (fiber_product j (periodic_future n))). lra.
Qed.

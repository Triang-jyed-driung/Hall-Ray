From Stdlib Require Import Reals Psatz Lia Arith List.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  SymbolicCoding ConcreteCocycle SymbolicCocycle DefectLimit ConstantCoding DefectNoncommuting
  EllipticConjugacy DefectPhases.
Open Scope R_scope.
Import ListNotations.

(* The actual future (a^n b)^infinity and its full cocycle return. *)
Definition periodic_future (n : nat) : future :=
  fun k => if Nat.eqb (k mod (S n)) n then false else true.
Definition periodic_return (n : nat) := fiber_product (S n) (periodic_future n).
Definition phase_return (n : nat) := mul2 (matrix_power constant_rotation n) rotation_defect.

Lemma periodic_future_period : forall n k,
  periodic_future n (k+S n)%nat = periodic_future n k.
Proof.
  intros n k. unfold periodic_future.
  replace (k+S n)%nat with (k+1*(S n))%nat by lia.
  rewrite Nat.Div0.mod_add. reflexivity.
Qed.

Lemma periodic_defect_common_prefix : forall n,
  same_prefix (S n+n) (periodic_future n) (one_defect n).
Proof.
  intros n k Hk. unfold periodic_future, one_defect.
  destruct (lt_dec k (S n)) as [Hsmall|Hlarge].
  - rewrite Nat.mod_small by exact Hsmall. reflexivity.
  - assert (Hmod : (k mod S n = k-S n)%nat).
    { replace k with ((k-S n)+1*(S n))%nat at 1 by lia.
      rewrite Nat.Div0.mod_add. apply Nat.mod_small; lia. }
    rewrite Hmod.
    assert (Hneq1 : Nat.eqb (k-S n) n = false) by (apply Nat.eqb_neq; lia).
    assert (Hneq2 : Nat.eqb k n = false) by (apply Nat.eqb_neq; lia).
    rewrite Hneq1, Hneq2. reflexivity.
Qed.

Lemma matrix_multiply_difference_right : forall A B C,
  mul2 A (sub2 B C) = sub2 (mul2 A B) (mul2 A C).
Proof. intros [] [] []; apply mat2_ext; unfold mul2, sub2, add2, scale2; simpl; ring. Qed.
Lemma matrix_multiply_difference_left : forall A B C,
  mul2 (sub2 A B) C = sub2 (mul2 A C) (mul2 B C).
Proof. intros [] [] []; apply mat2_ext; unfold mul2, sub2, add2, scale2; simpl; ring. Qed.

Lemma unimodular_relative_difference : forall P T,
  det2 P = 1 -> sub2 T P = mul2 P (sub2 (mul2 (adj2 P) T) id2).
Proof.
  intros P T HP. rewrite matrix_multiply_difference_right, <- mul2_assoc.
  rewrite (unimodular_right_inverse P HP), mul2_id_left, mul2_id_right. reflexivity.
Qed.

Theorem symbolic_absolute_fiber_bound : forall n N w z,
  same_prefix (n+N) w z ->
  opnorm (sub2 (fiber_product n w) (fiber_product n z)) <= (11/10)^n*(1/600)^N.
Proof.
  intros n N w z Hsame.
  rewrite (unimodular_relative_difference (fiber_product n z) (fiber_product n w)
    (factor_product_unimodular n z)).
  eapply Rle_trans; [apply opnorm_submultiplicative|].
  apply Rmult_le_compat; auto using opnorm_nonnegative.
  - apply fiber_product_norm.
  - apply symbolic_uniform_fiber_bound. intros k Hk. symmetry; apply Hsame; exact Hk.
Qed.

Theorem periodic_return_unimodular : forall n, det2 (periodic_return n) = 1.
Proof. intro n; apply factor_product_unimodular. Qed.

Theorem periodic_defect_error_bound : forall n,
  opnorm (sub2 (periodic_return n) (defect_product n)) <= (11/10)^(S n)*(1/600)^n.
Proof.
  intro n. apply symbolic_absolute_fiber_bound. apply periodic_defect_common_prefix.
Qed.

Lemma matrix_power_adjugate : forall A n,
  adj2 (matrix_power A n) = matrix_power (adj2 A) n.
Proof.
  intros A n. induction n.
  - simpl. apply mat2_ext; unfold adj2, id2; simpl; ring.
  - change (adj2 (mul2 A (matrix_power A n)) = matrix_power (adj2 A) (S n)).
    rewrite adj2_mul, IHn, matrix_power_successor_right. reflexivity.
Qed.

Theorem defect_product_reconstruction : forall n,
  defect_product n = mul2 (matrix_power constant_return n) (defect_sequence n).
Proof.
  intro n. unfold defect_sequence. rewrite <- matrix_power_adjugate, <- mul2_assoc.
  rewrite unimodular_right_inverse.
  - rewrite mul2_id_left. reflexivity.
  - apply matrix_power_unimodular, cocycle_unimodular.
Qed.

Theorem periodic_return_asymptotic_bound : forall n,
  opnorm (sub2 (periodic_return n) (mul2 (matrix_power constant_return n) defect_limit)) <=
    2*(1/500)^n.
Proof.
  intro n.
  pose proof (periodic_defect_error_bound n) as HP.
  pose proof (defect_limit_error_bound n) as HD.
  assert (HA : opnorm constant_return <= 11/10).
  { pose proof (cocycle_bounds a_future) as HB. unfold constant_return. lra. }
  pose proof (matrix_power_norm constant_return (11/10) n ltac:(lra) HA) as HAn.
  assert (Htail : opnorm (sub2 (defect_product n) (mul2 (matrix_power constant_return n) defect_limit)) <=
    (11/10)^n*((1/5)*(1/600)^n)).
  { rewrite (defect_product_reconstruction n), <- matrix_multiply_difference_right.
    eapply Rle_trans; [apply opnorm_submultiplicative|].
    apply Rmult_le_compat; auto using opnorm_nonnegative. }
  pose proof (opnorm_difference_triangle (periodic_return n) (defect_product n)
    (mul2 (matrix_power constant_return n) defect_limit)) as HT.
  assert (Heq : (11/10)^(S n)*(1/600)^n+(11/10)^n*((1/5)*(1/600)^n) =
    (13/10)*(11/6000)^n).
  { simpl pow.
    replace (11/6000) with ((11/10)*(1/600)) by field.
    rewrite Rpow_mult_distr. field. }
  assert (Hsum : opnorm (sub2 (periodic_return n) (mul2 (matrix_power constant_return n) defect_limit)) <=
    (13/10)*(11/6000)^n) by (rewrite <- Heq; lra).
  pose proof (pow_incr (11/6000) (1/500) n ltac:(lra)) as Hpow.
  pose proof (pow_le (11/6000) n ltac:(lra)).
  pose proof (pow_le (1/500) n ltac:(lra)). nra.
Qed.

Lemma conjugation_power : forall G A n, det2 G = 1 ->
  mul2 (mul2 (adj2 G) (matrix_power A n)) G =
    matrix_power (mul2 (mul2 (adj2 G) A) G) n.
Proof.
  intros G A n HG. induction n.
  - simpl. rewrite mul2_id_right. apply adjugate_left_identity; exact HG.
  - change (mul2 (mul2 (adj2 G) (mul2 A (matrix_power A n))) G =
      mul2 (mul2 (mul2 (adj2 G) A) G) (matrix_power (mul2 (mul2 (adj2 G) A) G) n)).
    rewrite <- (conjugation_product G A (matrix_power A n) HG), IHn. reflexivity.
Qed.

Lemma trace_cyclic : forall A B, trace2 (mul2 A B) = trace2 (mul2 B A).
Proof. intros [] []; unfold trace2, mul2; simpl; ring. Qed.
Lemma trace_conjugation : forall G A, det2 G = 1 ->
  trace2 (mul2 (mul2 (adj2 G) A) G) = trace2 A.
Proof.
  intros G A HG. rewrite trace_cyclic, <- mul2_assoc.
  rewrite (unimodular_right_inverse G HG), mul2_id_left. reflexivity.
Qed.

Theorem asymptotic_model_phase_trace : forall n,
  trace2 (mul2 (matrix_power constant_return n) defect_limit) = trace2 (phase_return n).
Proof.
  intro n. rewrite <- (trace_conjugation constant_basis _ constant_basis_unimodular).
  rewrite <- (conjugation_product constant_basis (matrix_power constant_return n) defect_limit
    constant_basis_unimodular).
  rewrite (conjugation_power constant_basis constant_return n constant_basis_unimodular),
    constant_rotation_conjugacy. reflexivity.
Qed.

Theorem periodic_phase_trace_error : forall n,
  Rabs (trace2 (periodic_return n)-trace2 (phase_return n)) <= 4*(1/500)^n.
Proof.
  intro n. rewrite <- asymptotic_model_phase_trace, <- trace_subtraction.
  pose proof (trace_operator_bound (sub2 (periodic_return n)
    (mul2 (matrix_power constant_return n) defect_limit))) as HT.
  pose proof (periodic_return_asymptotic_bound n). lra.
Qed.

(* A fixed positive trace margin in the phase model eventually gives actual
   elliptic returns. This does not assume irrationality or phase density. *)
Theorem periodic_returns_eventually_elliptic_with_margin : forall delta,
  0 < delta -> exists N, forall n, (N <= n)%nat ->
  Rabs (trace2 (phase_return n)) <= 2-delta -> Rabs (trace2 (periodic_return n)) < 2.
Proof.
  intros delta Hd.
  destruct (pow_lt_1_zero (1/500) ltac:(rewrite Rabs_right; lra)
    (delta/4) ltac:(lra)) as [N HN].
  exists N. intros n Hn Hphase. specialize (HN n Hn).
  rewrite Rabs_right in HN by (apply Rle_ge, pow_le; lra).
  pose proof (periodic_phase_trace_error n) as HE.
  assert (HT : Rabs (trace2 (periodic_return n)) <=
    Rabs (trace2 (periodic_return n)-trace2 (phase_return n))+Rabs (trace2 (phase_return n))).
  { replace (trace2 (periodic_return n)) with
      ((trace2 (periodic_return n)-trace2 (phase_return n))+trace2 (phase_return n)) at 1 by ring.
    apply Rabs_triang. }
  lra.
Qed.

Lemma transpose_product : forall A B,
  transpose2 (mul2 A B) = mul2 (transpose2 B) (transpose2 A).
Proof. intros [] []; apply mat2_ext; unfold transpose2, mul2; simpl; ring. Qed.
Lemma orthogonal_product : forall A B,
  orthogonal2 A -> orthogonal2 B -> orthogonal2 (mul2 A B).
Proof.
  intros A B HA HB. unfold orthogonal2 in *.
  rewrite transpose_product, !mul2_assoc.
  rewrite <- (mul2_assoc (transpose2 A) A B), HA, mul2_id_left. exact HB.
Qed.
Lemma orthogonal_power : forall A n, orthogonal2 A -> orthogonal2 (matrix_power A n).
Proof.
  intros A n HA. induction n; simpl.
  - unfold orthogonal2; apply mat2_ext; unfold transpose2, mul2, id2; simpl; ring.
  - apply orthogonal_product; assumption.
Qed.

Theorem constant_power_reconstruction : forall n,
  matrix_power constant_return n =
  mul2 (mul2 constant_basis (matrix_power constant_rotation n)) (adj2 constant_basis).
Proof.
  intro n.
  pose proof (conjugation_power constant_basis constant_return n constant_basis_unimodular) as H.
  rewrite constant_rotation_conjugacy in H. rewrite <- H.
  symmetry; apply undo_conjugation, constant_basis_unimodular.
Qed.

Definition constant_power_bound := opnorm constant_basis*opnorm (adj2 constant_basis).
Lemma constant_power_bound_nonnegative : 0 <= constant_power_bound.
Proof. apply Rmult_le_pos; apply opnorm_nonnegative. Qed.

Theorem constant_powers_uniformly_bounded : forall n,
  opnorm (matrix_power constant_return n) <= constant_power_bound.
Proof.
  intro n. rewrite constant_power_reconstruction.
  assert (Hrot : opnorm (matrix_power constant_rotation n) = 1).
  { apply orthogonal_opnorm, orthogonal_power. exact (proj2 constant_rotation_special_orthogonal). }
  pose proof (opnorm_submultiplicative (mul2 constant_basis (matrix_power constant_rotation n))
    (adj2 constant_basis)) as H1.
  pose proof (opnorm_submultiplicative constant_basis (matrix_power constant_rotation n)) as H2.
  rewrite Hrot in H2.
  pose proof (Rmult_le_compat_r (opnorm (adj2 constant_basis)) _ _
    (opnorm_nonnegative _) H2). unfold constant_power_bound. nra.
Qed.

Lemma constant_future_product : forall n, fiber_product n a_future = matrix_power constant_return n.
Proof.
  induction n; [reflexivity|].
  change (mul2 constant_return (fiber_product n a_future) = mul2 constant_return (matrix_power constant_return n)).
  rewrite IHn. reflexivity.
Qed.

Lemma symbolic_relative_absolute_bound : forall n N w z,
  same_prefix (n+N) w z ->
  opnorm (sub2 (fiber_product n w) (fiber_product n z)) <=
    opnorm (fiber_product n z)*(1/600)^N.
Proof.
  intros n N w z Hsame.
  rewrite (unimodular_relative_difference (fiber_product n z) (fiber_product n w)
    (factor_product_unimodular n z)).
  eapply Rle_trans; [apply opnorm_submultiplicative|].
  apply Rmult_le_compat_l; [apply opnorm_nonnegative|].
  apply symbolic_uniform_fiber_bound. intros k Hk; symmetry; apply Hsame; exact Hk.
Qed.

Lemma periodic_initial_all_a : forall n, same_prefix n (periodic_future n) a_future.
Proof.
  intros n k Hk. unfold periodic_future, a_future.
  rewrite Nat.mod_small by lia.
  assert (Nat.eqb k n = false) as Hneq by (apply Nat.eqb_neq; lia).
  rewrite Hneq. reflexivity.
Qed.

Theorem partial_period_rotation_bound : forall n j, (j <= n)%nat ->
  opnorm (sub2 (fiber_product j (periodic_future n)) (matrix_power constant_return j)) <=
    constant_power_bound*(1/600)^(n-j).
Proof.
  intros n j Hjn.
  assert (Hsame : same_prefix (j+(n-j)) (periodic_future n) a_future).
  { replace (j+(n-j))%nat with n by lia. apply periodic_initial_all_a. }
  pose proof (symbolic_relative_absolute_bound j (n-j) _ _ Hsame) as H.
  rewrite constant_future_product in H.
  pose proof (constant_powers_uniformly_bounded j).
  eapply Rle_trans; [exact H|]. apply Rmult_le_compat_r; auto.
  apply pow_le; lra.
Qed.

Theorem partial_period_uniform_bound : forall n j, (j <= n)%nat ->
  opnorm (fiber_product j (periodic_future n)) <= 2*constant_power_bound.
Proof.
  intros n j Hjn.
  pose proof (partial_period_rotation_bound n j Hjn) as Herror.
  pose proof (constant_powers_uniformly_bounded j) as Hconst.
  pose proof constant_power_bound_nonnegative as Hpos.
  pose proof (pow_incr (1/600) 1 (n-j) ltac:(lra)) as Hpow.
  rewrite pow1 in Hpow.
  pose proof (Rmult_le_compat_l constant_power_bound _ _ Hpos Hpow) as HM.
  rewrite Rmult_1_r in HM.
  rewrite (matrix_difference_decomposition (fiber_product j (periodic_future n)) (matrix_power constant_return j)).
  pose proof (opnorm_subadditive (sub2 (fiber_product j (periodic_future n)) (matrix_power constant_return j))
    (matrix_power constant_return j)). lra.
Qed.

Lemma product_append : forall xs ys,
  product (xs++ys) = mul2 (product xs) (product ys).
Proof.
  induction xs as [|A xs IH]; intro ys; simpl.
  - rewrite mul2_id_left. reflexivity.
  - rewrite IH, mul2_assoc. reflexivity.
Qed.
Lemma factors_concatenation : forall n m w,
  factors (n+m) w = factors n w++factors m (shift_by n w).
Proof.
  induction n; intros m w; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.
Theorem fiber_product_concatenation : forall n m w,
  fiber_product (n+m) w = mul2 (fiber_product n w) (fiber_product m (shift_by n w)).
Proof.
  intros n m w. unfold fiber_product. rewrite factors_concatenation, product_append. reflexivity.
Qed.

Lemma cocycle_extensional : forall w z,
  (forall k, w k = z k) -> cocycle w = cocycle z.
Proof.
  intros w z H. unfold cocycle. rewrite (H O).
  assert (HC : coded (shift w) = coded (shift z)).
  { apply coded_extensional. intro k; apply H. }
  rewrite HC. reflexivity.
Qed.
Lemma fiber_product_extensional : forall n w z,
  (forall k, w k = z k) -> fiber_product n w = fiber_product n z.
Proof.
  induction n; intros w z H; [reflexivity|].
  change (mul2 (cocycle w) (fiber_product n (shift w)) = mul2 (cocycle z) (fiber_product n (shift z))).
  rewrite (cocycle_extensional w z H). f_equal. apply IHn. intro k; apply H.
Qed.

Theorem periodic_cycle_products : forall n k,
  fiber_product (k*S n) (periodic_future n) = matrix_power (periodic_return n) k.
Proof.
  intros n k. induction k; [reflexivity|].
  change (fiber_product (S n+k*S n) (periodic_future n) =
    mul2 (periodic_return n) (matrix_power (periodic_return n) k)).
  rewrite fiber_product_concatenation.
  assert (Hshift : fiber_product (k*S n) (shift_by (S n) (periodic_future n)) =
    fiber_product (k*S n) (periodic_future n)).
  { apply fiber_product_extensional. intro j. unfold shift_by.
    replace (S n+j)%nat with (j+S n)%nat by lia. apply periodic_future_period. }
  rewrite Hshift, IHk. reflexivity.
Qed.

Definition indices_tend_to_infinity (ns : nat -> nat) :=
  forall N, exists I, forall i, (I <= i)%nat -> (N <= ns i)%nat.

Theorem periodic_returns_elliptic_at_phase_limit : forall ns S,
  indices_tend_to_infinity ns ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  Rabs (trace2 (mul2 S rotation_defect)) < 2 ->
  exists I, forall i, (I <= i)%nat -> Rabs (trace2 (periodic_return (ns i))) < 2.
Proof.
  intros ns S Hns HC HS.
  set (delta := (2-Rabs (trace2 (mul2 S rotation_defect)))/2).
  assert (Hd : 0 < delta) by (unfold delta; lra).
  pose proof (matrix_cv_trace _ _ (matrix_cv_right_product _ _ rotation_defect HC)) as Htrace.
  destruct (Htrace delta Hd) as [I1 HI1].
  destruct (periodic_returns_eventually_elliptic_with_margin delta Hd) as [N HN].
  destruct (Hns N) as [I2 HI2].
  exists (Nat.max I1 I2). intros i Hi.
  specialize (HI1 i ltac:(lia)). specialize (HI2 i ltac:(lia)).
  apply HN; [exact HI2|].
  change (Rabs (trace2 (phase_return (ns i))-trace2 (mul2 S rotation_defect)) < delta) in HI1.
  assert (HT : Rabs (trace2 (phase_return (ns i))) <=
    Rabs (trace2 (phase_return (ns i))-trace2 (mul2 S rotation_defect))+
    Rabs (trace2 (mul2 S rotation_defect))).
  { replace (trace2 (phase_return (ns i))) with
      ((trace2 (phase_return (ns i))-trace2 (mul2 S rotation_defect))+trace2 (mul2 S rotation_defect)) at 1 by ring.
    apply Rabs_triang. }
  unfold delta in *. lra.
Qed.

From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import MatrixAlgebra ReturnIdentity ReturnBranches IntegralMatrices
  FiberProducts EuclideanNorm ConcreteCocycle SymbolicCoding SymbolicCocycle.
Open Scope R_scope.

Definition marking (s : bool) := if s then gamma_a else gamma_b.
Definition denominator (w : future) :=
  if w O then da (fst (coded (shift w))) (snd (coded (shift w)))
         else db (fst (coded (shift w))) (snd (coded (shift w))).
Definition inverse_roof (w : future) := /sqrt (denominator w).
Definition upper_row_last (w : future) := if w O then -10 else 10.
Definition unstable_frame (w : future) := hx (fst (coded w)) (snd (coded w)).
Definition triangular_step (w : future) :=
  triangular3 (denominator w) (-1) (upper_row_last w) (scale2 (inverse_roof w) (cocycle w)).

Fixpoint marking_product (n : nat) (w : future) :=
  match n with O => id3 | S k => mul3 (marking (w O)) (marking_product k (shift w)) end.
Fixpoint triangular_product (n : nat) (w : future) :=
  match n with O => id3 | S k => mul3 (triangular_step w) (triangular_product k (shift w)) end.
Fixpoint return_height (n : nat) (w : future) : R :=
  match n with O => 1 | S k => denominator w*return_height k (shift w) end.
Fixpoint return_scale (n : nat) (w : future) : R :=
  match n with O => 1 | S k => inverse_roof w*return_scale k (shift w) end.

Lemma denominator_bounds : forall w, 503/5 <= denominator w <= 507/5.
Proof.
  intro w. unfold denominator. destruct (w O);
    [apply da_bounds|apply db_bounds]; exact (coded_inside (shift w)).
Qed.
Lemma inverse_roof_bounds : forall w, 0 < inverse_roof w <= 1/10.
Proof.
  intro w. pose proof (denominator_bounds w).
  pose proof (inverse_sqrt_bound (denominator w) ltac:(lra)).
  split; [unfold inverse_roof; apply Rinv_0_lt_compat, sqrt_lt_R0; lra|tauto].
Qed.

Lemma inverse_root_square : forall d, 0 < d -> /sqrt d* /sqrt d = /d.
Proof.
  intros d Hd. pose proof (sqrt_lt_R0 d Hd) as Hs.
  pose proof (Rsqr_sqrt d ltac:(lra)) as Hsq. unfold Rsqr in Hsq.
  replace d with (sqrt d*sqrt d) at 3 by lra. field; lra.
Qed.
Lemma matrix_scale_composition : forall r s A, scale2 r (scale2 s A) = scale2 (r*s) A.
Proof. intros r s []; apply mat2_ext; unfold scale2; simpl; ring. Qed.
Lemma matrix_scale_product : forall r s A B,
  mul2 (scale2 r A) (scale2 s B) = scale2 (r*s) (mul2 A B).
Proof. intros r s [] []; apply mat2_ext; unfold scale2, mul2; simpl; ring. Qed.

Lemma normalized_schur_a : forall x y, in_U x y ->
  scale2 (/sqrt (da x y)) (normalized_a x y) = scale2 (/da x y) (numerator_a x y).
Proof.
  intros x y HU. unfold normalized_a.
  change (scale2 (/sqrt (da x y)) (scale2 (/sqrt (da x y)) (numerator_a x y)) =
    scale2 (/da x y) (numerator_a x y)).
  rewrite matrix_scale_composition, inverse_root_square; [reflexivity|].
  pose proof (da_bounds x y HU); lra.
Qed.
Lemma normalized_schur_b : forall x y, in_U x y ->
  scale2 (/sqrt (db x y)) (normalized_b x y) = scale2 (/db x y) (numerator_b x y).
Proof.
  intros x y HU. unfold normalized_b.
  change (scale2 (/sqrt (db x y)) (scale2 (/sqrt (db x y)) (numerator_b x y)) =
    scale2 (/db x y) (numerator_b x y)).
  rewrite matrix_scale_composition, inverse_root_square; [reflexivity|].
  pose proof (db_bounds x y HU); lra.
Qed.

Lemma projective_marked_step_a : forall x y, in_U x y ->
  mul3 (hx (phi_a1 x y) (phi_a2 x y)) gamma_a =
  mul3 (triangular3 (da x y) (-1) (-10) (scale2 (/da x y) (numerator_a x y))) (hx x y).
Proof.
  intros x y HU. assert (Hd : 101-x-10*y <> 0) by (pose proof (da_bounds x y HU); unfold da in *; lra).
  apply mat3_ext; unfold hx, mul3, phi_a1, phi_a2, gamma_a, triangular3, scale2, numerator_a, da;
    simpl; field; exact Hd.
Qed.
Lemma projective_marked_step_b : forall x y, in_U x y ->
  mul3 (hx (phi_b1 x y) (phi_b2 x y)) gamma_b =
  mul3 (triangular3 (db x y) (-1) 10 (scale2 (/db x y) (numerator_b x y))) (hx x y).
Proof.
  intros x y HU. assert (Hd : 101-x+10*y <> 0) by (pose proof (db_bounds x y HU); unfold db in *; lra).
  apply mat3_ext; unfold hx, mul3, phi_b1, phi_b2, gamma_b, triangular3, scale2, numerator_b, db;
    simpl; field; exact Hd.
Qed.

Theorem marked_cocycle_step : forall w,
  mul3 (unstable_frame w) (marking (w O)) = mul3 (triangular_step w) (unstable_frame (shift w)).
Proof.
  intro w. unfold unstable_frame at 1. rewrite (coded_recursion w).
  unfold triangular_step, denominator, inverse_roof, upper_row_last, cocycle, marking.
  unfold denominator. destruct (w O) eqn:Hs; unfold branch; simpl fst; simpl snd;
    unfold fiber_matrix; fold (cocycle w).
  - rewrite normalized_schur_a by exact (coded_inside (shift w)).
    apply projective_marked_step_a. exact (coded_inside (shift w)).
  - rewrite normalized_schur_b by exact (coded_inside (shift w)).
    apply projective_marked_step_b. exact (coded_inside (shift w)).
Qed.

Theorem marked_cocycle_product : forall n w,
  mul3 (unstable_frame w) (marking_product n w) =
  mul3 (triangular_product n w) (unstable_frame (shift_by n w)).
Proof.
  induction n; intro w.
  - simpl. rewrite mul3_id_left, mul3_id_right. reflexivity.
  - cbn [marking_product triangular_product].
    rewrite <- mul3_assoc, marked_cocycle_step, mul3_assoc, IHn, <- mul3_assoc. reflexivity.
Qed.

Theorem triangular_product_shape : forall n w, exists v z,
  triangular_product n w =
  triangular3 (return_height n w) v z (scale2 (return_scale n w) (fiber_product n w)).
Proof.
  induction n; intro w.
  - exists 0, 0. apply mat3_ext; unfold triangular_product, return_height, return_scale,
      fiber_product, factors, product, triangular3, scale2, id2, id3; simpl; ring.
  - destruct (IHn (shift w)) as [v [z Hz]].
    cbn [triangular_product]. unfold triangular_step. rewrite Hz, triangular3_product, matrix_scale_product.
    eexists; eexists; reflexivity.
Qed.

Lemma return_height_at_least_one : forall n w, 1 <= return_height n w.
Proof.
  induction n; intro w; [simpl; lra|].
  cbn [return_height]. specialize (IHn (shift w)). pose proof (denominator_bounds w).
  pose proof (Rmult_le_pos (denominator w-1) (return_height n (shift w)-1) ltac:(lra) ltac:(lra)). nra.
Qed.
Theorem return_height_expanding : forall n w, (0 < n)%nat -> 1 < return_height n w.
Proof.
  intros [|n] w Hn; [lia|]. cbn [return_height].
  pose proof (return_height_at_least_one n (shift w)). pose proof (denominator_bounds w).
  pose proof (Rmult_le_pos (denominator w-1) (return_height n (shift w)-1) ltac:(lra) ltac:(lra)). nra.
Qed.
Lemma return_scale_positive : forall n w, 0 < return_scale n w.
Proof.
  induction n; intro w; [simpl; lra|]. cbn [return_scale].
  apply Rmult_lt_0_compat; auto. exact (proj1 (inverse_roof_bounds w)).
Qed.
Lemma return_scale_at_most_one : forall n w, return_scale n w <= 1.
Proof.
  induction n; intro w; [simpl; lra|]. cbn [return_scale].
  pose proof (inverse_roof_bounds w). pose proof (return_scale_positive n (shift w)).
  specialize (IHn (shift w)).
  pose proof (Rmult_le_compat 0 (inverse_roof w) 0 (return_scale n (shift w)) ltac:(lra) ltac:(lra)
    ltac:(lra) ltac:(lra)).
  assert (inverse_roof w*return_scale n (shift w) <= (1/10)*1).
  { apply Rmult_le_compat; lra. } lra.
Qed.
Theorem return_scale_contracting : forall n w, (0 < n)%nat -> 0 < return_scale n w < 1.
Proof.
  intros [|n] w Hn; [lia|]. split; [apply return_scale_positive|]. cbn [return_scale].
  pose proof (inverse_roof_bounds w). pose proof (return_scale_positive n (shift w)).
  pose proof (return_scale_at_most_one n (shift w)).
  assert (inverse_roof w*return_scale n (shift w) <= (1/10)*1).
  { apply Rmult_le_compat; lra. } lra.
Qed.

Lemma inverse_roof_balance : forall w, denominator w*(inverse_roof w)^2 = 1.
Proof.
  intro w. pose proof (denominator_bounds w) as Hd.
  unfold inverse_roof. replace ((/sqrt (denominator w))^2) with
    (/sqrt (denominator w)* /sqrt (denominator w)) by ring.
  rewrite inverse_root_square by lra. field; lra.
Qed.
Theorem return_height_scale_balance : forall n w,
  return_height n w*(return_scale n w)^2 = 1.
Proof.
  induction n; intro w; [simpl; ring|]. cbn [return_height return_scale].
  replace (denominator w*return_height n (shift w)*(inverse_roof w*return_scale n (shift w))^2) with
    ((denominator w*(inverse_roof w)^2)*(return_height n (shift w)*(return_scale n (shift w))^2)) by ring.
  rewrite inverse_roof_balance, IHn. ring.
Qed.

Lemma marking_integral : forall s, integral_matrix (marking s).
Proof.
  intros []; [exists (ZMat3 101 (-1) (-10) 10 0 (-1) 1 0 0)
             |exists (ZMat3 101 (-1) 10 10 0 1 (-1) 0 0)]; reflexivity.
Qed.
Lemma marking_unimodular : forall s, det3 (marking s) = 1.
Proof. intros []; [exact (proj1 integral_markings_unimodular)|exact (proj2 integral_markings_unimodular)]. Qed.
Theorem marking_product_integral : forall n w, integral_matrix (marking_product n w).
Proof.
  induction n; intro w; simpl; [apply integral_identity|].
  apply integral_product; auto using marking_integral.
Qed.
Theorem marking_product_unimodular : forall n w, det3 (marking_product n w) = 1.
Proof.
  induction n; intro w; simpl.
  - unfold det3, id3; simpl; ring.
  - rewrite mul3_determinant, marking_unimodular, IHn. ring.
Qed.

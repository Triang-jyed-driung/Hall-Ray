From Stdlib Require Import Reals Psatz Lia Arith List.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  ReturnBranches SymbolicCoding ConcreteCocycle SymbolicCocycle.
Open Scope R_scope.

Definition a_future : future := fun _ => true.
Definition one_defect (r : nat) : future := fun k => if Nat.eqb k r then false else true.
Definition constant_return := cocycle a_future.
Definition defect_product (r : nat) := fiber_product (S r) (one_defect r).
Fixpoint matrix_power (A : mat2) (n : nat) :=
  match n with O => id2 | S k => mul2 A (matrix_power A k) end.

(* D_r = G B_r G^{-1}, the defect in the original fiber coordinates.
   No conjugator or rotation angle is needed to construct this limit. *)
Definition defect_sequence (r : nat) :=
  mul2 (matrix_power (adj2 constant_return) r) (defect_product r).

Lemma adjugate_determinant : forall A, det2 (adj2 A) = det2 A.
Proof. intros []; unfold det2, adj2; simpl; ring. Qed.
Lemma adjugate_left_identity : forall A,
  det2 A = 1 -> mul2 (adj2 A) A = id2.
Proof.
  intros [a b c d] Hd. unfold det2 in Hd; simpl in Hd.
  apply mat2_ext; unfold mul2, adj2, id2; simpl; nra.
Qed.

Lemma matrix_power_successor_right : forall A n,
  matrix_power A (S n) = mul2 (matrix_power A n) A.
Proof.
  intros A n. induction n.
  - simpl. rewrite mul2_id_left, mul2_id_right. reflexivity.
  - change (mul2 A (matrix_power A (S n)) = mul2 (mul2 A (matrix_power A n)) A).
    rewrite IHn, mul2_assoc. reflexivity.
Qed.
Lemma matrix_power_unimodular : forall A n,
  det2 A = 1 -> det2 (matrix_power A n) = 1.
Proof.
  intros A n Hd. induction n; simpl.
  - unfold det2, id2; simpl; ring.
  - rewrite det2_mul, Hd, IHn. ring.
Qed.
Lemma matrix_power_norm : forall A b n,
  0 <= b -> opnorm A <= b -> opnorm (matrix_power A n) <= b^n.
Proof.
  intros A b n Hb HA. induction n; simpl.
  - rewrite opnorm_identity. lra.
  - eapply Rle_trans; [apply opnorm_submultiplicative|].
    apply Rmult_le_compat; auto using opnorm_nonnegative.
Qed.
Lemma fiber_product_norm : forall n w, opnorm (fiber_product n w) <= (11/10)^n.
Proof.
  induction n; intro w; unfold fiber_product in *; simpl.
  - rewrite opnorm_identity. lra.
  - eapply Rle_trans; [apply opnorm_submultiplicative|].
    apply Rmult_le_compat; auto using opnorm_nonnegative.
    + pose proof (cocycle_bounds w); lra.
Qed.

Lemma one_defect_shift : forall r, shift (one_defect (S r)) = one_defect r.
Proof. reflexivity. Qed.
Lemma defect_product_step : forall r,
  defect_product (S r) = mul2 (cocycle (one_defect (S r))) (defect_product r).
Proof.
  intro r. unfold defect_product, fiber_product; simpl.
  rewrite one_defect_shift. reflexivity.
Qed.

Lemma defect_sequence_unimodular : forall r, det2 (defect_sequence r) = 1.
Proof.
  intro r. unfold defect_sequence, defect_product. rewrite det2_mul.
  rewrite matrix_power_unimodular.
  - rewrite factor_product_unimodular. ring.
  - rewrite adjugate_determinant. apply cocycle_unimodular.
Qed.

Lemma defect_head_difference : forall r,
  opnorm (sub2 (cocycle (one_defect (S r))) constant_return) <= (2/25)*(1/900)^r.
Proof.
  intro r.
  assert (Hclose : close ((2/5)*(1/900)^r) (coded (one_defect r)) (coded a_future)).
  { apply common_future_estimate. intros k Hk. unfold one_defect, a_future.
    assert (Hneq : Nat.eqb k r = false) by (apply Nat.eqb_neq; lia).
    rewrite Hneq. reflexivity. }
  unfold cocycle, constant_return. unfold cocycle.
  change (opnorm (sub2
    (fiber_matrix true (fst (coded (one_defect r))) (snd (coded (one_defect r))))
    (fiber_matrix true (fst (coded a_future)) (snd (coded a_future)))) <= (2/25)*(1/900)^r).
  pose proof (fiber_matrix_lipschitz true
    (fst (coded (one_defect r))) (snd (coded (one_defect r)))
    (fst (coded a_future)) (snd (coded a_future)) ((2/5)*(1/900)^r)
    (coded_inside (one_defect r)) (coded_inside a_future)
    ltac:(apply Rmult_le_pos; [lra|apply pow_le; lra]) (proj1 Hclose) (proj2 Hclose)) as H.
  nra.
Qed.

Theorem defect_increment_identity : forall r,
  sub2 (defect_sequence (S r)) (defect_sequence r) =
  mul2 (mul2 (mul2 (matrix_power (adj2 constant_return) r) (adj2 constant_return))
                 (sub2 (cocycle (one_defect (S r))) constant_return)) (defect_product r).
Proof.
  intro r. unfold defect_sequence. rewrite matrix_power_successor_right, defect_product_step.
  rewrite !mul2_assoc.
  rewrite <- (mul2_assoc (adj2 constant_return) (cocycle (one_defect (S r))) (defect_product r)).
  rewrite (inverse_comparison constant_return (cocycle (one_defect (S r))) (cocycle_unimodular a_future)).
  rewrite mul2_add_left, mul2_id_left, mul2_add_right.
  rewrite <- !mul2_assoc.
  generalize (mul2 (mul2 (mul2 (matrix_power (adj2 constant_return) r) (adj2 constant_return))
    (sub2 (cocycle (one_defect (S r))) constant_return)) (defect_product r)).
  generalize (mul2 (matrix_power (adj2 constant_return) r) (defect_product r)).
  intros [] []; apply mat2_ext; unfold sub2, add2, scale2; simpl; ring.
Qed.

Theorem defect_increment_bound : forall r,
  opnorm (sub2 (defect_sequence (S r)) (defect_sequence r)) <= (1/10)*(1/600)^r.
Proof.
  intro r.
  pose proof (cocycle_bounds a_future) as HA.
  assert (Hadj : opnorm (adj2 constant_return) <= 11/10) by (unfold constant_return; lra).
  pose proof (matrix_power_norm (adj2 constant_return) (11/10) r ltac:(lra) Hadj) as HP.
  pose proof (fiber_product_norm (S r) (one_defect r)) as HT.
  change (opnorm (defect_product r) <= (11/10)^(S r)) in HT.
  pose proof (defect_head_difference r) as HD.
  rewrite defect_increment_identity.
  assert (HB : opnorm
    (mul2 (mul2 (mul2 (matrix_power (adj2 constant_return) r) (adj2 constant_return))
                 (sub2 (cocycle (one_defect (S r))) constant_return)) (defect_product r)) <=
    (11/10)^r*(11/10)*((2/25)*(1/900)^r)*(11/10)^(S r)).
  { eapply Rle_trans; [apply opnorm_submultiplicative|].
    apply Rmult_le_compat; auto using opnorm_nonnegative.
    eapply Rle_trans; [apply opnorm_submultiplicative|].
    apply Rmult_le_compat; auto using opnorm_nonnegative.
    eapply Rle_trans; [apply opnorm_submultiplicative|].
    apply Rmult_le_compat; auto using opnorm_nonnegative. }
  assert (Hpower : (11/10)^r*(11/10)*((2/25)*(1/900)^r)*(11/10)^(S r) =
    (121/1250)*((11/10)^2/900)^r).
  { replace ((11/10)^r*(11/10)*((2/25)*(1/900)^r)*(11/10)^(S r)) with
      ((121/1250)*(((11/10)^r*(11/10)^r)*(1/900)^r)) by (simpl pow; field).
    rewrite <- !Rpow_mult_distr.
    replace ((11/10)*(11/10)*(1/900)) with ((11/10)^2/900) by field. reflexivity. }
  rewrite Hpower in HB.
  pose proof (pow_incr ((11/10)^2/900) (1/600) r ltac:(simpl; nra)) as Hpow.
  pose proof (pow_le ((11/10)^2/900) r ltac:(simpl; nra)).
  pose proof (pow_le (1/600) r ltac:(lra)). nra.
Qed.

Theorem defect_limit_exists :
  { D : mat2 | matrix_cv defect_sequence D /\ det2 D = 1 /\
    forall r, opnorm (sub2 (defect_sequence r) D) <= (1/5)*(1/600)^r }.
Proof.
  destruct (geometric_matrix_convergence defect_sequence (1/10) (1/600)
    ltac:(lra) ltac:(lra) defect_increment_bound) as [D [HD Hbound]].
  exists D. split; [exact HD|]. split.
  - apply (unimodular_limit defect_sequence); auto using defect_sequence_unimodular.
  - intro r. specialize (Hbound r).
    pose proof (pow_le (1/600) r ltac:(lra)).
    assert (Hconstant : (1/10)/(1-1/600) <= 1/5) by (field_simplify; lra). nra.
Qed.

Definition defect_limit := proj1_sig defect_limit_exists.
Theorem defect_limit_converges : matrix_cv defect_sequence defect_limit.
Proof. exact (proj1 (proj2_sig defect_limit_exists)). Qed.
Theorem defect_limit_unimodular : det2 defect_limit = 1.
Proof. exact (proj1 (proj2 (proj2_sig defect_limit_exists))). Qed.
Theorem defect_limit_error_bound : forall r,
  opnorm (sub2 (defect_sequence r) defect_limit) <= (1/5)*(1/600)^r.
Proof. exact (proj2 (proj2 (proj2_sig defect_limit_exists))). Qed.

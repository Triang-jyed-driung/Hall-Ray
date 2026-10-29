From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra ScalarEstimates ConstantReturn FiberProducts
  EuclideanNorm MatrixLimits SymbolicCoding ConcreteCocycle SymbolicCocycle
  DefectLimit ConstantCoding DefectCertificate.
Open Scope R_scope.

Definition commutator (A B : mat2) := sub2 (mul2 A B) (mul2 B A).

Lemma opnorm_subtract_bound : forall A B, opnorm (sub2 A B) <= opnorm A+opnorm B.
Proof.
  intros A B. unfold sub2. eapply Rle_trans; [apply opnorm_subadditive|].
  rewrite opnorm_negative. lra.
Qed.

Theorem commutator_norm_bound : forall A B,
  opnorm (commutator A B) <= 2*opnorm A*opnorm B.
Proof.
  intros A B. unfold commutator.
  pose proof (opnorm_subtract_bound (mul2 A B) (mul2 B A)).
  pose proof (opnorm_submultiplicative A B).
  pose proof (opnorm_submultiplicative B A). nra.
Qed.

Lemma commutator_difference : forall A B C,
  commutator A B = add2 (commutator A C) (commutator A (sub2 B C)).
Proof.
  intros [] [] []; apply mat2_ext; unfold commutator, sub2, add2, mul2, scale2; simpl; ring.
Qed.
Lemma commuting_commutator_zero : forall A B,
  mul2 A B = mul2 B A -> commutator A B = zero2.
Proof.
  intros A B H. unfold commutator. rewrite H.
  destruct (mul2 B A); apply mat2_ext; unfold sub2, add2, scale2, zero2; simpl; ring.
Qed.
Lemma zero2_add_left : forall A, add2 zero2 A = A.
Proof. intros []; apply mat2_ext; unfold add2, zero2; simpl; ring. Qed.

Theorem finite_concrete_commutator_lower_bound :
  1/10000 < a21 (commutator constant_return (defect_sequence 2)).
Proof.
  destruct constant_root_exists as [alpha [Ha Hf]]. unfold commutator.
  rewrite (constant_return_formula alpha ltac:(lra) Hf), (defect_two_formula alpha ltac:(lra) Hf).
  apply finite_defect_commutator_certificate; tauto.
Qed.

Theorem defect_limit_noncommuting :
  mul2 constant_return defect_limit <> mul2 defect_limit constant_return.
Proof.
  intro Hcomm.
  pose proof (commuting_commutator_zero constant_return defect_limit Hcomm) as Hzero.
  pose proof (commutator_difference constant_return (defect_sequence 2) defect_limit) as Hid.
  rewrite Hzero, zero2_add_left in Hid.
  pose proof (commutator_norm_bound constant_return (sub2 (defect_sequence 2) defect_limit)) as Hnorm.
  rewrite <- Hid in Hnorm.
  pose proof (defect_limit_error_bound 2) as Herror.
  pose proof (cocycle_bounds a_future) as HA.
  change (opnorm constant_return <= 26/25 /\ opnorm (adj2 constant_return) <= 26/25) in HA.
  assert (Hprod : opnorm constant_return*opnorm (sub2 (defect_sequence 2) defect_limit) <=
                 (26/25)*((1/5)*(1/600)^2)).
  { apply Rmult_le_compat; auto using opnorm_nonnegative; tauto. }
  pose proof (opnorm_entries (commutator constant_return (defect_sequence 2))) as Hentries.
  pose proof (Rle_abs (a21 (commutator constant_return (defect_sequence 2)))) as Habs.
  pose proof finite_concrete_commutator_lower_bound. simpl pow in *. nra.
Qed.

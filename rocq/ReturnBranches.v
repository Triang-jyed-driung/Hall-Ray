From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra.
Open Scope R_scope.

(* The two inverse branches in (3.3), using actual real coordinates. *)
Definition in_U (x y : R) := -1/5 <= x <= 1/5 /\ -1/50 <= y <= 1/50.
Definition in_V (x y : R) := -1/50 <= x <= 1/50 /\ -1/5 <= y <= 1/5.
Definition da (x y : R) := 101-x-10*y.
Definition db (x y : R) := 101-x+10*y.
Definition phi_a1 (x y : R) := (10-y)/da x y.
Definition phi_a2 (x y : R) := 1/da x y.
Definition phi_b1 (x y : R) := (10+y)/db x y.
Definition phi_b2 (x y : R) := -1/db x y.

Lemma da_bounds : forall x y, in_U x y -> 503/5 <= da x y <= 507/5.
Proof. unfold in_U, da; intros; lra. Qed.
Lemma db_bounds : forall x y, in_U x y -> 503/5 <= db x y <= 507/5.
Proof. unfold in_U, db; intros; lra. Qed.

Theorem phi_a_invariant : forall x y, in_U x y -> in_U (phi_a1 x y) (phi_a2 x y).
Proof.
  intros x y Hu. pose proof (da_bounds x y Hu) as Hd.
  unfold in_U in *. unfold phi_a1, phi_a2.
  assert (Hpos : 0 < da x y) by lra.
  split; split.
  - apply (Rmult_le_reg_r (da x y)); try lra. field_simplify; nra.
  - apply (Rmult_le_reg_r (da x y)); try lra. field_simplify; nra.
  - apply (Rmult_le_reg_r (da x y)); try lra. field_simplify; nra.
  - apply (Rmult_le_reg_r (da x y)); try lra. field_simplify; nra.
Qed.

Theorem phi_b_invariant : forall x y, in_U x y -> in_U (phi_b1 x y) (phi_b2 x y).
Proof.
  intros x y Hu. pose proof (db_bounds x y Hu) as Hd.
  unfold in_U in *. unfold phi_b1, phi_b2.
  assert (Hpos : 0 < db x y) by lra.
  split; split.
  - apply (Rmult_le_reg_r (db x y)); try lra. field_simplify; nra.
  - apply (Rmult_le_reg_r (db x y)); try lra. field_simplify; nra.
  - apply (Rmult_le_reg_r (db x y)); try lra. field_simplify; nra.
  - apply (Rmult_le_reg_r (db x y)); try lra. field_simplify; nra.
Qed.

Theorem phi_disjoint : forall x y x' y', in_U x y -> in_U x' y' ->
  phi_a2 x y <> phi_b2 x' y'.
Proof.
  intros x y x' y' Hu Hu'.
  pose proof (da_bounds x y Hu). pose proof (db_bounds x' y' Hu').
  unfold phi_a2, phi_b2.
  assert (0 < 1 / da x y) by (apply Rdiv_lt_0_compat; lra).
  assert (-1 / db x' y' < 0) by (apply Rdiv_neg_pos; lra).
  lra.
Qed.

Theorem phi_a_injective : forall x y x' y', in_U x y -> in_U x' y' ->
  phi_a1 x y = phi_a1 x' y' -> phi_a2 x y = phi_a2 x' y' ->
  x = x' /\ y = y'.
Proof.
  intros x y x' y' Hu Hu' H1 H2.
  pose proof (da_bounds x y Hu). pose proof (da_bounds x' y' Hu').
  unfold phi_a1, phi_a2 in *.
  assert (Hda : da x y <> 0) by lra.
  assert (Hda' : da x' y' <> 0) by lra.
  assert (Hd : da x y = da x' y').
  { apply Rinv_eq_reg. unfold Rdiv in H2. rewrite !Rmult_1_l in H2. exact H2. }
  rewrite Hd in H1.
  pose proof (Rdiv_eq_reg_r _ _ _ H1 Hda').
  unfold da in Hd. split; lra.
Qed.

Theorem phi_b_injective : forall x y x' y', in_U x y -> in_U x' y' ->
  phi_b1 x y = phi_b1 x' y' -> phi_b2 x y = phi_b2 x' y' ->
  x = x' /\ y = y'.
Proof.
  intros x y x' y' Hu Hu' H1 H2.
  pose proof (db_bounds x y Hu). pose proof (db_bounds x' y' Hu').
  unfold phi_b1, phi_b2 in *.
  assert (Hdb : db x y <> 0) by lra.
  assert (Hdb' : db x' y' <> 0) by lra.
  assert (Hd : db x y = db x' y').
  { apply Rinv_eq_reg. unfold Rdiv in H2. nra. }
  rewrite Hd in H1.
  pose proof (Rdiv_eq_reg_r _ _ _ H1 Hdb').
  unfold db in Hd. split; lra.
Qed.

(* Fixed-point algebra in (4.2)--(4.3), with no root-existence assumption hidden. *)
Definition fixed_u1 (alpha : R) := 10/alpha-1/alpha^2.
Definition fixed_u2 (alpha : R) := 1/alpha.

Theorem fixed_point_denominator : forall alpha,
  100 < alpha -> cubic alpha = 0 ->
  da (fixed_u1 alpha) (fixed_u2 alpha) = alpha.
Proof.
  intros alpha Ha Hf. unfold cubic in Hf.
  unfold da, fixed_u1, fixed_u2.
  apply (Rmult_eq_reg_r (alpha^2)); [|nra].
  field_simplify; nra.
Qed.

Theorem fixed_point_formula : forall alpha,
  100 < alpha -> cubic alpha = 0 ->
  phi_a1 (fixed_u1 alpha) (fixed_u2 alpha) = fixed_u1 alpha /\
  phi_a2 (fixed_u1 alpha) (fixed_u2 alpha) = fixed_u2 alpha.
Proof.
  intros alpha Ha Hf. unfold phi_a1, phi_a2.
  rewrite (fixed_point_denominator alpha Ha Hf).
  unfold fixed_u1, fixed_u2. split; field; lra.
Qed.

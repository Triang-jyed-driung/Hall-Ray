From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra ReturnBranches.
Open Scope R_scope.

Definition mul3 (A B : mat3) := Mat3
  (b11 A*b11 B+b12 A*b21 B+b13 A*b31 B)
  (b11 A*b12 B+b12 A*b22 B+b13 A*b32 B)
  (b11 A*b13 B+b12 A*b23 B+b13 A*b33 B)
  (b21 A*b11 B+b22 A*b21 B+b23 A*b31 B)
  (b21 A*b12 B+b22 A*b22 B+b23 A*b32 B)
  (b21 A*b13 B+b22 A*b23 B+b23 A*b33 B)
  (b31 A*b11 B+b32 A*b21 B+b33 A*b31 B)
  (b31 A*b12 B+b32 A*b22 B+b33 A*b32 B)
  (b31 A*b13 B+b32 A*b23 B+b33 A*b33 B).
Definition scale3 (r : R) (A : mat3) := Mat3
  (r*b11 A) (r*b12 A) (r*b13 A)
  (r*b21 A) (r*b22 A) (r*b23 A)
  (r*b31 A) (r*b32 A) (r*b33 A).
Definition block3 (r : R) (A : mat2) :=
  Mat3 r 0 0 0 (a11 A) (a12 A) 0 (a21 A) (a22 A).
Definition raw_chart (x y v w : R) := Mat3 1 v w (-x) 1 0 (-y) 0 1.
Definition chart (c x y v w : R) (E : mat2) :=
  scale3 c (mul3 (block3 1 E) (raw_chart x y v w)).
Definition psi_a1 (v w : R) := -1/(101+10*v+w).
Definition psi_a2 (v w : R) := (-10-v)/(101+10*v+w).
Definition psi_b1 (v w : R) := -1/(101+10*v-w).
Definition psi_b2 (v w : R) := (10+v)/(101+10*v-w).

Lemma mat3_ext : forall A B,
  b11 A=b11 B -> b12 A=b12 B -> b13 A=b13 B ->
  b21 A=b21 B -> b22 A=b22 B -> b23 A=b23 B ->
  b31 A=b31 B -> b32 A=b32 B -> b33 A=b33 B -> A=B.
Proof. intros [] []; simpl; intros; subst; reflexivity. Qed.

Theorem raw_marked_return_a : forall x y v w,
  da x y <> 0 -> 101+10*v+w <> 0 ->
  mul3 (raw_chart (phi_a1 x y) (phi_a2 x y) v w) gamma_a =
  mul3 (block3 (101+10*v+w) (scale2 (/da x y) (numerator_a x y)))
       (raw_chart x y (psi_a1 v w) (psi_a2 v w)).
Proof.
  intros x y v w Hd Hv. unfold da in Hd.
  apply mat3_ext; unfold mul3, raw_chart, gamma_a, block3, scale2,
    numerator_a, phi_a1, phi_a2, psi_a1, psi_a2, da; simpl;
    field; auto.
Qed.

Theorem raw_marked_return_b : forall x y v w,
  db x y <> 0 -> 101+10*v-w <> 0 ->
  mul3 (raw_chart (phi_b1 x y) (phi_b2 x y) v w) gamma_b =
  mul3 (block3 (101+10*v-w) (scale2 (/db x y) (numerator_b x y)))
       (raw_chart x y (psi_b1 v w) (psi_b2 v w)).
Proof.
  intros x y v w Hd Hv. unfold db in Hd.
  apply mat3_ext; unfold mul3, raw_chart, gamma_b, block3, scale2,
    numerator_b, phi_b1, phi_b2, psi_b1, psi_b2, db; simpl;
    field; auto.
Qed.

Theorem chart_determinant : forall c x y v w E,
  det3 (chart c x y v w E) = c^3*det2 E*(1+v*x+w*y).
Proof.
  intros c x y v w []; unfold det3, chart, scale3, mul3, block3, raw_chart, det2;
  simpl; ring.
Qed.

Theorem normalized_chart_unimodular : forall c x y v w E,
  c^3*(1+v*x+w*y) = 1 -> det2 E = 1 -> det3 (chart c x y v w E) = 1.
Proof. intros. rewrite chart_determinant, H0. nra. Qed.

Theorem chart_denominator_positive : forall x y v w,
  in_U x y -> in_V v w -> 124/125 <= 1+v*x+w*y.
Proof.
  unfold in_U, in_V. intros x y v w [[Hx1 Hx2] [Hy1 Hy2]] [[Hv1 Hv2] [Hw1 Hw2]].
  assert (Hvx : -1/250 <= v*x).
  { pose proof (Rmult_le_pos (x+1/5) (v+1/50) ltac:(lra) ltac:(lra)).
    pose proof (Rmult_le_pos (1/5-x) (1/50-v) ltac:(lra) ltac:(lra)). nra. }
  assert (Hwy : -1/250 <= w*y).
  { pose proof (Rmult_le_pos (y+1/50) (w+1/5) ltac:(lra) ltac:(lra)).
    pose proof (Rmult_le_pos (1/50-y) (1/5-w) ltac:(lra) ltac:(lra)). nra. }
  lra.
Qed.

Definition hx (x y : R) := Mat3 1 0 0 (-x) 1 0 (-y) 0 1.
Definition stable_shear (v w : R) := Mat3 1 v w 0 1 0 0 0 1.

(* The exact factorization used in Section 6, Step 4.  When
   c=(1+v*x+w*y)^(-1/3), the first block factor is the paper's
   g_{-(1/3)log(1+v*x+w*y)}. *)
Theorem forgetting_past_factorization : forall c x y v w,
  1+v*x+w*y <> 0 ->
  chart c x y v w id2 =
  mul3 (block3 (c*(1+v*x+w*y)) (scale2 c id2))
       (mul3 (stable_shear (v/(1+v*x+w*y)) (w/(1+v*x+w*y))) (hx x y)).
Proof.
  intros c x y v w Hi. apply mat3_ext;
  unfold chart, scale3, mul3, block3, raw_chart, id2, scale2, stable_shear, hx;
  simpl; field; auto.
Qed.

Definition flow_scale (r : R) := Mat3 (/ (r*r)) 0 0 0 r 0 0 0 r.
Theorem stable_shear_conjugation : forall r v w,
  r <> 0 ->
  mul3 (mul3 (flow_scale r) (stable_shear v w)) (flow_scale (/r)) =
  stable_shear (v/r^3) (w/r^3).
Proof.
  intros r v w Hr. apply mat3_ext;
  unfold mul3, flow_scale, stable_shear; simpl; field; auto.
Qed.

From Stdlib Require Import Reals Psatz ZArith.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices.
Open Scope R_scope.

Definition adj3 (A : mat3) := Mat3
  (b22 A*b33 A-b23 A*b32 A) (b13 A*b32 A-b12 A*b33 A) (b12 A*b23 A-b13 A*b22 A)
  (b23 A*b31 A-b21 A*b33 A) (b11 A*b33 A-b13 A*b31 A) (b13 A*b21 A-b11 A*b23 A)
  (b21 A*b32 A-b22 A*b31 A) (b12 A*b31 A-b11 A*b32 A) (b11 A*b22 A-b12 A*b21 A).
Definition zadj3 (A : zmat3) := ZMat3
  (z22 A*z33 A-z23 A*z32 A) (z13 A*z32 A-z12 A*z33 A) (z12 A*z23 A-z13 A*z22 A)
  (z23 A*z31 A-z21 A*z33 A) (z11 A*z33 A-z13 A*z31 A) (z13 A*z21 A-z11 A*z23 A)
  (z21 A*z32 A-z22 A*z31 A) (z12 A*z31 A-z11 A*z32 A) (z11 A*z22 A-z12 A*z21 A).

Lemma real3_adjugate : forall A, real3 (zadj3 A) = adj3 (real3 A).
Proof.
  intros []; apply mat3_ext; unfold zadj3, real3, adj3; simpl;
    repeat first [rewrite minus_IZR|rewrite mult_IZR]; reflexivity.
Qed.
Lemma mul3_adjugate_right : forall A, mul3 A (adj3 A) = scale3 (det3 A) id3.
Proof. intros []; apply mat3_ext; unfold mul3, adj3, scale3, det3, id3; simpl; ring. Qed.
Lemma mul3_adjugate_left : forall A, mul3 (adj3 A) A = scale3 (det3 A) id3.
Proof. intros []; apply mat3_ext; unfold mul3, adj3, scale3, det3, id3; simpl; ring. Qed.
Lemma unimodular3_inverse_right : forall A, det3 A = 1 -> mul3 A (adj3 A) = id3.
Proof.
  intros A HA; rewrite mul3_adjugate_right, HA.
  apply mat3_ext; unfold scale3, id3; simpl; ring.
Qed.
Lemma unimodular3_inverse_left : forall A, det3 A = 1 -> mul3 (adj3 A) A = id3.
Proof.
  intros A HA; rewrite mul3_adjugate_left, HA.
  apply mat3_ext; unfold scale3, id3; simpl; ring.
Qed.
Theorem integral_adjugate : forall A, integral_matrix A -> integral_matrix (adj3 A).
Proof.
  intros A [Z HZ]; exists (zadj3 Z); rewrite real3_adjugate, HZ; reflexivity.
Qed.

Record vec3 := Vec3 { v1 : R; v2 : R; v3 : R }.
Record zvec3 := ZVec3 { zv1 : Z; zv2 : Z; zv3 : Z }.
Definition real_vector (z : zvec3) := Vec3 (IZR (zv1 z)) (IZR (zv2 z)) (IZR (zv3 z)).
Definition action3 (A : mat3) (v : vec3) := Vec3
  (b11 A*v1 v+b12 A*v2 v+b13 A*v3 v)
  (b21 A*v1 v+b22 A*v2 v+b23 A*v3 v)
  (b31 A*v1 v+b32 A*v2 v+b33 A*v3 v).
Definition zaction3 (A : zmat3) (v : zvec3) := ZVec3
  (z11 A*zv1 v+z12 A*zv2 v+z13 A*zv3 v)
  (z21 A*zv1 v+z22 A*zv2 v+z23 A*zv3 v)
  (z31 A*zv1 v+z32 A*zv2 v+z33 A*zv3 v).

Lemma vec3_ext : forall a b, v1 a=v1 b -> v2 a=v2 b -> v3 a=v3 b -> a=b.
Proof. intros [] []; simpl; intros; subst; reflexivity. Qed.
Lemma action3_product : forall A B v, action3 (mul3 A B) v = action3 A (action3 B v).
Proof. intros [] [] []; apply vec3_ext; unfold action3, mul3; simpl; ring. Qed.
Lemma action3_identity : forall v, action3 id3 v = v.
Proof. intros []; apply vec3_ext; unfold action3, id3; simpl; ring. Qed.
Lemma real_vector_action : forall A z,
  real_vector (zaction3 A z) = action3 (real3 A) (real_vector z).
Proof.
  intros [] []; apply vec3_ext; unfold real_vector, zaction3, action3, real3; simpl;
    repeat first [rewrite plus_IZR|rewrite mult_IZR]; reflexivity.
Qed.

Definition lattice (A : mat3) (v : vec3) := exists z, v = action3 A (real_vector z).
Definition same_lattice (A B : mat3) := forall v, lattice A v <-> lattice B v.
Lemma same_lattice_reflexive : forall A, same_lattice A A.
Proof. intros A v; tauto. Qed.
Lemma same_lattice_symmetric : forall A B, same_lattice A B -> same_lattice B A.
Proof. intros A B H v; specialize (H v); tauto. Qed.
Lemma same_lattice_transitive : forall A B C,
  same_lattice A B -> same_lattice B C -> same_lattice A C.
Proof. intros A B C H1 H2 v; specialize (H1 v); specialize (H2 v); tauto. Qed.

Theorem unimodular_marking_preserves_lattice : forall A Gamma,
  integral_matrix Gamma -> det3 Gamma = 1 -> same_lattice (mul3 A Gamma) A.
Proof.
  intros A Gamma [Z HZ] Hdet v; split.
  - intros [z Hz]. exists (zaction3 Z z).
    rewrite real_vector_action, HZ, <- action3_product. exact Hz.
  - intros [z Hz]. exists (zaction3 (zadj3 Z) z).
    rewrite real_vector_action, real3_adjugate, HZ, action3_product.
    rewrite <- (action3_product Gamma (adj3 Gamma) (real_vector z)).
    rewrite (unimodular3_inverse_right Gamma Hdet), action3_identity. exact Hz.
Qed.

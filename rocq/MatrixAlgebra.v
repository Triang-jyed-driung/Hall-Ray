From Stdlib Require Import Reals Psatz.

Open Scope R_scope.

(* Concrete algebra from Sections 3--4 of arXiv:2609.23464v1.
   This file does not postulate any statement from the paper. *)

Record mat2 := Mat2 { a11 : R; a12 : R; a21 : R; a22 : R }.
Definition det2 (A : mat2) := a11 A * a22 A - a12 A * a21 A.
Definition trace2 (A : mat2) := a11 A + a22 A.
Definition id2 := Mat2 1 0 0 1.
Definition mul2 (A B : mat2) :=
  Mat2 (a11 A*a11 B+a12 A*a21 B) (a11 A*a12 B+a12 A*a22 B)
       (a21 A*a11 B+a22 A*a21 B) (a21 A*a12 B+a22 A*a22 B).
Definition scale2 (r : R) (A : mat2) :=
  Mat2 (r*a11 A) (r*a12 A) (r*a21 A) (r*a22 A).
Definition adj2 (A : mat2) := Mat2 (a22 A) (-a12 A) (-a21 A) (a11 A).
Definition transpose2 (A : mat2) := Mat2 (a11 A) (a21 A) (a12 A) (a22 A).
Definition orthogonal2 (A : mat2) := mul2 (transpose2 A) A = id2.

Lemma mat2_ext : forall A B,
  a11 A = a11 B -> a12 A = a12 B ->
  a21 A = a21 B -> a22 A = a22 B -> A = B.
Proof. intros [] []; simpl; intros; subst; reflexivity. Qed.

Lemma mul2_assoc : forall A B C, mul2 (mul2 A B) C = mul2 A (mul2 B C).
Proof. intros [] [] []; apply mat2_ext; simpl; ring. Qed.
Lemma mul2_id_left : forall A, mul2 id2 A = A.
Proof. intros []; apply mat2_ext; simpl; ring. Qed.
Lemma mul2_id_right : forall A, mul2 A id2 = A.
Proof. intros []; apply mat2_ext; simpl; ring. Qed.
Lemma det2_mul : forall A B, det2 (mul2 A B) = det2 A * det2 B.
Proof. intros [] []; unfold det2, mul2; simpl; ring. Qed.
Lemma det2_scale : forall r A, det2 (scale2 r A) = r*r*det2 A.
Proof. intros r []; unfold det2, scale2; simpl; ring. Qed.
Lemma mul2_adj_right : forall A, mul2 A (adj2 A) = scale2 (det2 A) id2.
Proof. intros []; apply mat2_ext; unfold det2, mul2, adj2, scale2, id2; simpl; ring. Qed.

Record mat3 := Mat3 {
  b11 : R; b12 : R; b13 : R;
  b21 : R; b22 : R; b23 : R;
  b31 : R; b32 : R; b33 : R
}.
Definition det3 (A : mat3) :=
  b11 A * (b22 A*b33 A-b23 A*b32 A)
  -b12 A * (b21 A*b33 A-b23 A*b31 A)
  +b13 A * (b21 A*b32 A-b22 A*b31 A).
Definition gamma_a := Mat3 101 (-1) (-10) 10 0 (-1) 1 0 0.
Definition gamma_b := Mat3 101 (-1) 10 10 0 1 (-1) 0 0.
Definition char3 (A : mat3) (x : R) :=
  det3 (Mat3 (x-b11 A) (-b12 A) (-b13 A)
             (-b21 A) (x-b22 A) (-b23 A)
             (-b31 A) (-b32 A) (x-b33 A)).
Definition cubic (x : R) := x^3-101*x^2+20*x-1.
Definition cubic_discriminant (b c d : R) :=
  b^2*c^2-4*c^3-4*b^3*d-27*d^2+18*b*c*d.

Theorem integral_markings_unimodular : det3 gamma_a = 1 /\ det3 gamma_b = 1.
Proof. split; unfold det3, gamma_a, gamma_b; simpl; ring. Qed.
Theorem gamma_a_characteristic_polynomial : forall x, char3 gamma_a x = cubic x.
Proof. intro; unfold char3, det3, gamma_a, cubic; simpl; ring. Qed.
Theorem constant_cubic_discriminant : cubic_discriminant (-101) 20 (-1) = -36471.
Proof. unfold cubic_discriminant; ring. Qed.
Theorem cubic_no_unit_roots : cubic 1 <> 0 /\ cubic (-1) <> 0.
Proof. unfold cubic; split; simpl; nra. Qed.

Definition numerator_a (x y : R) := Mat2 (10-y) (x-1) 1 10.
Definition numerator_b (x y : R) := Mat2 (10+y) (1-x) (-1) 10.
Theorem numerator_a_determinant : forall x y,
  det2 (numerator_a x y) = 101-x-10*y.
Proof. intros; unfold det2, numerator_a; simpl; ring. Qed.
Theorem numerator_b_determinant : forall x y,
  det2 (numerator_b x y) = 101-x+10*y.
Proof. intros; unfold det2, numerator_b; simpl; ring. Qed.

Definition normalized_a (x y : R) :=
  scale2 (/sqrt (101-x-10*y)) (numerator_a x y).
Definition normalized_b (x y : R) :=
  scale2 (/sqrt (101-x+10*y)) (numerator_b x y).

Lemma normalize_determinant : forall A d,
  0 < d -> det2 A = d -> det2 (scale2 (/sqrt d) A) = 1.
Proof.
  intros A d Hd HA. rewrite det2_scale, HA.
  pose proof (sqrt_lt_R0 d Hd) as Hs.
  pose proof (Rsqr_sqrt d (Rlt_le _ _ Hd)) as Hsq.
  unfold Rsqr in Hsq.
  replace d with (sqrt d * sqrt d) at 3 by nra.
  field; lra.
Qed.

Theorem normalized_a_unimodular : forall x y,
  0 < 101-x-10*y -> det2 (normalized_a x y) = 1.
Proof. intros; apply normalize_determinant; auto using numerator_a_determinant. Qed.
Theorem normalized_b_unimodular : forall x y,
  0 < 101-x+10*y -> det2 (normalized_b x y) = 1.
Proof. intros; apply normalize_determinant; auto using numerator_b_determinant. Qed.

(* Section 4.4: nonorthogonality forces the trace amplitude to exceed 2. *)
Definition amplitude_squared (A : mat2) :=
  (a11 A+a22 A)^2+(a12 A-a21 A)^2.

Theorem amplitude_identity : forall A,
  amplitude_squared A = 4*det2 A + (a11 A-a22 A)^2+(a12 A+a21 A)^2.
Proof. intros []; unfold amplitude_squared, det2; simpl; ring. Qed.

Lemma equal_diagonal_opposite_offdiagonal_orthogonal : forall A,
  det2 A = 1 -> a11 A = a22 A -> a12 A = -a21 A -> orthogonal2 A.
Proof.
  intros [a b c d] Hd Ha Hb.
  unfold det2 in Hd; simpl in *. unfold orthogonal2, mul2, transpose2, id2; simpl.
  apply mat2_ext; simpl; nra.
Qed.

Theorem nonorthogonal_amplitude : forall A,
  det2 A = 1 -> ~orthogonal2 A -> 4 < amplitude_squared A.
Proof.
  intros A Hd Hn. rewrite amplitude_identity, Hd.
  pose proof (pow2_ge_0 (a11 A-a22 A)) as Hsq1.
  pose proof (pow2_ge_0 (a12 A+a21 A)) as Hsq2.
  destruct (Req_dec (a11 A) (a22 A)) as [Ha|Ha].
  - destruct (Req_dec (a12 A) (-a21 A)) as [Hb|Hb].
    + exfalso; apply Hn; now apply equal_diagonal_opposite_offdiagonal_orthogonal.
    + assert (Hs : 0 < (a12 A+a21 A)^2).
      { pose proof (Rlt_0_sqr (a12 A+a21 A) ltac:(lra)); unfold Rsqr in *; nra. } nra.
  - assert (Hs : 0 < (a11 A-a22 A)^2).
    { pose proof (Rlt_0_sqr (a11 A-a22 A) ltac:(lra)); unfold Rsqr in *; nra. } nra.
Qed.

Definition rotation (theta : R) := Mat2 (cos theta) (-sin theta) (sin theta) (cos theta).
Theorem rotation_trace_formula : forall theta A,
  trace2 (mul2 (rotation theta) A) =
  (a11 A+a22 A)*cos theta + (a12 A-a21 A)*sin theta.
Proof. intros theta []; unfold trace2, mul2, rotation; simpl; ring. Qed.

Theorem rotation_unimodular : forall theta, det2 (rotation theta) = 1.
Proof.
  intro theta. pose proof (sin2_cos2 theta).
  unfold det2, rotation; simpl. unfold Rsqr in *. nra.
Qed.

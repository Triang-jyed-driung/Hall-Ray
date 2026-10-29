From Stdlib Require Import Reals Psatz Lia ZArith.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralCubic.
Open Scope R_scope.

Definition id3 := Mat3 1 0 0 0 1 0 0 0 1.
Definition trace3 (A : mat3) := b11 A+b22 A+b33 A.
Definition second3 (A : mat3) :=
  b11 A*b22 A-b12 A*b21 A+b11 A*b33 A-b13 A*b31 A+b22 A*b33 A-b23 A*b32 A.
Definition triangular3 (a v w : R) (B : mat2) :=
  Mat3 a v w 0 (a11 B) (a12 B) 0 (a21 B) (a22 B).
Fixpoint power3 (A : mat3) (n : nat) :=
  match n with O => id3 | S k => mul3 A (power3 A k) end.

Lemma mul3_assoc : forall A B C, mul3 (mul3 A B) C = mul3 A (mul3 B C).
Proof. intros [] [] []; apply mat3_ext; unfold mul3; simpl; ring. Qed.
Lemma mul3_id_left : forall A, mul3 id3 A = A.
Proof. intros []; apply mat3_ext; unfold mul3, id3; simpl; ring. Qed.
Lemma mul3_id_right : forall A, mul3 A id3 = A.
Proof. intros []; apply mat3_ext; unfold mul3, id3; simpl; ring. Qed.
Lemma mul3_determinant : forall A B, det3 (mul3 A B) = det3 A*det3 B.
Proof. intros [] []; unfold det3, mul3; simpl; ring. Qed.
Lemma power3_unimodular : forall A n, det3 A = 1 -> det3 (power3 A n) = 1.
Proof.
  intros A n HA. induction n; simpl.
  - unfold det3, id3; simpl; ring.
  - rewrite mul3_determinant, HA, IHn; ring.
Qed.
Lemma hx_inverse_left : forall x y, mul3 (hx (-x) (-y)) (hx x y) = id3.
Proof. intros; apply mat3_ext; unfold mul3, hx, id3; simpl; ring. Qed.
Lemma hx_inverse_right : forall x y, mul3 (hx x y) (hx (-x) (-y)) = id3.
Proof. intros; apply mat3_ext; unfold mul3, hx, id3; simpl; ring. Qed.

Lemma triangular3_product : forall a v w B c u z C,
  mul3 (triangular3 a v w B) (triangular3 c u z C) =
  triangular3 (a*c) (a*u+v*a11 C+w*a21 C) (a*z+v*a12 C+w*a22 C) (mul2 B C).
Proof. intros; apply mat3_ext; unfold mul3, triangular3, mul2; simpl; ring. Qed.
Lemma triangular3_determinant : forall a v w B,
  det3 (triangular3 a v w B) = a*det2 B.
Proof. intros a v w []; unfold det3, triangular3, det2; simpl; ring. Qed.

Lemma characteristic_coefficients : forall A x,
  char3 A x = x^3-trace3 A*x^2+second3 A*x-det3 A.
Proof. intros [] x; unfold char3, trace3, second3, det3; simpl; ring. Qed.
Lemma characteristic_hx_conjugation : forall x y A t,
  char3 (mul3 (mul3 (hx x y) A) (hx (-x) (-y))) t = char3 A t.
Proof. intros x y [] t; unfold char3, det3, mul3, hx; simpl; ring. Qed.
Lemma characteristic_repeated_block : forall a b v w t,
  char3 (triangular3 a v w (scale2 b id2)) t = (t-a)*(t-b)^2.
Proof. intros; unfold char3, det3, triangular3, scale2, id2; simpl; ring. Qed.

Record zmat3 := ZMat3 {
  z11 : Z; z12 : Z; z13 : Z;
  z21 : Z; z22 : Z; z23 : Z;
  z31 : Z; z32 : Z; z33 : Z
}.
Definition real3 (A : zmat3) := Mat3
  (IZR (z11 A)) (IZR (z12 A)) (IZR (z13 A))
  (IZR (z21 A)) (IZR (z22 A)) (IZR (z23 A))
  (IZR (z31 A)) (IZR (z32 A)) (IZR (z33 A)).
Definition zid3 := ZMat3 1 0 0 0 1 0 0 0 1.
Definition zmul3 (A B : zmat3) := ZMat3
  (z11 A*z11 B+z12 A*z21 B+z13 A*z31 B)
  (z11 A*z12 B+z12 A*z22 B+z13 A*z32 B)
  (z11 A*z13 B+z12 A*z23 B+z13 A*z33 B)
  (z21 A*z11 B+z22 A*z21 B+z23 A*z31 B)
  (z21 A*z12 B+z22 A*z22 B+z23 A*z32 B)
  (z21 A*z13 B+z22 A*z23 B+z23 A*z33 B)
  (z31 A*z11 B+z32 A*z21 B+z33 A*z31 B)
  (z31 A*z12 B+z32 A*z22 B+z33 A*z32 B)
  (z31 A*z13 B+z32 A*z23 B+z33 A*z33 B).
Fixpoint zpower3 (A : zmat3) (n : nat) :=
  match n with O => zid3 | S k => zmul3 A (zpower3 A k) end.

Lemma real3_product : forall A B, real3 (zmul3 A B) = mul3 (real3 A) (real3 B).
Proof.
  intros [] []; apply mat3_ext; unfold zmul3, real3, mul3; simpl;
    repeat first [rewrite plus_IZR|rewrite mult_IZR]; reflexivity.
Qed.
Lemma real3_identity : real3 zid3 = id3.
Proof. reflexivity. Qed.
Lemma real3_power : forall A n, real3 (zpower3 A n) = power3 (real3 A) n.
Proof. intros A n; induction n; simpl; [reflexivity|]. rewrite real3_product, IHn; reflexivity. Qed.

Definition ztrace3 (A : zmat3) := (z11 A+z22 A+z33 A)%Z.
Definition zsecond3 (A : zmat3) :=
  (z11 A*z22 A-z12 A*z21 A+z11 A*z33 A-z13 A*z31 A+z22 A*z33 A-z23 A*z32 A)%Z.
Definition zdet3 (A : zmat3) :=
  (z11 A*(z22 A*z33 A-z23 A*z32 A)-z12 A*(z21 A*z33 A-z23 A*z31 A)+
   z13 A*(z21 A*z32 A-z22 A*z31 A))%Z.

Lemma real3_trace : forall A, trace3 (real3 A) = IZR (ztrace3 A).
Proof. intros []; unfold real3, trace3, ztrace3; simpl; rewrite !plus_IZR; reflexivity. Qed.
Lemma real3_second : forall A, second3 (real3 A) = IZR (zsecond3 A).
Proof.
  intros []; unfold real3, second3, zsecond3; simpl.
  repeat first [rewrite plus_IZR|rewrite minus_IZR|rewrite mult_IZR]. reflexivity.
Qed.
Lemma real3_determinant : forall A, det3 (real3 A) = IZR (zdet3 A).
Proof.
  intros []; unfold real3, det3, zdet3; simpl.
  repeat first [rewrite plus_IZR|rewrite minus_IZR|rewrite mult_IZR]. reflexivity.
Qed.

Definition integral_matrix (A : mat3) := exists Z, real3 Z = A.
Lemma integral_identity : integral_matrix id3.
Proof. exists zid3; reflexivity. Qed.
Lemma integral_product : forall A B,
  integral_matrix A -> integral_matrix B -> integral_matrix (mul3 A B).
Proof.
  intros A B [ZA HA] [ZB HB]. exists (zmul3 ZA ZB). rewrite real3_product, HA, HB. reflexivity.
Qed.
Lemma integral_power : forall A n, integral_matrix A -> integral_matrix (power3 A n).
Proof. intros A n [ZA HA]. exists (zpower3 ZA n). rewrite real3_power, HA; reflexivity. Qed.
Theorem integral_characteristic_coefficients : forall A,
  integral_matrix A -> det3 A = 1 -> exists T S : Z,
    forall x, char3 A x = x^3-IZR T*x^2+IZR S*x-1.
Proof.
  intros A [ZA HA] Hd. exists (ztrace3 ZA), (zsecond3 ZA). intro x.
  rewrite characteristic_coefficients, <- HA.
  rewrite real3_trace, real3_second, HA, Hd. reflexivity.
Qed.

Theorem integral_matrix_no_repeated_contracting_block : forall A x y a b v w,
  integral_matrix A -> det3 A = 1 -> 1 < a -> 0 < b < 1 ->
  mul3 (mul3 (hx x y) A) (hx (-x) (-y)) = triangular3 a v w (scale2 b id2) -> False.
Proof.
  intros A x y a b v w HI HD Ha Hb Hconj.
  destruct (integral_characteristic_coefficients A HI HD) as [T [S Hpoly]].
  apply (integral_characteristic_no_double_contraction T S a b Ha Hb).
  intro t. rewrite <- Hpoly.
  rewrite <- (characteristic_hx_conjugation x y A t), Hconj, characteristic_repeated_block. reflexivity.
Qed.

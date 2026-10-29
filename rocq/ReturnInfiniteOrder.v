From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices MarkedCocycle
  FiberProducts SymbolicCoding SymbolicCocycle DefectLimit ConstantCoding
  EllipticConjugacy PeriodicReturns.
Open Scope R_scope.

Definition word_periodic (n : nat) (w : future) := forall k, w (n+k)%nat = w k.

Lemma periodic_unstable_frame : forall n w,
  word_periodic n w -> unstable_frame (shift_by n w) = unstable_frame w.
Proof.
  intros n w H. unfold unstable_frame.
  assert (HC : coded (shift_by n w) = coded w).
  { apply coded_extensional. intro k; apply H. }
  rewrite HC; reflexivity.
Qed.

Lemma power3_intertwining : forall H A T m,
  mul3 H A = mul3 T H -> mul3 H (power3 A m) = mul3 (power3 T m) H.
Proof.
  intros H A T m HT. induction m.
  - simpl. rewrite mul3_id_left, mul3_id_right; reflexivity.
  - cbn [power3]. rewrite <- mul3_assoc, HT, mul3_assoc, IHm, <- mul3_assoc. reflexivity.
Qed.

Lemma triangular_power_shape : forall a v z B m, exists u w,
  power3 (triangular3 a v z B) m = triangular3 (a^m) u w (matrix_power B m).
Proof.
  intros a v z B m. induction m.
  - exists 0, 0. apply mat3_ext; unfold power3, matrix_power, triangular3, id2, id3; simpl; ring.
  - destruct IHm as [u [w Hw]]. cbn [power3]. rewrite Hw, triangular3_product.
    eexists; eexists; reflexivity.
Qed.

Lemma scaled_matrix_power : forall r A m,
  matrix_power (scale2 r A) m = scale2 (r^m) (matrix_power A m).
Proof.
  intros r A m. induction m.
  - simpl. apply mat2_ext; unfold scale2, id2; simpl; ring.
  - cbn [matrix_power]. rewrite IHm, matrix_scale_product. reflexivity.
Qed.

Lemma real_power_expands : forall a m,
  1 < a -> (0 < m)%nat -> 1 < a^m.
Proof.
  intros a [|m] Ha Hm; [lia|]. cbn [pow].
  pose proof (pow_incr 1 a m ltac:(lra)) as Hpow. rewrite pow1 in Hpow.
  pose proof (Rmult_le_compat_l a _ _ ltac:(lra) Hpow). nra.
Qed.
Lemma real_power_contracts : forall b m,
  0 < b < 1 -> (0 < m)%nat -> 0 < b^m < 1.
Proof.
  intros b [|m] Hb Hm; [lia|]. split.
  - apply pow_lt; lra.
  - cbn [pow]. pose proof (pow_incr b 1 m ltac:(lra)) as Hpow. rewrite pow1 in Hpow.
    pose proof (Rmult_le_compat_l b _ _ ltac:(lra) Hpow). nra.
Qed.

(* No nonempty cyclic word can have a finite-order SL2 fiber return.
   This uses integrality and the elementary repeated-root obstruction only. *)
Theorem cyclic_cocycle_infinite_order : forall n w m,
  (0 < n)%nat -> word_periodic n w -> (0 < m)%nat ->
  matrix_power (fiber_product n w) m <> id2.
Proof.
  intros n w m Hn Hperiod Hm Hfinite.
  pose proof (marked_cocycle_product n w) as Hmarked.
  rewrite (periodic_unstable_frame n w Hperiod) in Hmarked.
  pose proof (power3_intertwining (unstable_frame w) (marking_product n w)
    (triangular_product n w) m Hmarked) as Hpower.
  pose proof (f_equal (fun X => mul3 X
    (hx (-fst (coded w)) (-snd (coded w)))) Hpower) as Hconj.
  change (mul3 (mul3 (unstable_frame w) (power3 (marking_product n w) m))
    (hx (-fst (coded w)) (-snd (coded w))) =
    mul3 (mul3 (power3 (triangular_product n w) m) (unstable_frame w))
      (hx (-fst (coded w)) (-snd (coded w)))) in Hconj.
  rewrite (mul3_assoc (power3 (triangular_product n w) m) (unstable_frame w)
    (hx (-fst (coded w)) (-snd (coded w)))) in Hconj.
  unfold unstable_frame in Hconj. rewrite hx_inverse_right, mul3_id_right in Hconj.
  destruct (triangular_product_shape n w) as [v [z Hshape]].
  rewrite Hshape in Hconj.
  destruct (triangular_power_shape (return_height n w) v z
    (scale2 (return_scale n w) (fiber_product n w)) m) as [u [t Htri]].
  rewrite Htri, scaled_matrix_power, Hfinite in Hconj.
  apply (integral_matrix_no_repeated_contracting_block (power3 (marking_product n w) m)
    (fst (coded w)) (snd (coded w)) ((return_height n w)^m) ((return_scale n w)^m) u t).
  - apply integral_power, marking_product_integral.
  - apply power3_unimodular, marking_product_unimodular.
  - apply real_power_expands; [apply return_height_expanding|]; assumption.
  - apply real_power_contracts; [apply return_scale_contracting|]; assumption.
  - exact Hconj.
Qed.

Theorem constant_return_infinite_order : forall m,
  (0 < m)%nat -> matrix_power constant_return m <> id2.
Proof.
  intros m Hm.
  pose proof (cyclic_cocycle_infinite_order 1 a_future m ltac:(lia) ltac:(intros k; reflexivity) Hm) as H.
  rewrite constant_future_product in H. cbn [matrix_power] in H.
  rewrite mul2_id_right in H. exact H.
Qed.

Theorem periodic_return_infinite_order : forall n m,
  (0 < m)%nat -> matrix_power (periodic_return n) m <> id2.
Proof.
  intros n m Hm. apply (cyclic_cocycle_infinite_order (S n) (periodic_future n) m); auto; try lia.
  intro k. replace (S n+k)%nat with (k+S n)%nat by lia. apply periodic_future_period.
Qed.

Theorem constant_rotation_infinite_order : forall m,
  (0 < m)%nat -> matrix_power constant_rotation m <> id2.
Proof.
  intros m Hm Hfinite. apply (constant_return_infinite_order m Hm).
  rewrite constant_power_reconstruction, Hfinite, mul2_id_right.
  apply unimodular_right_inverse, constant_basis_unimodular.
Qed.

Theorem conjugated_periodic_return_infinite_order : forall n G m,
  det2 G = 1 -> (0 < m)%nat ->
  matrix_power (mul2 (mul2 (adj2 G) (periodic_return n)) G) m <> id2.
Proof.
  intros n G m HG Hm Hfinite. apply (periodic_return_infinite_order n m Hm).
  pose proof (conjugation_power G (periodic_return n) m HG) as Hconj.
  rewrite Hfinite in Hconj.
  assert (Hundo := undo_conjugation G (matrix_power (periodic_return n) m) HG).
  rewrite Hconj, mul2_id_right, (unimodular_right_inverse G HG) in Hundo.
  symmetry; exact Hundo.
Qed.

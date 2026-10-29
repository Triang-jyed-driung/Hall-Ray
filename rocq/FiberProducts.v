From Stdlib Require Import Reals Psatz Lia List.
From HallRay Require Import MatrixAlgebra ScalarEstimates.
Import ListNotations.
Open Scope R_scope.

Definition add2 (A B : mat2) :=
  Mat2 (a11 A+a11 B) (a12 A+a12 B) (a21 A+a21 B) (a22 A+a22 B).
Definition sub2 (A B : mat2) := add2 A (scale2 (-1) B).
Definition zero2 := Mat2 0 0 0 0.
Fixpoint product (xs : list mat2) : mat2 :=
  match xs with [] => id2 | A::tail => mul2 A (product tail) end.
Definition relative_error (xs ys : list mat2) :=
  sub2 (mul2 (adj2 (product xs)) (product ys)) id2.

Lemma adj2_mul : forall A B, adj2 (mul2 A B) = mul2 (adj2 B) (adj2 A).
Proof. intros [] []; apply mat2_ext; unfold adj2, mul2; simpl; ring. Qed.

Lemma mul2_add_left : forall A B C,
  mul2 (add2 A B) C = add2 (mul2 A C) (mul2 B C).
Proof. intros [] [] []; apply mat2_ext; unfold mul2, add2; simpl; ring. Qed.
Lemma mul2_add_right : forall A B C,
  mul2 A (add2 B C) = add2 (mul2 A B) (mul2 A C).
Proof. intros [] [] []; apply mat2_ext; unfold mul2, add2; simpl; ring. Qed.

Lemma inverse_comparison : forall A B, det2 A = 1 ->
  mul2 (adj2 A) B = add2 (mul2 (adj2 A) (sub2 B A)) id2.
Proof.
  intros [a b c d] [] Hd. unfold det2 in Hd; simpl in Hd.
  apply mat2_ext; unfold mul2, adj2, add2, sub2, scale2, id2; simpl; nra.
Qed.

Theorem relative_error_step : forall A B xs ys,
  det2 A = 1 ->
  relative_error (A::xs) (B::ys) =
  add2 (mul2 (mul2 (mul2 (adj2 (product xs)) (adj2 A)) (sub2 B A)) (product ys))
       (relative_error xs ys).
Proof.
  intros A B xs ys Hd. unfold relative_error; simpl product.
  rewrite adj2_mul, !mul2_assoc.
  rewrite <- (mul2_assoc (adj2 A) B (product ys)).
  rewrite (inverse_comparison A B Hd), mul2_add_left, mul2_id_left, mul2_add_right.
  rewrite <- !mul2_assoc.
  generalize (mul2 (mul2 (mul2 (adj2 (product xs)) (adj2 A)) (sub2 B A)) (product ys)).
  generalize (mul2 (adj2 (product xs)) (product ys)).
  intros [] []; apply mat2_ext; unfold sub2, add2, scale2, id2; simpl; ring.
Qed.

(* A normed-matrix interface. These are explicit parameters of the estimates,
   not global axioms, and this file does not assert an unproved Euclidean
   instance or the paper's concrete Lipschitz bounds. *)
Record matrix_norm := {
  mnorm : mat2 -> R;
  mnorm_nonnegative : forall A, 0 <= mnorm A;
  mnorm_identity : mnorm id2 = 1;
  mnorm_zero : mnorm zero2 = 0;
  mnorm_submultiplicative : forall A B, mnorm (mul2 A B) <= mnorm A*mnorm B;
  mnorm_subadditive : forall A B, mnorm (add2 A B) <= mnorm A+mnorm B
}.

Section Estimates.
Variable nm : matrix_norm.
Local Abbreviation norm := (mnorm nm).

Lemma norm_product : forall xs b,
  0 <= b -> (forall A, In A xs -> norm A <= b) ->
  norm (product xs) <= b^(length xs).
Proof.
  induction xs as [|A xs IH]; intros b Hb Hbounds; simpl.
  - rewrite mnorm_identity. lra.
  - eapply Rle_trans; [apply mnorm_submultiplicative|].
    apply Rmult_le_compat; auto using mnorm_nonnegative.
    + apply Hbounds; simpl; auto.
    + apply IH; auto. intros B HB. apply Hbounds; simpl; auto.
Qed.

Lemma norm_inverse_product : forall xs b,
  0 <= b -> (forall A, In A xs -> norm (adj2 A) <= b) ->
  norm (adj2 (product xs)) <= b^(length xs).
Proof.
  induction xs as [|A xs IH]; intros b Hb Hbounds; simpl product; simpl length.
  - assert (adj2 id2 = id2) as H by (apply mat2_ext; simpl; ring).
    rewrite H, mnorm_identity. simpl; lra.
  - rewrite adj2_mul. eapply Rle_trans; [apply mnorm_submultiplicative|].
    rewrite Rmult_comm. apply Rmult_le_compat; auto using mnorm_nonnegative.
    + apply Hbounds; simpl; auto.
    + apply IH; auto. intros B HB. apply Hbounds; simpl; auto.
Qed.

(* local_close n N is exactly the decay pattern used in Lemma 3.6:
   the jth error is <= .08 * 900^(-(n+N-j-1)). *)
Inductive local_close : nat -> nat -> list mat2 -> list mat2 -> Prop :=
| close_nil : forall N, local_close O N [] []
| close_cons : forall n N A B xs ys,
    det2 A = 1 ->
    norm (adj2 A) <= 11/10 -> norm B <= 11/10 ->
    norm (sub2 B A) <= (2/25)*(1/900)^(N+n) ->
    local_close n N xs ys ->
    local_close (S n) N (A::xs) (B::ys).

Lemma local_close_lengths : forall n N xs ys,
  local_close n N xs ys -> length xs = n /\ length ys = n.
Proof.
  intros n N xs ys H. induction H; simpl; [auto|].
  destruct IHlocal_close. split; congruence.
Qed.

Lemma local_close_norms : forall n N xs ys,
  local_close n N xs ys ->
  (forall A, In A xs -> norm (adj2 A) <= 11/10) /\
  (forall B, In B ys -> norm B <= 11/10).
Proof.
  intros n N xs ys H. induction H as [N|n N A B xs ys Hd HA HB He Htail [IHx IHy]].
  - split; intros C HC; inversion HC.
  - split; intros C [HC|HC]; subst; auto.
Qed.

Lemma geometric_sum_last : forall x n,
  geometric_sum x (S n) = geometric_sum x n+x^n.
Proof.
  intros x n. induction n; [simpl; ring|].
  change (1+x*geometric_sum x (S n) = (1+x*geometric_sum x n)+x^(S n)).
  rewrite IHn. simpl. ring.
Qed.

Theorem relative_product_estimate : forall n N xs ys,
  local_close n N xs ys ->
  norm (relative_error xs ys) <=
    (11/125)*(1/900)^N*geometric_sum ((11/10)^2/900) n.
Proof.
  intros n N xs ys Hclose.
  induction Hclose as [N|n N A B xs ys Hd HA HB He Htail IH].
  - unfold relative_error; simpl product.
    assert (sub2 (mul2 (adj2 id2) id2) id2 = zero2) as Hzero
      by (apply mat2_ext; simpl; ring).
    rewrite Hzero, mnorm_zero. simpl. lra.
  - destruct (local_close_lengths _ _ _ _ Htail) as [Hlenx Hleny].
    destruct (local_close_norms _ _ _ _ Htail) as [Hnx Hny].
    pose proof (norm_inverse_product xs (11/10) ltac:(lra) Hnx) as HX.
    pose proof (norm_product ys (11/10) ltac:(lra) Hny) as HY.
    rewrite Hlenx in HX. rewrite Hleny in HY.
    rewrite (relative_error_step A B xs ys Hd).
    eapply Rle_trans; [apply mnorm_subadditive|].
    assert (HT : norm (mul2 (mul2 (mul2 (adj2 (product xs)) (adj2 A)) (sub2 B A)) (product ys)) <=
                 (11/10)^n*(11/10)*((2/25)*(1/900)^(N+n))*(11/10)^n).
    { eapply Rle_trans; [apply mnorm_submultiplicative|].
      apply Rmult_le_compat; auto using mnorm_nonnegative.
      eapply Rle_trans; [apply mnorm_submultiplicative|].
      apply Rmult_le_compat; auto using mnorm_nonnegative.
      eapply Rle_trans; [apply mnorm_submultiplicative|].
      apply Rmult_le_compat; auto using mnorm_nonnegative. }
    assert (Hpower : (11/10)^n*(11/10)*((2/25)*(1/900)^(N+n))*(11/10)^n =
      (11/125)*(1/900)^N*((11/10)^2/900)^n).
    { rewrite pow_add.
      replace (((11/10)^2/900)^n) with (((11/10)^n*(11/10)^n)*(1/900)^n).
      - field.
      - rewrite <- !Rpow_mult_distr. f_equal. simpl. field. }
    rewrite Hpower in HT. rewrite geometric_sum_last. nra.
Qed.

Theorem uniform_fiber_bound : forall n N xs ys,
  local_close n N xs ys -> norm (relative_error xs ys) <= (1/600)^N.
Proof.
  intros n N xs ys Hclose.
  pose proof (relative_product_estimate _ _ _ _ Hclose) as H.
  pose proof (fiber_geometric_constant n) as HG.
  assert (Heq : (2/25)*(11/10) = 11/125) by field.
  rewrite Heq in HG.
  pose proof (pow_le (1/900) N ltac:(lra)) as HP.
  pose proof (pow_incr (1/900) (1/600) N ltac:(lra)) as Hpow.
  nra.
Qed.
End Estimates.

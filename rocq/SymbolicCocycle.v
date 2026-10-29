From Stdlib Require Import Reals Psatz Lia List.
From HallRay Require Import MatrixAlgebra ReturnBranches SymbolicCoding
  FiberProducts EuclideanNorm ConcreteCocycle.
Import ListNotations.
Open Scope R_scope.

(* This is M(z) = M_{z(0)}(u(sigma z)), not an abstract cocycle. *)
Definition cocycle (w : future) :=
  fiber_matrix (w O) (fst (coded (shift w))) (snd (coded (shift w))).
Fixpoint factors (n : nat) (w : future) : list mat2 :=
  match n with O => [] | S k => cocycle w::factors k (shift w) end.
Definition fiber_product (n : nat) (w : future) := product (factors n w).
Definition same_prefix (n : nat) (w z : future) := forall k, (k < n)%nat -> w k = z k.

Lemma cocycle_unimodular : forall w, det2 (cocycle w) = 1.
Proof. intro w. apply fiber_matrix_unimodular. exact (coded_inside (shift w)). Qed.
Lemma cocycle_bounds : forall w,
  opnorm (cocycle w) <= 26/25 /\ opnorm (adj2 (cocycle w)) <= 26/25.
Proof. intro w. apply fiber_matrix_uniform_bounds. exact (coded_inside (shift w)). Qed.

Lemma factor_product_unimodular : forall n w, det2 (fiber_product n w) = 1.
Proof.
  induction n; intro w; unfold fiber_product in *; simpl.
  - unfold det2, id2; simpl; ring.
  - rewrite det2_mul, cocycle_unimodular, IHn. ring.
Qed.

Theorem symbolic_local_close : forall n N w z,
  same_prefix (n+N) w z ->
  local_close euclidean_matrix_norm n N (factors n w) (factors n z).
Proof.
  induction n as [|n IH]; intros N w z Hsame; simpl.
  - constructor.
  - assert (Hhead : w O = z O) by (apply Hsame; lia).
    assert (Htail : same_prefix (n+N) (shift w) (shift z)).
    { intros k Hk. unfold shift. apply Hsame; lia. }
    assert (Hcoords : close ((2/5)*(1/900)^(N+n)) (coded (shift z)) (coded (shift w))).
    { apply common_future_estimate. intros k Hk. symmetry. apply Htail; lia. }
    pose proof (cocycle_bounds w) as Hw. pose proof (cocycle_bounds z) as Hz.
    constructor.
    + apply cocycle_unimodular.
    + change (opnorm (adj2 (cocycle w)) <= 11/10). lra.
    + change (opnorm (cocycle z) <= 11/10). lra.
    + change (opnorm (sub2 (cocycle z) (cocycle w)) <= (2/25)*(1/900)^(N+n)).
      unfold cocycle. rewrite <- Hhead.
      pose proof (fiber_matrix_lipschitz (w O)
        (fst (coded (shift z))) (snd (coded (shift z)))
        (fst (coded (shift w))) (snd (coded (shift w))) ((2/5)*(1/900)^(N+n))
        (coded_inside (shift z)) (coded_inside (shift w))
        ltac:(apply Rmult_le_pos; [lra|apply pow_le; lra])
        (proj1 Hcoords) (proj2 Hcoords)) as HL.
      nra.
    + apply IH. exact Htail.
Qed.

(* Lemma 3.6 for the actual, concrete Euclidean matrix cocycle. *)
Theorem symbolic_uniform_fiber_bound : forall n N w z,
  same_prefix (n+N) w z ->
  opnorm (sub2 (mul2 (adj2 (fiber_product n w)) (fiber_product n z)) id2) <= (1/600)^N.
Proof.
  intros n N w z Hsame.
  exact (uniform_fiber_bound euclidean_matrix_norm n N _ _
    (symbolic_local_close n N w z Hsame)).
Qed.

Theorem fiber_product_inverse_identity : forall n w,
  mul2 (fiber_product n w) (adj2 (fiber_product n w)) = id2.
Proof.
  intros n w. rewrite mul2_adj_right, factor_product_unimodular.
  apply mat2_ext; unfold scale2, id2; simpl; ring.
Qed.

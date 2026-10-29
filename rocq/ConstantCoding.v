From Stdlib Require Import Reals Psatz Lia.
From HallRay Require Import MatrixAlgebra FiberProducts ReturnBranches Contraction SymbolicCoding
  ScalarEstimates ConstantReturn SymbolicCocycle DefectLimit.
Open Scope R_scope.

Lemma branch_fixed_point_unique : forall s p q,
  inside p -> inside q -> branch s p = p -> branch s q = q -> p = q.
Proof.
  intros s [x y] [u v] Hp Hq Hfp Hfq.
  set (e := Rmax (Rabs (x-u)) (Rabs (y-v))).
  assert (He : 0 <= e).
  { unfold e. pose proof (Rmax_l (Rabs (x-u)) (Rabs (y-v))). pose proof (Rabs_pos (x-u)). lra. }
  assert (Hclose : close e (x,y) (u,v)).
  { split; simpl; [apply Rmax_l|apply Rmax_r]. }
  pose proof (branch_contraction s (x,y) (u,v) e Hp Hq He Hclose) as HC.
  rewrite Hfp, Hfq in HC. unfold close in HC; simpl in HC.
  assert (He' : e <= e/900) by (unfold e at 1; apply Rmax_lub; tauto).
  assert (Hx : x = u).
  { destruct (Req_dec x u); auto. pose proof (Rabs_pos_lt (x-u) ltac:(lra)). lra. }
  assert (Hy : y = v).
  { destruct (Req_dec y v); auto. pose proof (Rabs_pos_lt (y-v) ltac:(lra)). lra. }
  subst; reflexivity.
Qed.

Lemma algebraic_fixed_point_inside : forall alpha, 100 < alpha ->
  in_U (fixed_u1 alpha) (fixed_u2 alpha).
Proof.
  intros alpha Ha.
  assert (Hinv : 0 < /alpha) by (apply Rinv_0_lt_compat; lra).
  assert (Hinvbound : /alpha < 1/100).
  { apply (Rmult_lt_reg_r alpha); [lra|].
    replace (/alpha*alpha) with 1 by (field; lra). nra. }
  unfold in_U, fixed_u1, fixed_u2.
  replace (10/alpha-1/alpha^2) with ((10- /alpha)/alpha) by (field; lra).
  split.
  - split; apply (Rmult_le_reg_r alpha); try lra;
      replace ((10- /alpha)/alpha*alpha) with (10- /alpha) by (field; lra); nra.
  - unfold Rdiv. nra.
Qed.

Theorem constant_coding_formula : forall alpha,
  100 < alpha -> cubic alpha = 0 -> coded a_future = (fixed_u1 alpha,fixed_u2 alpha).
Proof.
  intros alpha Ha Hf.
  apply (branch_fixed_point_unique true).
  - apply coded_inside.
  - exact (algebraic_fixed_point_inside alpha Ha).
  - symmetry. exact (coded_recursion a_future).
  - destruct (fixed_point_formula alpha Ha Hf) as [H1 H2].
    unfold branch; simpl. rewrite H1, H2. reflexivity.
Qed.

Theorem constant_return_formula : forall alpha,
  100 < alpha -> cubic alpha = 0 -> constant_return = constant_matrix alpha.
Proof.
  intros alpha Ha Hf. unfold constant_return, cocycle.
  change (normalized_a (fst (coded a_future)) (snd (coded a_future)) = constant_matrix alpha).
  rewrite (constant_coding_formula alpha Ha Hf). simpl.
  symmetry; apply constant_matrix_is_cocycle; assumption.
Qed.

Theorem concrete_constant_return_elliptic : Rabs (trace2 constant_return) < 2.
Proof.
  destruct constant_root_exists as [alpha [Ha Hf]].
  rewrite (constant_return_formula alpha ltac:(lra) Hf).
  apply constant_return_elliptic; lra.
Qed.

Theorem concrete_constant_return_lower_left_positive : 0 < a21 constant_return.
Proof.
  destruct constant_root_exists as [alpha [Ha Hf]].
  rewrite (constant_return_formula alpha ltac:(lra) Hf).
  unfold constant_matrix, scale2; simpl.
  rewrite Rmult_1_r. apply Rinv_0_lt_compat, sqrt_lt_R0; lra.
Qed.

Theorem cubic_monotone_large : forall a b,
  100 <= a -> a < b -> cubic a < cubic b.
Proof.
  intros a b Ha Hab.
  assert (Hk : 0 < a*a+a*b+b*b-101*(a+b)+20).
  { pose proof (Rmult_le_pos (a-100) (b-100) ltac:(lra) ltac:(lra)).
    pose proof (pow2_ge_0 (a-100)). pose proof (pow2_ge_0 (b-100)). nra. }
  unfold cubic. nra.
Qed.

Theorem constant_root_fine_isolation : forall alpha,
  100 < alpha -> cubic alpha = 0 ->
  100801689041906829488/1000000000000000000 < alpha <
  100801689041906829489/1000000000000000000.
Proof.
  intros alpha Ha Hf.
  assert (Hl : cubic (100801689041906829488/1000000000000000000) < 0)
    by (unfold cubic; simpl; nra).
  assert (Hr : 0 < cubic (100801689041906829489/1000000000000000000))
    by (unfold cubic; simpl; nra).
  split.
  - destruct (Rlt_dec (100801689041906829488/1000000000000000000) alpha); auto.
    destruct (Req_dec alpha (100801689041906829488/1000000000000000000)); [subst; lra|].
    pose proof (cubic_monotone_large alpha (100801689041906829488/1000000000000000000)
      ltac:(lra) ltac:(lra)). lra.
  - destruct (Rlt_dec alpha (100801689041906829489/1000000000000000000)); auto.
    destruct (Req_dec alpha (100801689041906829489/1000000000000000000)); [subst; lra|].
    pose proof (cubic_monotone_large (100801689041906829489/1000000000000000000) alpha
      ltac:(lra) ltac:(lra)). lra.
Qed.

Definition defect_u1 alpha := phi_b1 (fixed_u1 alpha) (fixed_u2 alpha).
Definition defect_u2 alpha := phi_b2 (fixed_u1 alpha) (fixed_u2 alpha).
Definition preceding_u1 alpha := phi_a1 (defect_u1 alpha) (defect_u2 alpha).
Definition preceding_u2 alpha := phi_a2 (defect_u1 alpha) (defect_u2 alpha).
Definition explicit_defect_product_two alpha :=
  mul2 (normalized_a (preceding_u1 alpha) (preceding_u2 alpha))
    (mul2 (normalized_a (defect_u1 alpha) (defect_u2 alpha))
          (normalized_b (fixed_u1 alpha) (fixed_u2 alpha))).
Definition explicit_defect_two alpha :=
  mul2 (matrix_power (adj2 (constant_matrix alpha)) 2) (explicit_defect_product_two alpha).

Theorem defect_two_formula : forall alpha,
  100 < alpha -> cubic alpha = 0 -> defect_sequence 2 = explicit_defect_two alpha.
Proof.
  intros alpha Ha Hf.
  assert (H0 : coded (one_defect O) = (defect_u1 alpha,defect_u2 alpha)).
  { rewrite (coded_recursion (one_defect O)).
    change (branch false (coded a_future) = (defect_u1 alpha,defect_u2 alpha)).
    rewrite (constant_coding_formula alpha Ha Hf). reflexivity. }
  assert (H1 : coded (one_defect 1) = (preceding_u1 alpha,preceding_u2 alpha)).
  { rewrite (coded_recursion (one_defect 1)).
    change (branch true (coded (one_defect O)) = (preceding_u1 alpha,preceding_u2 alpha)).
    rewrite H0. reflexivity. }
  unfold defect_sequence. rewrite (constant_return_formula alpha Ha Hf).
  unfold defect_product, fiber_product. simpl factors. simpl product.
  rewrite mul2_id_right.
  unfold cocycle. rewrite one_defect_shift, one_defect_shift.
  change (mul2 (matrix_power (adj2 (constant_matrix alpha)) 2)
    (mul2 (normalized_a (fst (coded (one_defect 1))) (snd (coded (one_defect 1))))
      (mul2 (normalized_a (fst (coded (one_defect O))) (snd (coded (one_defect O))))
        (normalized_b (fst (coded a_future)) (snd (coded a_future))))) = explicit_defect_two alpha).
  rewrite H1, H0, (constant_coding_formula alpha Ha Hf). reflexivity.
Qed.

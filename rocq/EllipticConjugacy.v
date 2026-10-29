From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  SymbolicCocycle ConstantCoding DefectLimit DefectNoncommuting.
Open Scope R_scope.

Lemma unit_scale_identity : scale2 1 id2 = id2.
Proof. apply mat2_ext; unfold scale2, id2; simpl; ring. Qed.
Lemma unimodular_right_inverse : forall A, det2 A = 1 -> mul2 A (adj2 A) = id2.
Proof. intros A HA. rewrite mul2_adj_right, HA, unit_scale_identity. reflexivity. Qed.

Lemma special_orthogonal_shape : forall A,
  det2 A = 1 -> orthogonal2 A -> a11 A = a22 A /\ a12 A = -a21 A.
Proof.
  intros A Hd Ho. unfold orthogonal2 in Ho.
  pose proof (f_equal (fun X => mul2 X (adj2 A)) Ho) as H.
  change (mul2 (mul2 (transpose2 A) A) (adj2 A) = mul2 id2 (adj2 A)) in H.
  rewrite mul2_assoc, (unimodular_right_inverse A Hd), mul2_id_right, mul2_id_left in H.
  pose proof (f_equal a11 H). pose proof (f_equal a12 H).
  unfold transpose2, adj2 in *; simpl in *. split; lra.
Qed.

Theorem special_orthogonal_commute : forall A B,
  det2 A = 1 -> orthogonal2 A -> det2 B = 1 -> orthogonal2 B ->
  mul2 A B = mul2 B A.
Proof.
  intros [a b c d] [u v w z] Hd HA He HB.
  destruct (special_orthogonal_shape _ Hd HA) as [Ha Hb].
  destruct (special_orthogonal_shape _ He HB) as [Hu Hv].
  simpl in *. subst a b u v. apply mat2_ext; unfold mul2; simpl; ring.
Qed.

(* An explicit upper triangular conjugator for any elliptic SL2 matrix with
   positive lower-left entry. No spectral theorem or conjugacy is assumed. *)
Definition elliptic_cosine (A : mat2) := trace2 A/2.
Definition elliptic_sine (A : mat2) := sqrt (1-(elliptic_cosine A)^2).
Definition elliptic_scale (A : mat2) := sqrt (elliptic_sine A/a21 A).
Definition elliptic_basis (A : mat2) :=
  Mat2 (elliptic_scale A)
       (elliptic_scale A*(a11 A-elliptic_cosine A)/elliptic_sine A)
       0 (/elliptic_scale A).
Definition elliptic_rotation (A : mat2) :=
  Mat2 (elliptic_cosine A) (-elliptic_sine A) (elliptic_sine A) (elliptic_cosine A).

Lemma elliptic_cosine_range : forall A,
  Rabs (trace2 A) < 2 -> -1 < elliptic_cosine A < 1.
Proof.
  intros A H. apply Rabs_def2 in H. unfold elliptic_cosine; lra.
Qed.
Lemma elliptic_sine_positive : forall A,
  Rabs (trace2 A) < 2 -> 0 < elliptic_sine A.
Proof.
  intros A H. pose proof (elliptic_cosine_range A H).
  unfold elliptic_sine. apply sqrt_lt_R0. nra.
Qed.
Lemma elliptic_circle_equation : forall A,
  Rabs (trace2 A) < 2 -> (elliptic_cosine A)^2+(elliptic_sine A)^2 = 1.
Proof.
  intros A H. pose proof (elliptic_cosine_range A H).
  unfold elliptic_sine. rewrite pow2_sqrt; nra.
Qed.
Lemma elliptic_scale_positive : forall A,
  Rabs (trace2 A) < 2 -> 0 < a21 A -> 0 < elliptic_scale A.
Proof.
  intros A HA Hc. unfold elliptic_scale.
  apply sqrt_lt_R0, Rdiv_lt_0_compat; auto using elliptic_sine_positive.
Qed.
Lemma elliptic_scale_equation : forall A,
  Rabs (trace2 A) < 2 -> 0 < a21 A ->
  (elliptic_scale A)^2*a21 A = elliptic_sine A.
Proof.
  intros A HA Hc.
  assert (Hpos : 0 <= elliptic_sine A/a21 A).
  { apply Rlt_le, Rdiv_lt_0_compat; auto using elliptic_sine_positive. }
  unfold elliptic_scale. rewrite pow2_sqrt by exact Hpos. field; lra.
Qed.

Theorem elliptic_basis_unimodular : forall A,
  Rabs (trace2 A) < 2 -> 0 < a21 A -> det2 (elliptic_basis A) = 1.
Proof.
  intros A HA Hc. pose proof (elliptic_scale_positive A HA Hc).
  pose proof (elliptic_sine_positive A HA).
  unfold det2, elliptic_basis; simpl; field; try split; lra.
Qed.

Theorem elliptic_rotation_special_orthogonal : forall A,
  Rabs (trace2 A) < 2 ->
  det2 (elliptic_rotation A) = 1 /\ orthogonal2 (elliptic_rotation A).
Proof.
  intros A HA. pose proof (elliptic_circle_equation A HA).
  split.
  - unfold det2, elliptic_rotation; simpl; nra.
  - unfold orthogonal2. apply mat2_ext;
      unfold mul2, transpose2, elliptic_rotation, id2; simpl; nra.
Qed.

Theorem elliptic_intertwining : forall A,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> 0 < a21 A ->
  mul2 A (elliptic_basis A) = mul2 (elliptic_basis A) (elliptic_rotation A).
Proof.
  intros A Hd HA Hc.
  pose proof (elliptic_sine_positive A HA) as Hs.
  pose proof (elliptic_scale_positive A HA Hc) as Hp.
  pose proof (elliptic_scale_equation A HA Hc) as Hscale.
  pose proof (elliptic_circle_equation A HA) as Hcircle.
  assert (Htrace : a11 A+a22 A = 2*elliptic_cosine A)
    by (unfold elliptic_cosine, trace2; field).
  assert (Hrel : (a11 A-elliptic_cosine A)^2+(elliptic_sine A)^2 = -a12 A*a21 A).
  { unfold det2 in Hd. nra. }
  apply mat2_ext; unfold mul2, elliptic_basis, elliptic_rotation; simpl.
  - field; lra.
  - apply (Rmult_eq_reg_r (elliptic_scale A*elliptic_sine A)); [|nra].
    field_simplify; try split; try lra.
    assert (Hscaled : (elliptic_scale A)^2*
      ((a11 A-elliptic_cosine A)^2+(elliptic_sine A)^2) = -a12 A*elliptic_sine A).
    { rewrite Hrel.
      replace ((elliptic_scale A)^2*(-a12 A*a21 A)) with
        (-a12 A*((elliptic_scale A)^2*a21 A)) by ring.
      rewrite Hscale. reflexivity. }
    nra.
  - apply (Rmult_eq_reg_r (elliptic_scale A)); [|lra].
    field_simplify; nra.
  - apply (Rmult_eq_reg_r (elliptic_scale A*elliptic_sine A)); [|nra].
    field_simplify; try split; try lra; nra.
Qed.

Theorem elliptic_conjugacy : forall A,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> 0 < a21 A ->
  mul2 (mul2 (adj2 (elliptic_basis A)) A) (elliptic_basis A) = elliptic_rotation A.
Proof.
  intros A Hd HA Hc.
  rewrite mul2_assoc, (elliptic_intertwining A Hd HA Hc), <- mul2_assoc.
  rewrite adjugate_left_identity; [apply mul2_id_left|].
  apply elliptic_basis_unimodular; assumption.
Qed.

Lemma conjugation_product : forall G A B, det2 G = 1 ->
  mul2 (mul2 (mul2 (adj2 G) A) G) (mul2 (mul2 (adj2 G) B) G) =
  mul2 (mul2 (adj2 G) (mul2 A B)) G.
Proof.
  intros G A B HG. rewrite !mul2_assoc.
  rewrite <- (mul2_assoc G (adj2 G) (mul2 B G)).
  rewrite (unimodular_right_inverse G HG), mul2_id_left. reflexivity.
Qed.

Lemma undo_conjugation : forall G A, det2 G = 1 ->
  mul2 (mul2 G (mul2 (mul2 (adj2 G) A) G)) (adj2 G) = A.
Proof.
  intros G A HG. rewrite !mul2_assoc.
  rewrite (unimodular_right_inverse G HG), mul2_id_right, <- mul2_assoc.
  rewrite (unimodular_right_inverse G HG), mul2_id_left. reflexivity.
Qed.

Theorem conjugated_defect_nonorthogonal : forall G,
  det2 G = 1 -> orthogonal2 (mul2 (mul2 (adj2 G) constant_return) G) ->
  ~orthogonal2 (mul2 (mul2 (adj2 G) defect_limit) G).
Proof.
  intros G HG HA HB. apply defect_limit_noncommuting.
  assert (HCdet : det2 constant_return = 1) by apply cocycle_unimodular.
  assert (HdetA : det2 (mul2 (mul2 (adj2 G) constant_return) G) = 1).
  { rewrite !det2_mul, adjugate_determinant, HG, HCdet. ring. }
  assert (HdetB : det2 (mul2 (mul2 (adj2 G) defect_limit) G) = 1).
  { rewrite !det2_mul, adjugate_determinant, HG, defect_limit_unimodular. ring. }
  pose proof (special_orthogonal_commute _ _ HdetA HA HdetB HB) as HC.
  rewrite !conjugation_product in HC by exact HG.
  pose proof (f_equal (fun X => mul2 (mul2 G X) (adj2 G)) HC) as H.
  change (mul2 (mul2 G (mul2 (mul2 (adj2 G) (mul2 constant_return defect_limit)) G)) (adj2 G) =
          mul2 (mul2 G (mul2 (mul2 (adj2 G) (mul2 defect_limit constant_return)) G)) (adj2 G)) in H.
  rewrite !undo_conjugation in H by exact HG. exact H.
Qed.

Definition constant_basis := elliptic_basis constant_return.
Definition constant_rotation := elliptic_rotation constant_return.
Definition rotation_defect := mul2 (mul2 (adj2 constant_basis) defect_limit) constant_basis.

Theorem constant_basis_unimodular : det2 constant_basis = 1.
Proof.
  apply elliptic_basis_unimodular;
    auto using concrete_constant_return_elliptic, concrete_constant_return_lower_left_positive.
Qed.

Theorem constant_rotation_conjugacy :
  mul2 (mul2 (adj2 constant_basis) constant_return) constant_basis = constant_rotation.
Proof.
  apply elliptic_conjugacy.
  - apply cocycle_unimodular.
  - exact concrete_constant_return_elliptic.
  - exact concrete_constant_return_lower_left_positive.
Qed.

Theorem constant_rotation_special_orthogonal :
  det2 constant_rotation = 1 /\ orthogonal2 constant_rotation.
Proof. apply elliptic_rotation_special_orthogonal, concrete_constant_return_elliptic. Qed.

Theorem rotation_defect_unimodular : det2 rotation_defect = 1.
Proof.
  unfold rotation_defect. rewrite !det2_mul, adjugate_determinant,
    constant_basis_unimodular, defect_limit_unimodular. ring.
Qed.

(* The paper's B notin SO(2), now for the constructed defect and an explicit
   constructed SL2 conjugator, with no numerical assumption. *)
Theorem rotation_defect_nonorthogonal : ~orthogonal2 rotation_defect.
Proof.
  apply conjugated_defect_nonorthogonal; [apply constant_basis_unimodular|].
  rewrite constant_rotation_conjugacy. exact (proj2 constant_rotation_special_orthogonal).
Qed.

Theorem defect_trace_amplitude : 4 < amplitude_squared rotation_defect.
Proof.
  apply nonorthogonal_amplitude; auto using rotation_defect_unimodular, rotation_defect_nonorthogonal.
Qed.

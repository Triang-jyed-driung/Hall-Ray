From Stdlib Require Import Reals Psatz ZArith Classical_Prop.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices
  LatticeBasis PaperTarget NormGeometry DaniCorrespondence.
Open Scope R_scope.

Definition zzero3 := ZVec3 0 0 0.
Definition zero3 := Vec3 0 0 0.
Definition negative_lattice_lengths nm A s :=
  exists z, z <> zzero3 /\ s = -length3 nm (action3 A (real_vector z)).

Lemma length3_nonnegative : forall nm v, 0 <= length3 nm v.
Proof.
  intros nm v; unfold length3.
  eapply Rle_trans; [apply Rabs_pos|apply Rmax_l].
Qed.
Lemma negative_lattice_lengths_nonempty : forall nm A,
  exists s, negative_lattice_lengths nm A s.
Proof.
  intros nm A. exists (-length3 nm (action3 A (real_vector (ZVec3 1 0 0)))).
  exists (ZVec3 1 0 0); split; [unfold zzero3; discriminate|reflexivity].
Qed.
Lemma negative_lattice_lengths_bounded : forall nm A,
  bound (negative_lattice_lengths nm A).
Proof.
  intros nm A. exists 0. intros s [z [Hz Hs]].
  pose proof (length3_nonnegative nm (action3 A (real_vector z))). lra.
Qed.

Definition systole nm A := -proj1_sig
  (completeness (negative_lattice_lengths nm A)
    (negative_lattice_lengths_bounded nm A)
    (negative_lattice_lengths_nonempty nm A)).

Lemma systole_lub : forall nm A,
  is_lub (negative_lattice_lengths nm A) (-systole nm A).
Proof.
  intros nm A. unfold systole. rewrite Ropp_involutive.
  apply (proj2_sig (completeness _ _ _)).
Qed.

Theorem systole_lower_bound : forall nm A z,
  z <> zzero3 -> systole nm A <= length3 nm (action3 A (real_vector z)).
Proof.
  intros nm A z Hz. destruct (systole_lub nm A) as [Hb _].
  specialize (Hb (-length3 nm (action3 A (real_vector z)))).
  assert (negative_lattice_lengths nm A (-length3 nm (action3 A (real_vector z))))
    by (exists z; auto). specialize (Hb H). lra.
Qed.

Theorem systole_greatest_lower_bound : forall nm A c,
  (forall z, z <> zzero3 -> c <= length3 nm (action3 A (real_vector z))) ->
  c <= systole nm A.
Proof.
  intros nm A c Hc. destruct (systole_lub nm A) as [_ Hleast].
  assert (Hbound : is_upper_bound (negative_lattice_lengths nm A) (-c)).
  { intros s [z [Hz Hs]]. specialize (Hc z Hz). lra. }
  specialize (Hleast (-c) Hbound). lra.
Qed.

Theorem systole_nonnegative : forall nm A, 0 <= systole nm A.
Proof.
  intros nm A. apply systole_greatest_lower_bound; intros; apply length3_nonnegative.
Qed.

Theorem systole_near : forall nm A eps,
  0 < eps -> exists z, z <> zzero3 /\
    length3 nm (action3 A (real_vector z)) < systole nm A+eps.
Proof.
  intros nm A eps He.
  destruct (classic (exists z, z <> zzero3 /\
    length3 nm (action3 A (real_vector z)) < systole nm A+eps)) as [Hyes|Hno]; auto.
  assert (Hlb : systole nm A+eps <= systole nm A).
  { apply systole_greatest_lower_bound. intros z Hz.
    destruct (Rlt_dec (length3 nm (action3 A (real_vector z))) (systole nm A+eps));
      [exfalso; apply Hno; exists z; auto|lra]. }
  lra.
Qed.

Lemma cube_continuity_epsilon : forall t eps,
  0 < eps -> exists delta, 0 < delta /\ forall u,
    Rabs (u-t) < delta -> Rabs (u^3-t^3) < eps.
Proof.
  intros t eps He.
  assert (Hc : continuity_pt (fun u : R => u^3) t) by reg.
  unfold continuity_pt, continue_in, limit1_in, limit_in in Hc; simpl in Hc.
  destruct (Hc eps He) as [d [Hd Hb]]. exists d; split; [exact Hd|].
  intros u Hu. destruct (Req_dec t u) as [Hsame|Hdiff].
  - subst u. replace (t^3-t^3) with 0 by ring. rewrite Rabs_R0; exact He.
  - apply Hb; repeat split; auto.
Qed.

Theorem systole_cube_near : forall nm A eps,
  0 < eps -> exists z, z <> zzero3 /\
    (length3 nm (action3 A (real_vector z)))^3 < (systole nm A)^3+eps.
Proof.
  intros nm A eps He.
  destruct (cube_continuity_epsilon (systole nm A) eps He) as [d [Hd Hcube]].
  destruct (systole_near nm A d Hd) as [z [Hz Hb]]. exists z; split; [exact Hz|].
  pose proof (systole_lower_bound nm A z Hz) as Hlo.
  specialize (Hcube (length3 nm (action3 A (real_vector z)))
    ltac:(rewrite Rabs_right; lra)).
  pose proof (Rle_abs ((length3 nm (action3 A (real_vector z)))^3-(systole nm A)^3)). lra.
Qed.

Theorem systole_cube_greatest_lower_bound : forall nm A c,
  (forall z, z <> zzero3 -> c <= (length3 nm (action3 A (real_vector z)))^3) ->
  c <= (systole nm A)^3.
Proof.
  intros nm A c Hb. destruct (Rle_dec c ((systole nm A)^3)) as [Hyes|Hno]; auto.
  destruct (systole_cube_near nm A (c-(systole nm A)^3) ltac:(lra)) as [z [Hz Hsmall]].
  specialize (Hb z Hz). lra.
Qed.

Theorem systole_cube_lower_bound : forall nm A z,
  z <> zzero3 -> (systole nm A)^3 <= (length3 nm (action3 A (real_vector z)))^3.
Proof.
  intros nm A z Hz. apply pow_incr; split.
  - apply systole_nonnegative.
  - apply systole_lower_bound; exact Hz.
Qed.

Definition negate3 (v : vec3) := Vec3 (-v1 v) (-v2 v) (-v3 v).
Definition znegate3 (z : zvec3) := ZVec3 (-zv1 z) (-zv2 z) (-zv3 z).

Lemma length3_negate : forall nm v, length3 nm (negate3 v) = length3 nm v.
Proof.
  intros nm [a b c]. unfold length3, negate3; simpl. rewrite Rabs_Ropp.
  replace (-b,-c) with (vscale (-1) (b,c)) by
    (unfold vscale; simpl; f_equal; ring).
  rewrite planar_norm_even; reflexivity.
Qed.
Lemma real_vector_negate : forall z, real_vector (znegate3 z) = negate3 (real_vector z).
Proof.
  intros []; apply vec3_ext; unfold real_vector, znegate3, negate3; simpl;
    rewrite opp_IZR; reflexivity.
Qed.
Lemma action3_negate : forall A v, action3 A (negate3 v) = negate3 (action3 A v).
Proof. intros [] []; apply vec3_ext; unfold action3, negate3; simpl; ring. Qed.
Lemma lattice_length_negate : forall nm A z,
  length3 nm (action3 A (real_vector (znegate3 z))) =
    length3 nm (action3 A (real_vector z)).
Proof.
  intros. rewrite real_vector_negate, action3_negate, length3_negate; reflexivity.
Qed.

Lemma approximation_index_nonzero_iff : forall q p1 p2,
  approximation_index_nonzero q p1 p2 <->
    approximation_lattice_vector (0,0) q p1 p2 <> zzero3.
Proof.
  intros q p1 p2. unfold approximation_index_nonzero,
    approximation_lattice_vector, zzero3. split.
  - intros H Heq. inversion Heq. destruct H as [Hq|[Hp1|Hp2]]; lia.
  - intros H. destruct (Nat.eq_dec q 0) as [Hq|Hq]; [|auto].
    destruct (Z.eq_dec p1 0) as [H1|H1]; [|auto].
    destruct (Z.eq_dec p2 0) as [H2|H2]; [|auto]. subst; contradiction.
Qed.

Lemma signed_lattice_vector_representation : forall nm A z,
  z <> zzero3 -> exists q p1 p2,
    approximation_index_nonzero q p1 p2 /\
    length3 nm (action3 A (real_vector z)) =
      length3 nm (action3 A (real_vector (approximation_lattice_vector (0,0) q p1 p2))).
Proof.
  intros nm A [a b c] Hnon.
  destruct (Z_le_gt_dec 0 a) as [Hpos|Hneg].
  - exists (Z.to_nat a),b,c.
    assert (Hrepr : approximation_lattice_vector (0,0) (Z.to_nat a) b c = ZVec3 a b c).
    { unfold approximation_lattice_vector. rewrite Z2Nat.id by exact Hpos. reflexivity. }
    split; [apply approximation_index_nonzero_iff; rewrite Hrepr; exact Hnon|].
    rewrite Hrepr; reflexivity.
  - exists (Z.to_nat (-a)),(-b)%Z,(-c)%Z.
    assert (Hrepr : approximation_lattice_vector (0,0) (Z.to_nat (-a)) (-b) (-c) =
      znegate3 (ZVec3 a b c)).
    { unfold approximation_lattice_vector, znegate3; simpl.
      rewrite Z2Nat.id by lia. reflexivity. }
    split.
    + unfold approximation_index_nonzero. left. intro Hzero.
      assert (Hz : (Z.of_nat (Z.to_nat (-a)) = 0)%Z) by (rewrite Hzero; reflexivity).
      rewrite Z2Nat.id in Hz by lia. lia.
    + rewrite Hrepr, lattice_length_negate. reflexivity.
Qed.

Lemma approximation_lattice_vector_independent : forall x q p1 p2,
  approximation_lattice_vector x q p1 p2 = approximation_lattice_vector (0,0) q p1 p2.
Proof. reflexivity. Qed.

Lemma action3_zero : forall A, action3 A zero3 = zero3.
Proof. intros []; apply vec3_ext; unfold action3, zero3; simpl; ring. Qed.
Lemma real_vector_zero : real_vector zzero3 = zero3.
Proof. reflexivity. Qed.
Lemma real_vector_zero_inverse : forall z, real_vector z = zero3 -> z = zzero3.
Proof.
  intros [a b c] H.
  pose proof (f_equal v1 H) as Ha; pose proof (f_equal v2 H) as Hb;
    pose proof (f_equal v3 H) as Hc.
  unfold real_vector, zero3 in Ha,Hb,Hc; simpl in Ha,Hb,Hc.
  apply eq_IZR_R0 in Ha; apply eq_IZR_R0 in Hb; apply eq_IZR_R0 in Hc.
  subst; reflexivity.
Qed.

Theorem unimodular_lattice_vector_nonzero : forall A z,
  det3 A = 1 -> z <> zzero3 -> action3 A (real_vector z) <> zero3.
Proof.
  intros A z HA Hz Hzero. apply Hz, real_vector_zero_inverse.
  apply (f_equal (action3 (adj3 A))) in Hzero.
  rewrite <- action3_product, (unimodular3_inverse_left A HA),
    action3_identity, action3_zero in Hzero. exact Hzero.
Qed.

Theorem systole_lattice_lower_bound : forall nm A v,
  lattice A v -> v <> zero3 -> systole nm A <= length3 nm v.
Proof.
  intros nm A v [z Hz] Hnon.
  assert (Hzn : z <> zzero3).
  { intro Hzero; subst z. rewrite real_vector_zero, action3_zero in Hz. contradiction. }
  rewrite Hz. apply systole_lower_bound; exact Hzn.
Qed.

Theorem systole_same_lattice : forall nm A B,
  det3 A = 1 -> det3 B = 1 -> same_lattice A B -> systole nm A = systole nm B.
Proof.
  intros nm A B HA HB Hsame. apply Rle_antisym.
  - apply systole_greatest_lower_bound. intros z Hz.
    apply systole_lattice_lower_bound.
    + apply (proj2 (Hsame _)). exists z; reflexivity.
    + apply unimodular_lattice_vector_nonzero; assumption.
  - apply systole_greatest_lower_bound. intros z Hz.
    apply systole_lattice_lower_bound.
    + apply (proj1 (Hsame _)). exists z; reflexivity.
    + apply unimodular_lattice_vector_nonzero; assumption.
Qed.

Theorem systole_marking_invariant : forall nm A Gamma,
  det3 A = 1 -> integral_matrix Gamma -> det3 Gamma = 1 ->
  systole nm (mul3 A Gamma) = systole nm A.
Proof.
  intros nm A Gamma HA Hi HG. apply systole_same_lattice.
  - rewrite mul3_determinant, HA, HG; ring.
  - exact HA.
  - apply unimodular_marking_preserves_lattice; assumption.
Qed.

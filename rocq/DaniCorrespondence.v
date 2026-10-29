From Stdlib Require Import Reals Psatz Lia ZArith Classical_Prop.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices
  LatticeBasis PaperTarget ScalarEstimates NormalizedFlow NormGeometry.
Open Scope R_scope.

Definition length3 (nm : planar_norm) (v : vec3) : R :=
  Rmax (Rabs (v1 v)) (length2 nm (v2 v, v3 v)).

Definition approximation_lattice_vector (x : vector2) (q : nat) (p1 p2 : Z) :=
  ZVec3 (Z.of_nat q) p1 p2.

Lemma planar_norm_even : forall nm v,
  length2 nm (vscale (-1) v) = length2 nm v.
Proof.
  intros nm v. rewrite length2_homogeneous.
  replace (Rabs (-1)) with 1 by (rewrite Rabs_left; lra). ring.
Qed.

Definition approximation_flow_length nm x r q p1 p2 :=
  length3 nm (action3 (mul3 (flow_scale r) (hx (fst x) (snd x)))
    (real_vector (approximation_lattice_vector x q p1 p2))).

Lemma approximation_flow_length_nonnegative : forall nm x r q p1 p2,
  0 <= approximation_flow_length nm x r q p1 p2.
Proof.
  intros. unfold approximation_flow_length, length3.
  eapply Rle_trans; [apply Rabs_pos|apply Rmax_l].
Qed.

Lemma approximation_value_nonnegative : forall nm x q p1 p2,
  0 <= approximation_value nm x q p1 p2.
Proof.
  intros. unfold approximation_value.
  apply Rmult_le_pos; [apply sqrt_pos|apply length2_nonnegative].
Qed.

Lemma integer_separation : forall u,
  (forall z : Z, u <> IZR z) ->
  exists delta, 0 < delta /\ forall z : Z, delta <= Rabs (u-IZR z).
Proof.
  intros u Hnon.
  set (n := Int_part u).
  pose proof (base_Int_part u) as Hfloor. fold n in Hfloor.
  assert (Hlo : IZR n < u) by (specialize (Hnon n); lra).
  exists (Rmin (u-IZR n) (IZR n+1-u)). split.
  - apply Rmin_pos; lra.
  - intro z. destruct (Z_le_gt_dec z n) as [Hz|Hz].
    + pose proof (IZR_le z n Hz). eapply Rle_trans; [apply Rmin_l|].
      rewrite Rabs_right; lra.
    + assert (Hnz : (n+1 <= z)%Z) by lia.
      apply IZR_le in Hnz. rewrite plus_IZR in Hnz; simpl in Hnz.
      eapply Rle_trans; [apply Rmin_r|]. rewrite Rabs_left; lra.
Qed.

Lemma irrational_fixed_denominator_gap : forall nm x q,
  ~ rational_vector x -> (0 < q)%nat ->
  exists delta, 0 < delta /\ forall p1 p2,
    delta <= length2 nm (approximation_vector x q p1 p2).
Proof.
  intros nm [x y] q Hirr Hq.
  assert (Hqr : 0 < INR q) by (apply lt_0_INR; exact Hq).
  assert (Hnon : (forall z, INR q*x <> IZR z) \/
                  (forall z, INR q*y <> IZR z)).
  { destruct (classic (exists z, INR q*x = IZR z)) as [[z Hz]|Hnone].
    - right. intros w Hw. apply Hirr. exists q,z,w; simpl.
      split; [exact Hq|]. split.
      + apply (Rmult_eq_reg_r (INR q)); [|lra]. field_simplify; nra.
      + apply (Rmult_eq_reg_r (INR q)); [|lra]. field_simplify; nra.
    - left. intros z Hz. apply Hnone. exists z; exact Hz. }
  destruct (planar_norm_equivalence nm) as [k [Hk Hbound]].
  destruct Hnon as [Hx|Hy].
  - destruct (integer_separation (INR q*x) Hx) as [d [Hd Hsep]].
    exists (k*d); split; [nra|]. intros p1 p2.
    specialize (Hbound (INR q*x-IZR p1) (INR q*y-IZR p2)).
    pose proof (Rmax_l (Rabs (INR q*x-IZR p1)) (Rabs (INR q*y-IZR p2))).
    specialize (Hsep p1). unfold approximation_vector; simpl. nra.
  - destruct (integer_separation (INR q*y) Hy) as [d [Hd Hsep]].
    exists (k*d); split; [nra|]. intros p1 p2.
    specialize (Hbound (INR q*x-IZR p1) (INR q*y-IZR p2)).
    pose proof (Rmax_r (Rabs (INR q*x-IZR p1)) (Rabs (INR q*y-IZR p2))).
    specialize (Hsep p2). unfold approximation_vector; simpl. nra.
Qed.

Theorem irrational_bounded_denominator_gap : forall nm x Q,
  ~ rational_vector x ->
  exists delta, 0 < delta /\ forall q p1 p2,
    (0 < q <= Q)%nat ->
    delta <= length2 nm (approximation_vector x q p1 p2).
Proof.
  intros nm x Q Hirr. induction Q as [|Q [d [Hd Hgap]]].
  - exists 1; split; [lra|]. intros; lia.
  - destruct (irrational_fixed_denominator_gap nm x (S Q) Hirr ltac:(lia))
      as [e [He Hnew]].
    exists (Rmin d e); split; [apply Rmin_pos; assumption|].
    intros q p1 p2 Hq. destruct (Nat.eq_dec q (S Q)) as [Hsame|Hdiff].
    + subst q. eapply Rle_trans; [apply Rmin_r|apply Hnew].
    + eapply Rle_trans; [apply Rmin_l|apply Hgap; lia].
Qed.

(* The sign in hx is immaterial because every norm is even. *)
Theorem dani_vector_identity : forall nm x q p1 p2 r,
  0 < r ->
  length3 nm (action3 (mul3 (flow_scale r) (hx (fst x) (snd x)))
    (real_vector (approximation_lattice_vector x q p1 p2))) =
  vector_length (INR q) (length2 nm (approximation_vector x q p1 p2)) r.
Proof.
  intros nm [x y] q p1 p2 r Hr.
  assert (Hvec : action3 (mul3 (flow_scale r) (hx x y))
      (real_vector (approximation_lattice_vector (x,y) q p1 p2)) =
      Vec3 (INR q/(r*r))
        ((-r)*(INR q*x-IZR p1)) ((-r)*(INR q*y-IZR p2))).
  { rewrite action3_product. apply vec3_ext;
      unfold action3, flow_scale, hx, real_vector, approximation_lattice_vector;
      simpl; rewrite <- INR_IZR_INZ; unfold Rdiv; ring. }
  simpl fst; simpl snd. rewrite Hvec. unfold length3; simpl.
  change (Rmax (Rabs (INR q/(r*r)))
    (length2 nm (vscale (-r) (approximation_vector (x,y) q p1 p2))) =
    vector_length (INR q) (length2 nm (approximation_vector (x,y) q p1 p2)) r).
  rewrite length2_homogeneous, Rabs_Ropp, (Rabs_right r) by lra.
  rewrite Rabs_right; [reflexivity|].
  apply Rle_ge. unfold Rdiv. apply Rmult_le_pos; [apply pos_INR|].
  apply Rlt_le, Rinv_0_lt_compat; nra.
Qed.

Theorem dani_balanced_vector : forall nm x q p1 p2,
  (0 < q)%nat -> 0 < length2 nm (approximation_vector x q p1 p2) ->
  exists r0, 0 < r0 /\
    (forall r, 0 < r ->
      length3 nm (action3 (mul3 (flow_scale r0) (hx (fst x) (snd x)))
        (real_vector (approximation_lattice_vector x q p1 p2))) <=
      length3 nm (action3 (mul3 (flow_scale r) (hx (fst x) (snd x)))
        (real_vector (approximation_lattice_vector x q p1 p2)))) /\
    (length3 nm (action3 (mul3 (flow_scale r0) (hx (fst x) (snd x)))
        (real_vector (approximation_lattice_vector x q p1 p2))))^3 =
      (approximation_value nm x q p1 p2)^2.
Proof.
  intros nm x q p1 p2 Hq Hd.
  set (d := length2 nm (approximation_vector x q p1 p2)) in *.
  assert (Hqr : 0 < INR q) by (apply lt_0_INR; exact Hq).
  set (r0 := positive_cube_root (INR q/d)).
  assert (Hr0 : 0 < r0) by apply positive_cube_root_positive.
  assert (Hcube : r0^3*d = INR q).
  { unfold r0. rewrite positive_cube_root_cube by (apply Rdiv_lt_0_compat; assumption).
    field; lra. }
  destruct (balanced_vector_minimum (INR q) d r0 Hqr Hd Hr0 Hcube)
    as [Heq [Hmin Hval]].
  exists r0; split; [exact Hr0|]. split.
  - intros r Hr. rewrite !dani_vector_identity by assumption. fold d.
    rewrite Heq; apply Hmin; exact Hr.
  - rewrite dani_vector_identity by assumption. fold d. rewrite Heq, Hval.
    unfold approximation_value. fold d.
    pose proof (pow2_sqrt (INR q) ltac:(lra)). nra.
Qed.

Lemma integer_nonzero_absolute : forall z : Z,
  z <> 0%Z -> 1 <= Rabs (IZR z).
Proof.
  intros z Hz. destruct (Z_le_gt_dec 1 z) as [Hpos|Hneg].
  - apply IZR_le in Hpos. simpl in Hpos.
    rewrite Rabs_right; lra.
  - assert (Hle : (z <= -1)%Z) by lia.
    apply IZR_le in Hle. simpl in Hle. rewrite Rabs_left; lra.
Qed.

Lemma integer_planar_norm_gap : forall nm,
  exists k, 0 < k /\ forall p1 p2,
    p1 <> 0%Z \/ p2 <> 0%Z -> k <= length2 nm (IZR p1, IZR p2).
Proof.
  intro nm. destruct (planar_norm_equivalence nm) as [k [Hk Hb]].
  exists k; split; [exact Hk|]. intros p1 p2 Hnon.
  specialize (Hb (IZR p1) (IZR p2)). destruct Hnon as [H1|H2].
  - pose proof (integer_nonzero_absolute p1 H1).
    pose proof (Rmax_l (Rabs (IZR p1)) (Rabs (IZR p2))). nra.
  - pose proof (integer_nonzero_absolute p2 H2).
    pose proof (Rmax_r (Rabs (IZR p1)) (Rabs (IZR p2))). nra.
Qed.

Definition approximation_index_nonzero (q : nat) (p1 p2 : Z) :=
  q <> 0%nat \/ p1 <> 0%Z \/ p2 <> 0%Z.

Theorem bounded_denominator_escape : forall nm x Q M,
  ~ rational_vector x ->
  exists R0, 0 < R0 /\ forall r q p1 p2,
    R0 <= r -> (q <= Q)%nat -> approximation_index_nonzero q p1 p2 ->
    M < length3 nm (action3 (mul3 (flow_scale r) (hx (fst x) (snd x)))
      (real_vector (approximation_lattice_vector x q p1 p2))).
Proof.
  intros nm x Q M Hirr.
  destruct (irrational_bounded_denominator_gap nm x Q Hirr) as [d [Hd Hgap]].
  destruct (integer_planar_norm_gap nm) as [k [Hk Hints]].
  set (e := Rmin d k).
  assert (He : 0 < e) by (apply Rmin_pos; assumption).
  assert (Hed : e <= d) by apply Rmin_l.
  assert (Hek : e <= k) by apply Rmin_r.
  exists ((Rabs M+1)/e). split.
  - apply Rdiv_lt_0_compat; [pose proof (Rabs_pos M); lra|exact He].
  - intros r q p1 p2 Hr Hq Hnon.
    assert (Hrpos : 0 < r).
    { assert (0 < (Rabs M+1)/e) by
        (apply Rdiv_lt_0_compat; [pose proof (Rabs_pos M); lra|exact He]). lra. }
    assert (Herror : e <= length2 nm (approximation_vector x q p1 p2)).
    { destruct q as [|q].
      - unfold approximation_index_nonzero in Hnon.
        assert (Hp : p1 <> 0%Z \/ p2 <> 0%Z) by tauto.
        pose proof (Hints p1 p2 Hp) as H.
        replace (approximation_vector x 0 p1 p2) with
          (vscale (-1) (IZR p1,IZR p2)) by
          (unfold approximation_vector, vscale; simpl; f_equal; ring).
        rewrite planar_norm_even. lra.
      - specialize (Hgap (S q) p1 p2 ltac:(lia)). lra. }
    rewrite dani_vector_identity by exact Hrpos.
    apply Rlt_le_trans with (r*length2 nm (approximation_vector x q p1 p2));
      [|apply Rmax_r].
    assert (Hmul : Rabs M+1 <= r*e).
    { apply (Rmult_le_compat_r e) in Hr; [|lra].
      replace ((Rabs M+1)/e*e) with (Rabs M+1) in Hr by (field; lra).
      exact Hr. }
    pose proof (Rle_abs M). nra.
Qed.

Definition balancing_scale nm x q p1 p2 :=
  positive_cube_root (INR q/length2 nm (approximation_vector x q p1 p2)).

Lemma irrational_error_positive : forall nm x q p1 p2,
  ~ rational_vector x -> (0 < q)%nat ->
  0 < length2 nm (approximation_vector x q p1 p2).
Proof.
  intros nm x q p1 p2 Hi Hq.
  destruct (irrational_fixed_denominator_gap nm x q Hi Hq) as [d [Hd Hb]].
  specialize (Hb p1 p2). lra.
Qed.

Theorem dani_balancing_scale : forall nm x q p1 p2,
  ~ rational_vector x -> (0 < q)%nat ->
  let r0 := balancing_scale nm x q p1 p2 in
  0 < r0 /\
  r0^3*length2 nm (approximation_vector x q p1 p2) = INR q /\
  (approximation_flow_length nm x r0 q p1 p2)^3 =
    (approximation_value nm x q p1 p2)^2 /\
  forall r, 0 < r ->
    approximation_flow_length nm x r0 q p1 p2 <=
    approximation_flow_length nm x r q p1 p2.
Proof.
  intros nm x q p1 p2 Hi Hq r0.
  pose proof (irrational_error_positive nm x q p1 p2 Hi Hq) as Hd.
  assert (Hqr : 0 < INR q) by (apply lt_0_INR; exact Hq).
  assert (Hr0 : 0 < r0) by apply positive_cube_root_positive.
  assert (Hcube : r0^3*length2 nm (approximation_vector x q p1 p2) = INR q).
  { unfold r0, balancing_scale. rewrite positive_cube_root_cube by
      (apply Rdiv_lt_0_compat; assumption). field; lra. }
  destruct (balanced_vector_minimum _ _ _ Hqr Hd Hr0 Hcube) as [Heq [Hmin Hval]].
  split; [exact Hr0|]. split; [exact Hcube|]. split.
  - unfold approximation_flow_length. rewrite dani_vector_identity by exact Hr0.
    rewrite Heq, Hval. unfold approximation_value.
    pose proof (pow2_sqrt (INR q) ltac:(lra)). nra.
  - intros r Hr. unfold approximation_flow_length.
    rewrite !dani_vector_identity by assumption. rewrite Heq. apply Hmin; exact Hr.
Qed.

Theorem dani_vector_lower_bound : forall nm x q p1 p2 r,
  ~ rational_vector x -> (0 < q)%nat -> 0 < r ->
  (approximation_value nm x q p1 p2)^2 <=
    (approximation_flow_length nm x r q p1 p2)^3.
Proof.
  intros nm x q p1 p2 r Hi Hq Hr.
  destruct (dani_balancing_scale nm x q p1 p2 Hi Hq) as [Hr0 [Hb [Hv Hmin]]].
  rewrite <- Hv. apply pow_incr. split.
  - apply approximation_flow_length_nonnegative.
  - apply Hmin; exact Hr.
Qed.

Lemma natural_cast_cofinal : forall T, exists N, T < INR N.
Proof.
  intro T. destruct (Rlt_dec T 0) as [Ht|Ht].
  - exists 0%nat; simpl; exact Ht.
  - pose proof (archimed T) as Hu.
    assert (Huz : (0 < up T)%Z) by (apply lt_IZR; simpl; lra).
    exists (Z.to_nat (up T)). rewrite INR_IZR_INZ, Z2Nat.id by lia. lra.
Qed.

(* Uniformly over all numerators, bounded approximation values at large
   denominators have their minimizing scale arbitrarily far forward. *)
Theorem balancing_scales_escape : forall nm x C R0,
  ~ rational_vector x -> 0 < C -> 0 < R0 ->
  exists Q, forall q p1 p2,
    (Q <= q)%nat -> (0 < q)%nat ->
    approximation_value nm x q p1 p2 <= C ->
    R0 < balancing_scale nm x q p1 p2.
Proof.
  intros nm x C R0 Hi HC HR.
  destruct (natural_cast_cofinal (R0^3*C)) as [Q HQ].
  exists Q. intros q p1 p2 Hq Hpos Ha.
  pose proof (le_INR Q q Hq) as Hlarge.
  assert (Hone : 1 <= INR q).
  { change (INR 1 <= INR q). apply le_INR; lia. }
  assert (Hsqrt : 1 <= sqrt (INR q)).
  { pose proof (sqrt_pos (INR q)). pose proof (pow2_sqrt (INR q) ltac:(lra)); nra. }
  pose proof (irrational_error_positive nm x q p1 p2 Hi Hpos) as Hd.
  assert (HdC : length2 nm (approximation_vector x q p1 p2) <= C).
  { unfold approximation_value in Ha. nra. }
  destruct (dani_balancing_scale nm x q p1 p2 Hi Hpos) as [Hr [Hcube _]].
  destruct (Rlt_dec R0 (balancing_scale nm x q p1 p2)) as [Hyes|Hno]; auto.
  pose proof (pow_incr (balancing_scale nm x q p1 p2) R0 3 ltac:(lra)) as Hp.
  pose proof (pow_le R0 3 ltac:(lra)). nra.
Qed.

(* An epsilon definition of the liminf of the cubed systole. Quantifying
   over vectors avoids assuming that a shortest vector has been selected.
   Both signs of the denominator represent the same lengths. *)
Definition has_dani_constant nm x rho : Prop :=
  (forall eps, 0 < eps < rho -> exists R0, 0 < R0 /\
    forall r q p1 p2, R0 <= r -> approximation_index_nonzero q p1 p2 ->
      (rho-eps)^2 <= (approximation_flow_length nm x r q p1 p2)^3) /\
  (forall eps, 0 < eps -> forall R0, exists r q p1 p2,
    0 < r /\ R0 <= r /\ approximation_index_nonzero q p1 p2 /\
    (approximation_flow_length nm x r q p1 p2)^3 <= (rho+eps)^2).

Theorem approximation_implies_dani : forall nm x rho,
  ~ rational_vector x -> 0 < rho ->
  has_approximation_constant nm x rho -> has_dani_constant nm x rho.
Proof.
  intros nm x rho Hi Hrho [Hlower Hupper]. split.
  - intros eps He. destruct (Hlower eps ltac:(lra)) as [Q HQ].
    destruct (bounded_denominator_escape nm x Q (rho+1) Hi) as [R0 [HR Hescape]].
    exists R0; split; [exact HR|]. intros r q p1 p2 Hr Hnon.
    destruct (le_lt_dec q Q) as [Hsmall|Hbig].
    + pose proof (Hescape r q p1 p2 Hr Hsmall Hnon) as Hlen.
      change (rho+1 < approximation_flow_length nm x r q p1 p2) in Hlen.
      pose proof (pow_incr (rho-eps) (approximation_flow_length nm x r q p1 p2)
        3 ltac:(lra)) as Hcube.
      (* A length above rho+1 also exceeds the required cubed threshold. *)
      pose proof (pow_incr (rho+1) (approximation_flow_length nm x r q p1 p2)
        3 ltac:(lra)) as Hbigcube.
      assert (Hthreshold : (rho-eps)^2 <= (rho+1)^3).
      { assert (0 <= (rho-eps)^2) by (apply pow_le; lra).
        assert ((rho-eps)^2 <= rho^2) by (apply pow_incr; lra).
        assert (0 <= rho^3) by (apply pow_le; lra). nra. }
      lra.
    + assert (Hpos : (0 < q)%nat) by lia.
      pose proof (HQ q ltac:(lia) Hpos p1 p2) as Ha.
      pose proof (dani_vector_lower_bound nm x q p1 p2 r Hi Hpos ltac:(lra)) as Hb.
      pose proof (pow_incr (rho-eps) (approximation_value nm x q p1 p2) 2 ltac:(lra)).
      lra.
  - intros eps He R0.
    destruct (balancing_scales_escape nm x (rho+eps) (Rabs R0+1) Hi ltac:(lra)
      ltac:(pose proof (Rabs_pos R0); lra)) as [Q HQ].
    destruct (Hupper eps He Q) as [q [p1 [p2 [Hq [Hpos Ha]]]]].
    destruct (dani_balancing_scale nm x q p1 p2 Hi Hpos) as [Hr [Hb [Hv Hmin]]].
    exists (balancing_scale nm x q p1 p2), q, p1, p2.
    split; [exact Hr|]. split.
    + pose proof (HQ q p1 p2 Hq Hpos Ha). pose proof (Rle_abs R0); lra.
    + split; [unfold approximation_index_nonzero; left; lia|].
      rewrite Hv. apply pow_incr. split; [apply approximation_value_nonnegative|exact Ha].
Qed.

Lemma cubic_bound_length_bound : forall L C,
  0 <= L -> 0 < C -> L^3 <= C^2 -> L < C+1.
Proof.
  intros L C HL HC Hb. destruct (Rlt_dec L (C+1)); auto.
  pose proof (pow_incr (C+1) L 3 ltac:(lra)).
  pose proof (pow_le C 3 ltac:(lra)). nra.
Qed.

Theorem dani_implies_approximation : forall nm x rho,
  ~ rational_vector x -> 0 < rho ->
  has_dani_constant nm x rho -> has_approximation_constant nm x rho.
Proof.
  intros nm x rho Hi Hrho [Hlower Hupper]. split.
  - intros eps He. destruct (Rlt_dec eps rho) as [Hsmall|Hlarge].
    + destruct (Hlower eps ltac:(lra)) as [R0 [HR Hb]].
      destruct (balancing_scales_escape nm x (rho+1) R0 Hi ltac:(lra) HR) as [Q HQ].
      exists Q. intros q Hq Hpos p1 p2.
      destruct (Rle_dec (rho-eps) (approximation_value nm x q p1 p2)) as [Hyes|Hno]; auto.
      pose proof (HQ q p1 p2 Hq Hpos ltac:(lra)) as Hlate.
      destruct (dani_balancing_scale nm x q p1 p2 Hi Hpos) as [Hr [Hbal [Hv Hmin]]].
      specialize (Hb (balancing_scale nm x q p1 p2) q p1 p2 ltac:(lra)
        ltac:(unfold approximation_index_nonzero; left; lia)).
      rewrite Hv in Hb. pose proof (approximation_value_nonnegative nm x q p1 p2). nra.
    + exists 0%nat. intros q Hq Hpos p1 p2.
      pose proof (approximation_value_nonnegative nm x q p1 p2). lra.
  - intros eps He Q.
    destruct (bounded_denominator_escape nm x Q (rho+eps+1) Hi) as [R0 [HR Hescape]].
    destruct (Hupper eps He R0) as [r [q [p1 [p2 [Hr [Hlate [Hnon Hlen]]]]]]].
    assert (Hsmall : approximation_flow_length nm x r q p1 p2 < rho+eps+1).
    { apply cubic_bound_length_bound; [apply approximation_flow_length_nonnegative|lra|exact Hlen]. }
    assert (Hbigq : (Q < q)%nat).
    { destruct (le_lt_dec q Q) as [Hle|Hlt]; auto.
      pose proof (Hescape r q p1 p2 Hlate Hle Hnon) as Hesc.
      change (rho+eps+1 < approximation_flow_length nm x r q p1 p2) in Hesc. lra. }
    exists q,p1,p2. split; [lia|]. split; [lia|].
    pose proof (dani_vector_lower_bound nm x q p1 p2 r Hi ltac:(lia) Hr) as Hbound.
    pose proof (approximation_value_nonnegative nm x q p1 p2). nra.
Qed.

Theorem dani_correspondence_vector_form : forall nm x rho,
  ~ rational_vector x -> 0 < rho ->
  (has_approximation_constant nm x rho <-> has_dani_constant nm x rho).
Proof.
  intros nm x rho Hi Hr. split.
  - apply approximation_implies_dani; assumption.
  - apply dani_implies_approximation; assumption.
Qed.

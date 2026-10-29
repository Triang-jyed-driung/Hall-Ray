From Stdlib Require Import Reals Psatz ZArith Classical_Prop.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices
  LatticeBasis PaperTarget NormGeometry DaniCorrespondence LatticeSystole.
Open Scope R_scope.

Definition size3 (v : vec3) := Rabs (v1 v)+Rabs (v2 v)+Rabs (v3 v).
Definition difference3 (u v : vec3) := Vec3 (v1 u-v1 v) (v2 u-v2 v) (v3 u-v3 v).

Lemma size3_nonnegative : forall v, 0 <= size3 v.
Proof.
  intros [a b c]; unfold size3; simpl.
  pose proof (Rabs_pos a); pose proof (Rabs_pos b); pose proof (Rabs_pos c); lra.
Qed.

Theorem length3_controls_coordinates : forall nm,
  exists C, 0 < C /\ forall v, size3 v <= C*length3 nm v.
Proof.
  intro nm. destruct (planar_norm_equivalence nm) as [k [Hk Hbound]].
  exists (1+2/k); split.
  - assert (0 < /k) by (apply Rinv_0_lt_compat; exact Hk). unfold Rdiv; nra.
  - intros [a b c]. unfold size3, length3; simpl.
    specialize (Hbound b c).
    pose proof (Rmax_l (Rabs a) (length2 nm (b,c))) as Ha.
    pose proof (Rmax_r (Rabs a) (length2 nm (b,c))) as Hn.
    pose proof (Rmax_l (Rabs b) (Rabs c)) as Hb.
    pose proof (Rmax_r (Rabs b) (Rabs c)) as Hc.
    apply (Rmult_le_reg_r k); [exact Hk|].
    replace ((1+2/k)*Rmax (Rabs a) (length2 nm (b,c))*k) with
      ((k+2)*Rmax (Rabs a) (length2 nm (b,c))) by (field; lra). nra.
Qed.

Lemma max_difference_bound : forall a b c d,
  Rabs (Rmax a b-Rmax c d) <= Rabs (a-c)+Rabs (b-d).
Proof.
  intros a b c d. pose proof (Rabs_pos (a-c)). pose proof (Rabs_pos (b-d)).
  pose proof (Rle_abs (a-c)); pose proof (Rle_abs (c-a)).
  pose proof (Rle_abs (b-d)); pose proof (Rle_abs (d-b)).
  rewrite (Rabs_minus_sym c a), (Rabs_minus_sym d b) in *.
  destruct (Rle_dec b a), (Rle_dec d c);
    repeat first [rewrite Rmax_left by lra|rewrite Rmax_right by lra];
    apply Rabs_le; split; lra.
Qed.

Theorem length3_lipschitz : forall nm u v,
  Rabs (length3 nm u-length3 nm v) <=
    (norm_bound nm+1)*size3 (difference3 u v).
Proof.
  intros nm [a b c] [x y z].
  unfold length3, size3, difference3; simpl.
  pose proof (max_difference_bound (Rabs a) (length2 nm (b,c))
    (Rabs x) (length2 nm (y,z))) as H.
  pose proof (Rabs_triang_inv2 a x) as H1.
  pose proof (planar_norm_lipschitz nm b c y z) as H2.
  pose proof (norm_bound_positive nm).
  pose proof (Rabs_pos (a-x)); pose proof (Rabs_pos (b-y)); pose proof (Rabs_pos (c-z)). nra.
Qed.

Definition entries_bounded3 (A : mat3) (M : R) :=
  Rabs (b11 A) <= M /\ Rabs (b12 A) <= M /\ Rabs (b13 A) <= M /\
  Rabs (b21 A) <= M /\ Rabs (b22 A) <= M /\ Rabs (b23 A) <= M /\
  Rabs (b31 A) <= M /\ Rabs (b32 A) <= M /\ Rabs (b33 A) <= M.

Definition entry_sum3 (A : mat3) :=
  Rabs (b11 A)+Rabs (b12 A)+Rabs (b13 A)+
  Rabs (b21 A)+Rabs (b22 A)+Rabs (b23 A)+
  Rabs (b31 A)+Rabs (b32 A)+Rabs (b33 A)+1.

Lemma entry_sum3_bounds : forall A,
  0 < entry_sum3 A /\ entries_bounded3 A (entry_sum3 A).
Proof.
  intros [a b c d e f g h i]. unfold entry_sum3, entries_bounded3; simpl.
  pose proof (Rabs_pos a); pose proof (Rabs_pos b); pose proof (Rabs_pos c);
    pose proof (Rabs_pos d); pose proof (Rabs_pos e); pose proof (Rabs_pos f);
    pose proof (Rabs_pos g); pose proof (Rabs_pos h); pose proof (Rabs_pos i).
  repeat split; lra.
Qed.

Lemma three_term_action_bound : forall a b c x y z M,
  0 <= M -> Rabs a <= M -> Rabs b <= M -> Rabs c <= M ->
  Rabs (a*x+b*y+c*z) <= M*(Rabs x+Rabs y+Rabs z).
Proof.
  intros a b c x y z M HM Ha Hb Hc.
  pose proof (Rabs_triang (a*x+b*y) (c*z)).
  pose proof (Rabs_triang (a*x) (b*y)). rewrite !Rabs_mult in *.
  pose proof (Rabs_pos x); pose proof (Rabs_pos y); pose proof (Rabs_pos z). nra.
Qed.

Theorem action3_size_bound : forall A M v,
  0 <= M -> entries_bounded3 A M -> size3 (action3 A v) <= 3*M*size3 v.
Proof.
  intros A M [x y z] HM (H11&H12&H13&H21&H22&H23&H31&H32&H33).
  unfold size3, action3; simpl.
  pose proof (three_term_action_bound _ _ _ x y z M HM H11 H12 H13).
  pose proof (three_term_action_bound _ _ _ x y z M HM H21 H22 H23).
  pose proof (three_term_action_bound _ _ _ x y z M HM H31 H32 H33). lra.
Qed.

Theorem unimodular_inverse_coordinate_bound : forall nm A,
  det3 A = 1 -> exists C, 0 < C /\ forall v,
    size3 v <= C*length3 nm (action3 A v).
Proof.
  intros nm A HA.
  destruct (length3_controls_coordinates nm) as [C [HC Hbound]].
  destruct (entry_sum3_bounds (adj3 A)) as [HM Hentries].
  exists (3*entry_sum3 (adj3 A)*C). split; [nra|]. intros v.
  pose proof (action3_size_bound (adj3 A) (entry_sum3 (adj3 A)) (action3 A v)
    ltac:(lra) Hentries) as H.
  rewrite <- action3_product, (unimodular3_inverse_left A HA), action3_identity in H.
  specialize (Hbound (action3 A v)). nra.
Qed.

Lemma integer_vector_size_lower : forall z,
  z <> zzero3 -> 1 <= size3 (real_vector z).
Proof.
  intros [a b c] Hnon. unfold size3, real_vector; simpl.
  pose proof (Rabs_pos (IZR a)); pose proof (Rabs_pos (IZR b)); pose proof (Rabs_pos (IZR c)).
  destruct (Z.eq_dec a 0) as [Ha|Ha].
  - destruct (Z.eq_dec b 0) as [Hb|Hb].
    + assert (Hc : c <> 0%Z) by (intro Hc; subst; apply Hnon; reflexivity).
      pose proof (integer_nonzero_absolute c Hc); lra.
    + pose proof (integer_nonzero_absolute b Hb); lra.
  - pose proof (integer_nonzero_absolute a Ha); lra.
Qed.

Theorem systole_positive : forall nm A, det3 A = 1 -> 0 < systole nm A.
Proof.
  intros nm A HA.
  destruct (unimodular_inverse_coordinate_bound nm A HA) as [C [HC Hb]].
  assert (Hlower : /C <= systole nm A).
  { apply systole_greatest_lower_bound. intros z Hz.
    specialize (Hb (real_vector z)). pose proof (integer_vector_size_lower z Hz).
    apply (Rmult_le_reg_l C); [exact HC|].
    replace (C* /C) with 1 by (field; lra). nra. }
  pose proof (Rinv_0_lt_compat C HC). lra.
Qed.

Definition matrix_difference3 (B A : mat3) := Mat3
  (b11 B-b11 A) (b12 B-b12 A) (b13 B-b13 A)
  (b21 B-b21 A) (b22 B-b22 A) (b23 B-b23 A)
  (b31 B-b31 A) (b32 B-b32 A) (b33 B-b33 A).
Definition matrices_close3 (d : R) (A B : mat3) :=
  entries_bounded3 (matrix_difference3 B A) d.

Lemma action3_difference : forall B A v,
  difference3 (action3 B v) (action3 A v) = action3 (matrix_difference3 B A) v.
Proof.
  intros [] [] []; apply vec3_ext; unfold difference3, action3, matrix_difference3;
    simpl; ring.
Qed.

Theorem lattice_vector_relative_continuity : forall nm A,
  det3 A = 1 -> exists K, 0 < K /\ forall d B v,
    0 <= d -> matrices_close3 d A B ->
    Rabs (length3 nm (action3 B v)-length3 nm (action3 A v)) <=
      K*d*length3 nm (action3 A v).
Proof.
  intros nm A HA.
  destruct (unimodular_inverse_coordinate_bound nm A HA) as [C [HC Hb]].
  exists (3*(norm_bound nm+1)*C). split.
  - pose proof (norm_bound_positive nm); nra.
  - intros d B v Hd Hclose.
    pose proof (norm_bound_positive nm) as HN.
    eapply Rle_trans; [apply length3_lipschitz|]. rewrite action3_difference.
    eapply Rle_trans.
    + apply Rmult_le_compat_l; [lra|]. apply action3_size_bound; [exact Hd|exact Hclose].
    + replace ((norm_bound nm+1)*(3*d*size3 v)) with
        ((3*(norm_bound nm+1)*d)*size3 v) by ring.
      replace (3*(norm_bound nm+1)*C*d*length3 nm (action3 A v)) with
        ((3*(norm_bound nm+1)*d)*(C*length3 nm (action3 A v))) by ring.
      apply Rmult_le_compat_l; [nra|apply Hb].
Qed.

Lemma absolute_difference_sandwich : forall a b h,
  Rabs (b-a) <= h -> a-h <= b <= a+h.
Proof.
  intros a b h Hb. destruct (Rcase_abs (b-a));
    [rewrite Rabs_left in Hb by lra|rewrite Rabs_right in Hb by lra]; lra.
Qed.

Theorem systole_comparison_upper : forall nm A B c,
  0 < c ->
  (forall z, z <> zzero3 ->
    length3 nm (action3 B (real_vector z)) <= c*length3 nm (action3 A (real_vector z))) ->
  systole nm B <= c*systole nm A.
Proof.
  intros nm A B c HC Hb.
  assert (Hlb : systole nm B/c <= systole nm A).
  { apply systole_greatest_lower_bound. intros z Hz.
    pose proof (systole_lower_bound nm B z Hz) as Hs.
    specialize (Hb z Hz). apply (Rmult_le_reg_l c); [exact HC|].
    replace (c*(systole nm B/c)) with (systole nm B) by (field; lra). lra. }
  apply (Rmult_le_compat_l c) in Hlb; [|lra].
  replace (c*(systole nm B/c)) with (systole nm B) in Hlb by (field; lra). exact Hlb.
Qed.

Theorem systole_relative_comparison : forall nm A B h,
  0 <= h <= 1 ->
  (forall v, Rabs (length3 nm (action3 B v)-length3 nm (action3 A v)) <=
    h*length3 nm (action3 A v)) ->
  Rabs (systole nm B-systole nm A) <= h*systole nm A.
Proof.
  intros nm A B h Hh Hb.
  assert (Hupper : systole nm B <= (1+h)*systole nm A).
  { apply systole_comparison_upper; [lra|]. intros z Hz.
    specialize (Hb (real_vector z)). apply absolute_difference_sandwich in Hb. nra. }
  assert (Hlower : (1-h)*systole nm A <= systole nm B).
  { apply systole_greatest_lower_bound. intros z Hz.
    pose proof (systole_lower_bound nm A z Hz) as Hs.
    specialize (Hb (real_vector z)). apply absolute_difference_sandwich in Hb.
    assert (Hscaled : (1-h)*systole nm A <=
      (1-h)*length3 nm (action3 A (real_vector z))) by
      (apply Rmult_le_compat_l; lra). nra. }
  apply Rabs_le; split; nra.
Qed.

Theorem systole_relative_continuity : forall nm A,
  det3 A = 1 -> exists K, 0 < K /\ forall d B,
    0 <= d -> K*d <= 1 -> matrices_close3 d A B ->
    Rabs (systole nm B-systole nm A) <= K*d*systole nm A.
Proof.
  intros nm A HA.
  destruct (lattice_vector_relative_continuity nm A HA) as [K [HK Hb]].
  exists K; split; [exact HK|]. intros d B Hd Hsmall Hclose.
  apply systole_relative_comparison; [split; nra|].
  intros v. apply (Hb d B v Hd Hclose).
Qed.

Theorem systole_continuous : forall nm A,
  det3 A = 1 -> forall eps, 0 < eps ->
  exists delta, 0 < delta /\ forall B,
    matrices_close3 delta A B -> Rabs (systole nm B-systole nm A) < eps.
Proof.
  intros nm A HA eps He.
  destruct (systole_relative_continuity nm A HA) as [K [HK Hb]].
  pose proof (systole_nonnegative nm A) as Hs.
  set (delta := Rmin (1/(2*K)) (eps/(2*K*(systole nm A+1)))).
  assert (Hd : 0 < delta).
  { apply Rmin_pos; apply Rdiv_lt_0_compat; nra. }
  assert (Hsmall : K*delta <= 1/2).
  { pose proof (Rmin_l (1/(2*K)) (eps/(2*K*(systole nm A+1)))) as H.
    change (delta <= 1/(2*K)) in H.
    apply (Rmult_le_compat_r (2*K)) in H; [|nra].
    replace (1/(2*K)*(2*K)) with 1 in H by (field; lra). nra. }
  assert (Herr : K*delta*systole nm A < eps).
  { pose proof (Rmin_r (1/(2*K)) (eps/(2*K*(systole nm A+1)))) as H.
    change (delta <= eps/(2*K*(systole nm A+1))) in H.
    apply (Rmult_le_compat_r (2*K*(systole nm A+1))) in H; [|nra].
    replace (eps/(2*K*(systole nm A+1))*(2*K*(systole nm A+1))) with eps in H
      by (field; nra). nra. }
  exists delta; split; [exact Hd|]. intros B Hclose.
  eapply Rle_lt_trans; [exact (Hb delta B ltac:(lra) ltac:(lra) Hclose)|exact Herr].
Qed.

Theorem systole_uniform_relative_continuity : forall nm M,
  0 < M -> exists K, 0 < K /\ forall A B d,
    det3 A = 1 -> entries_bounded3 (adj3 A) M ->
    0 <= d -> K*d <= 1 -> matrices_close3 d A B ->
    Rabs (systole nm B-systole nm A) <= K*d*systole nm A.
Proof.
  intros nm M HM.
  destruct (length3_controls_coordinates nm) as [C [HC Hcoordinates]].
  set (K := 9*(norm_bound nm+1)*M*C).
  pose proof (norm_bound_positive nm) as HN.
  assert (HK : 0 < K) by (unfold K; repeat apply Rmult_lt_0_compat; lra).
  exists K; split; [exact HK|].
  intros A B d HA Hentries Hd Hsmall Hclose.
  apply systole_relative_comparison; [split; [nra|exact Hsmall]|].
  intros v.
  assert (Hinv : size3 v <= (3*M*C)*length3 nm (action3 A v)).
  { pose proof (action3_size_bound (adj3 A) M (action3 A v) ltac:(lra) Hentries) as H.
    rewrite <- action3_product, (unimodular3_inverse_left A HA), action3_identity in H.
    pose proof (Hcoordinates (action3 A v)). nra. }
  eapply Rle_trans; [apply length3_lipschitz|]. rewrite action3_difference.
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [lra|].
    exact (action3_size_bound (matrix_difference3 B A) d v Hd Hclose).
  - replace ((norm_bound nm+1)*(3*d*size3 v)) with
      ((3*(norm_bound nm+1)*d)*size3 v) by ring.
    unfold K. replace (9*(norm_bound nm+1)*M*C*d*length3 nm (action3 A v)) with
      ((3*(norm_bound nm+1)*d)*((3*M*C)*length3 nm (action3 A v))) by ring.
    apply Rmult_le_compat_l; [nra|exact Hinv].
Qed.

Theorem systole_uniform_continuity : forall nm M U eps,
  0 < M -> 0 <= U -> 0 < eps ->
  exists delta, 0 < delta /\ forall A B,
    det3 A = 1 -> entries_bounded3 (adj3 A) M -> systole nm A <= U ->
    matrices_close3 delta A B -> Rabs (systole nm B-systole nm A) < eps.
Proof.
  intros nm M U eps HM HU He.
  destruct (systole_uniform_relative_continuity nm M HM) as [K [HK Hb]].
  set (delta := Rmin (1/(2*K)) (eps/(2*K*(U+1)))).
  assert (Hd : 0 < delta) by (apply Rmin_pos; apply Rdiv_lt_0_compat; nra).
  assert (Hsmall : K*delta <= 1/2).
  { pose proof (Rmin_l (1/(2*K)) (eps/(2*K*(U+1)))) as H.
    change (delta <= 1/(2*K)) in H.
    apply (Rmult_le_compat_r (2*K)) in H; [|nra].
    replace (1/(2*K)*(2*K)) with 1 in H by (field; lra). nra. }
  assert (Herr : K*delta*U < eps).
  { pose proof (Rmin_r (1/(2*K)) (eps/(2*K*(U+1)))) as H.
    change (delta <= eps/(2*K*(U+1))) in H.
    apply (Rmult_le_compat_r (2*K*(U+1))) in H; [|nra].
    replace (eps/(2*K*(U+1))*(2*K*(U+1))) with eps in H by (field; nra). nra. }
  exists delta; split; [exact Hd|]. intros A B HA Hentries Hupper Hclose.
  eapply Rle_lt_trans; [exact (Hb A B delta HA Hentries ltac:(lra) ltac:(lra) Hclose)|].
  eapply Rle_lt_trans; [|exact Herr]. apply Rmult_le_compat_l; nra.
Qed.

Theorem systole_left_relative_continuity : forall nm,
  exists K, 0 < K /\ forall A L d,
    0 <= d -> K*d <= 1 -> matrices_close3 d id3 L ->
    Rabs (systole nm (mul3 L A)-systole nm A) <= K*d*systole nm A.
Proof.
  intro nm. destruct (length3_controls_coordinates nm) as [C [HC Hcoordinates]].
  set (K := 3*(norm_bound nm+1)*C).
  pose proof (norm_bound_positive nm) as HN.
  assert (HK : 0 < K) by (unfold K; nra).
  exists K; split; [exact HK|]. intros A L d Hd Hsmall Hclose.
  apply systole_relative_comparison; [split; [nra|exact Hsmall]|].
  intros v. rewrite action3_product.
  pose proof (length3_lipschitz nm (action3 L (action3 A v)) (action3 A v)) as H.
  assert (Hsize : size3 (difference3 (action3 L (action3 A v)) (action3 A v)) <=
    3*d*size3 (action3 A v)).
  { rewrite <- (action3_identity (action3 A v)) at 2.
    rewrite action3_difference. apply action3_size_bound; [exact Hd|exact Hclose]. }
  eapply Rle_trans; [exact H|].
  eapply Rle_trans; [apply Rmult_le_compat_l; [lra|exact Hsize]|].
  replace ((norm_bound nm+1)*(3*d*size3 (action3 A v))) with
    ((3*(norm_bound nm+1)*d)*size3 (action3 A v)) by ring.
  unfold K. replace (3*(norm_bound nm+1)*C*d*length3 nm (action3 A v)) with
    ((3*(norm_bound nm+1)*d)*(C*length3 nm (action3 A v))) by ring.
  apply Rmult_le_compat_l; [nra|apply Hcoordinates].
Qed.

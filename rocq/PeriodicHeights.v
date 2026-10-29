From Stdlib Require Import Reals Psatz Lia Arith ZArith Classical_Prop.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices
  LatticeBasis LatticeReturns LatticeOrbit PeriodicReturns PeriodicWords PeriodicOrbits
  FiberProducts EuclideanNorm MatrixLimits DefectLimit EllipticPowers
  RealRotationDensity EllipticConjugacy EllipticRecurrence Concatenation PaperTarget NormGeometry DaniCorrespondence LatticeSystole
  SystoleContinuity SystoleCurves StableForgetting.
Open Scope R_scope.

Lemma length3_zero : forall nm, length3 nm zero3 = 0.
Proof.
  intro nm. unfold length3, zero3; simpl. rewrite Rabs_R0.
  change (Rmax 0 (length2 nm vzero) = 0). rewrite length2_zero, Rmax_left; lra.
Qed.

Lemma length3_size_upper : forall nm v,
  length3 nm v <= (norm_bound nm+1)*size3 v.
Proof.
  intros nm [a b c]. pose proof (length3_lipschitz nm (Vec3 a b c) zero3) as H.
  rewrite length3_zero in H.
  unfold difference3, size3, zero3 in H; simpl in H.
  rewrite !Rminus_0_r in H.
  pose proof (Rle_abs (length3 nm (Vec3 a b c)-0)).
  rewrite Rminus_0_r in H0. unfold size3; simpl; lra.
Qed.

Theorem systole_bounded_left_deformation : forall nm M,
  0 < M -> exists C, 0 < C /\ forall A L,
    det3 L = 1 -> entries_bounded3 (adj3 L) M ->
    systole nm A <= C*systole nm (mul3 L A).
Proof.
  intros nm M HM.
  destruct (length3_controls_coordinates nm) as [C [HC Hcoordinates]].
  set (D := 3*(norm_bound nm+1)*M*C).
  assert (HD : 0 < D) by
    (unfold D; pose proof (norm_bound_positive nm); repeat apply Rmult_lt_0_compat; lra).
  exists D; split; [exact HD|]. intros A L HL Hentries.
  apply systole_comparison_upper; [exact HD|]. intros z Hz.
  pose proof (action3_size_bound (adj3 L) M (action3 (mul3 L A) (real_vector z))
    ltac:(lra) Hentries) as Hsize.
  rewrite action3_product, <- (action3_product (adj3 L) L),
    (unimodular3_inverse_left L HL), action3_identity in Hsize.
  rewrite <- (action3_product L A (real_vector z)) in Hsize.
  pose proof (length3_size_upper nm (action3 A (real_vector z))) as Hnorm.
  pose proof (Hcoordinates (action3 (mul3 L A) (real_vector z))) as Hcoord.
  assert (Hchain : length3 nm (action3 A (real_vector z)) <=
    (norm_bound nm+1)*(3*M*size3 (action3 (mul3 L A) (real_vector z)))).
  { eapply Rle_trans; [exact Hnorm|]. apply Rmult_le_compat_l;
      [pose proof (norm_bound_positive nm); lra|exact Hsize]. }
  unfold D. eapply Rle_trans; [exact Hchain|].
  replace ((norm_bound nm+1)*(3*M*size3 (action3 (mul3 L A) (real_vector z)))) with
    ((3*(norm_bound nm+1)*M)*size3 (action3 (mul3 L A) (real_vector z))) by ring.
  replace (3*(norm_bound nm+1)*M*C*length3 nm (action3 (mul3 L A) (real_vector z))) with
    ((3*(norm_bound nm+1)*M)*(C*length3 nm (action3 (mul3 L A) (real_vector z)))) by ring.
  apply Rmult_le_compat_l; [pose proof (norm_bound_positive nm); nra|exact Hcoord].
Qed.

Lemma block3_inverse_entries : forall F M,
  det2 F = 1 -> 1 <= M -> opnorm (adj2 F) <= M ->
  entries_bounded3 (adj3 (block3 1 F)) M.
Proof.
  intros [a b c d] M HF HM Hb.
  pose proof (opnorm_entries (adj2 (Mat2 a b c d))) as Hentries.
  unfold entries_bounded3, adj3, block3, adj2 in *; simpl in *.
  unfold det2 in HF; simpl in HF.
  replace (a*d-b*c) with 1 by lra.
  replace (0*d-0*c) with 0 by ring. replace (0*c-a*0) with 0 by ring.
  repeat rewrite Rminus_0_r in *; repeat rewrite Rmult_1_l in *;
    repeat rewrite Rmult_0_l in *; repeat rewrite Rmult_0_r in *.
  repeat rewrite Rminus_0_r. repeat rewrite Rminus_0_l.
  rewrite ?Rabs_R0, ?Rabs_R1. repeat split; lra.
Qed.

Lemma fiber_translate_inverse_bound : forall E P C,
  0 <= C -> opnorm P <= C ->
  opnorm (adj2 (fiber_translate E P)) <=
    2*opnorm E*C*opnorm (adj2 E).
Proof.
  intros E P C HC HP. unfold fiber_translate.
  eapply Rle_trans; [apply opnorm_adjugate_bound|].
  pose proof (opnorm_submultiplicative (mul2 E P) (adj2 E)) as H1.
  pose proof (opnorm_submultiplicative E P) as H2.
  pose proof (opnorm_nonnegative E); pose proof (opnorm_nonnegative (adj2 E)).
  assert (H3 : opnorm E*opnorm P <= opnorm E*C) by
    (apply Rmult_le_compat_l; assumption).
  assert (H4 : opnorm (mul2 E P)*opnorm (adj2 E) <=
    (opnorm E*C)*opnorm (adj2 E)) by (apply Rmult_le_compat_r; lra).
  lra.
Qed.

Lemma periodic_real_time_cover : forall n t,
  0 <= t -> exists k r, 0 <= r < periodic_word_time n /\
    t = INR k*periodic_word_time n+r.
Proof.
  intros n t Ht.
  destruct (scaled_floor_approximation t (periodic_word_time n) Ht (periodic_word_time_positive n))
    as [k [Hk Hr]].
  exists (Z.to_nat k), (t-IZR k*periodic_word_time n).
  rewrite INR_IZR_INZ, Z2Nat.id by exact Hk. split; [exact Hr|ring].
Qed.

Lemma block3_determinant : forall a F, det3 (block3 a F) = a*det2 F.
Proof. intros a []; unfold det3, block3, det2; simpl; ring. Qed.

Theorem elliptic_periodic_height_bounded : forall nm n E,
  det2 E = 1 -> Rabs (trace2 (periodic_return n)) < 2 ->
  exists B, forall t, 0 <= t ->
    lattice_height_orbit nm (orbit_frame (periodic_word n) E) t <= B.
Proof.
  intros nm n E HE Hell.
  destruct (elliptic_powers_bounded (periodic_return n) (periodic_return_unimodular n) Hell)
    as [C [HC Hpowers]].
  set (M := 2*opnorm E*C*opnorm (adj2 E)+1).
  assert (HM1 : 1 <= M).
  { unfold M. pose proof (opnorm_nonnegative E); pose proof (opnorm_nonnegative (adj2 E)).
    assert (0 <= opnorm E*C) by nra. nra. }
  destruct (systole_bounded_left_deformation nm M ltac:(lra)) as [D [HD Hdeform]].
  destruct (compact_curve_systole_bounds nm
    (scaled_flow_curve (orbit_frame (periodic_word n) E)) 0 (periodic_word_time n)
    ltac:(pose proof (periodic_word_time_positive n); lra)
    (scaled_flow_curve_continuous _) ltac:(intro t; unfold scaled_flow_curve;
      rewrite mul3_determinant, flow_scale_determinant, orbit_frame_unimodular;
        try exact HE; try ring; pose proof (exp_pos t); lra)) as [m [U [Hm Hcompact]]].
  exists (D/m). intros t Ht.
  destruct (periodic_real_time_cover n t Ht) as [k [r [Hr Htime]]].
  set (L := block3 1 (fiber_translate E (matrix_power (periodic_return n) k))).
  assert (HL : det3 L = 1).
  { unfold L. rewrite block3_determinant, fiber_translate_unimodular; try ring; try exact HE.
    apply matrix_power_unimodular, periodic_return_unimodular. }
  assert (Hentries : entries_bounded3 (adj3 L) M).
  { unfold L. apply block3_inverse_entries.
    - apply fiber_translate_unimodular; [exact HE|apply matrix_power_unimodular, periodic_return_unimodular].
    - exact HM1.
    - eapply Rle_trans; [exact (fiber_translate_inverse_bound E
        (matrix_power (periodic_return n) k) C ltac:(lra) (Hpowers k))|]. unfold M; lra. }
  set (A := mul3 (diagonal_flow r) (orbit_frame (periodic_word n) E)).
  assert (HA : det3 A = 1).
  { unfold A; rewrite mul3_determinant, diagonal_flow_unimodular, orbit_frame_unimodular by exact HE; ring. }
  pose proof (Hdeform A L HL Hentries) as Hlower.
  pose proof (Hcompact r ltac:(lra)) as Hbase.
  change (m <= systole nm A <= U) in Hbase.
  assert (Hpositive : 0 < systole nm (mul3 L A)).
  { apply systole_positive. rewrite mul3_determinant, HL, HA; ring. }
  assert (Hsame : systole nm (mul3 (diagonal_flow t) (orbit_frame (periodic_word n) E)) =
    systole nm (mul3 L A)).
  { apply systole_same_lattice.
    - rewrite mul3_determinant, diagonal_flow_unimodular, orbit_frame_unimodular by exact HE; ring.
    - rewrite mul3_determinant, HL, HA; ring.
    - rewrite Htime. apply periodic_lattice_cycle; exact HE. }
  unfold lattice_height_orbit, cusp_height. rewrite Hsame.
  apply (Rmult_le_reg_r (m*systole nm (mul3 L A))); [nra|].
  replace (/systole nm (mul3 L A)*(m*systole nm (mul3 L A))) with m by (field; lra).
  replace (D/m*(m*systole nm (mul3 L A))) with (D*systole nm (mul3 L A)) by (field; lra).
  lra.
Qed.

Lemma block3_close_from_opnorm : forall F d,
  0 <= d -> opnorm (sub2 F id2) <= d -> matrices_close3 d id3 (block3 1 F).
Proof.
  intros [a b c e] d Hd Hb.
  pose proof (opnorm_entries (sub2 (Mat2 a b c e) id2)) as Hentries.
  unfold sub2, add2, scale2, id2 in Hentries,Hb; simpl in Hentries,Hb.
  unfold matrices_close3, entries_bounded3, matrix_difference3, block3, id3; simpl.
  replace (1-1) with 0 by ring. replace (0-0) with 0 by ring.
  rewrite ?Rabs_R0, !Rminus_0_r.
  replace (a-1) with (a+ -1*1) by ring.
  replace (e-1) with (e+ -1*1) by ring.
  replace (b+ -1*0) with b in Hentries,Hb by ring.
  replace (c+ -1*0) with c in Hentries,Hb by ring.
  repeat split; lra.
Qed.

Lemma fiber_translate_close : forall E P d,
  det2 E = 1 -> 0 < d ->
  opnorm (sub2 P id2) < d/(opnorm E*opnorm (adj2 E)+1) ->
  matrices_close3 d id3 (block3 1 (fiber_translate E P)).
Proof.
  intros E P d HE Hd Hp. apply block3_close_from_opnorm; [lra|].
  pose proof (EllipticRecurrence.conjugated_difference_bound E P id2) as H.
  rewrite mul2_id_right, (EllipticConjugacy.unimodular_right_inverse E HE) in H.
  set (C := opnorm E*opnorm (adj2 E)) in *.
  assert (HC : 0 <= C) by (unfold C; apply Rmult_le_pos; apply opnorm_nonnegative).
  assert (Hprod : C*opnorm (sub2 P id2) <= C*(d/(C+1))) by
    (apply Rmult_le_compat_l; lra).
  assert (Hsmall : C*(d/(C+1)) < d).
  { apply (Rmult_lt_reg_r (C+1)); [lra|].
    replace (C*(d/(C+1))*(C+1)) with (C*d) by (field; lra). nra. }
  unfold fiber_translate. lra.
Qed.

Theorem cusp_height_left_continuity : forall nm A,
  det3 A = 1 -> forall eps, 0 < eps -> exists d, 0 < d /\ forall L,
    det3 L = 1 -> matrices_close3 d id3 L ->
    Rabs (cusp_height nm (mul3 L A)-cusp_height nm A) < eps.
Proof.
  intros nm A HA eps He.
  destruct (systole_left_relative_continuity nm) as [K [HK Hb]].
  assert (Hs : 0 < systole nm A) by (apply systole_positive; exact HA).
  assert (Hheight : 0 < cusp_height nm A) by (unfold cusp_height; apply Rinv_0_lt_compat; exact Hs).
  set (d := Rmin (1/(2*K)) (eps/(4*K*cusp_height nm A))).
  assert (Hd : 0 < d) by (apply Rmin_pos; apply Rdiv_lt_0_compat; nra).
  assert (Hsmall : K*d <= 1/2).
  { pose proof (Rmin_l (1/(2*K)) (eps/(4*K*cusp_height nm A))) as H.
    change (d <= 1/(2*K)) in H.
    apply (Rmult_le_compat_r (2*K)) in H; [|nra].
    replace (1/(2*K)*(2*K)) with 1 in H by (field; lra). nra. }
  assert (Herr : 2*K*d*cusp_height nm A < eps).
  { pose proof (Rmin_r (1/(2*K)) (eps/(4*K*cusp_height nm A))) as H.
    change (d <= eps/(4*K*cusp_height nm A)) in H.
    apply (Rmult_le_compat_r (4*K*cusp_height nm A)) in H; [|nra].
    replace (eps/(4*K*cusp_height nm A)*(4*K*cusp_height nm A)) with eps in H by (field; nra). nra. }
  exists d; split; [exact Hd|]. intros L HL Hclose.
  pose proof (Hb A L d ltac:(lra) ltac:(lra) Hclose) as Hsys.
  assert (HLsys : 0 < systole nm (mul3 L A)).
  { apply systole_positive. rewrite mul3_determinant, HL, HA; ring. }
  pose proof (reciprocal_relative_difference _ _ _ Hs HLsys Hsys) as Hdiff.
  apply absolute_difference_sandwich in Hsys.
  assert (Hinv : /systole nm (mul3 L A) <= 2* /systole nm A).
  { assert (Hhalf : systole nm A/2 <= systole nm (mul3 L A)) by nra.
    pose proof (Rinv_le_contravar (systole nm A/2) (systole nm (mul3 L A)) ltac:(lra) Hhalf).
    replace (/(systole nm A/2)) with (2* /systole nm A) in H by (field; lra). exact H. }
  unfold cusp_height. rewrite Rabs_minus_sym.
  eapply Rle_lt_trans; [exact Hdiff|].
  apply Rle_lt_trans with (2*K*d* /systole nm A).
  - nra.
  - exact Herr.
Qed.

Theorem periodic_height_late_approximation : forall nm n E,
  det2 E = 1 -> Rabs (trace2 (periodic_return n)) < 2 ->
  forall t0 eps T, 0 < eps -> exists t,
    T <= t /\
    Rabs (lattice_height_orbit nm (orbit_frame (periodic_word n) E) t-
      lattice_height_orbit nm (orbit_frame (periodic_word n) E) t0) < eps.
Proof.
  intros nm n E HE Hell t0 eps T He.
  set (A := mul3 (diagonal_flow t0) (orbit_frame (periodic_word n) E)).
  assert (HA : det3 A = 1).
  { unfold A; rewrite mul3_determinant, diagonal_flow_unimodular, orbit_frame_unimodular by exact HE; ring. }
  destruct (cusp_height_left_continuity nm A HA eps He) as [d [Hd Hnear]].
  destruct (DaniCorrespondence.natural_cast_cofinal ((T-t0)/periodic_word_time n)) as [N HN].
  set (tol := d/(opnorm E*opnorm (adj2 E)+1)).
  assert (Htol : 0 < tol).
  { unfold tol. apply Rdiv_lt_0_compat; [exact Hd|].
    pose proof (opnorm_nonnegative E); pose proof (opnorm_nonnegative (adj2 E)); nra. }
  destruct (EllipticRecurrence.periodic_return_recurrent n Hell tol N Htol) as [k [Hk Hpower]].
  exists (INR k*periodic_word_time n+t0). split.
  - pose proof (le_INR N k Hk). pose proof (periodic_word_time_positive n) as Htau.
    apply (Rmult_lt_compat_r (periodic_word_time n)) in HN; [|exact Htau].
    replace ((T-t0)/periodic_word_time n*periodic_word_time n) with (T-t0) in HN by (field; lra).
    nra.
  - set (L := block3 1 (fiber_translate E (matrix_power (periodic_return n) k))).
    assert (HL : det3 L = 1).
    { unfold L. rewrite block3_determinant, fiber_translate_unimodular; try ring; try exact HE.
      apply matrix_power_unimodular, periodic_return_unimodular. }
    assert (Hclose : matrices_close3 d id3 L).
    { unfold L. apply fiber_translate_close; [exact HE|exact Hd|exact Hpower]. }
    specialize (Hnear L HL Hclose).
    assert (Hsame : systole nm
      (mul3 (diagonal_flow (INR k*periodic_word_time n+t0)) (orbit_frame (periodic_word n) E)) =
      systole nm (mul3 L A)).
    { apply systole_same_lattice.
      - rewrite mul3_determinant, diagonal_flow_unimodular, orbit_frame_unimodular by exact HE; ring.
      - rewrite mul3_determinant, HL, HA; ring.
      - apply periodic_lattice_cycle; exact HE. }
    unfold lattice_height_orbit, cusp_height. rewrite Hsame. exact Hnear.
Qed.

Definition periodic_height_values nm n E y := exists t,
  0 <= t /\ y = lattice_height_orbit nm (orbit_frame (periodic_word n) E) t.

Lemma periodic_height_values_nonempty : forall nm n E,
  exists y, periodic_height_values nm n E y.
Proof.
  intros nm n E. exists (lattice_height_orbit nm (orbit_frame (periodic_word n) E) 0).
  exists 0; split; [lra|reflexivity].
Qed.

Lemma periodic_height_values_bounded : forall nm n E,
  det2 E = 1 -> Rabs (trace2 (periodic_return n)) < 2 ->
  bound (periodic_height_values nm n E).
Proof.
  intros nm n E HE Hell.
  destruct (elliptic_periodic_height_bounded nm n E HE Hell) as [B Hb].
  exists B. intros y [t [Ht Hy]]. subst y; apply Hb; exact Ht.
Qed.

Definition periodic_peak nm n E (HE : det2 E = 1)
  (Hell : Rabs (trace2 (periodic_return n)) < 2) :=
  proj1_sig (completeness (periodic_height_values nm n E)
    (periodic_height_values_bounded nm n E HE Hell)
    (periodic_height_values_nonempty nm n E)).

Lemma periodic_peak_lub : forall nm n E HE Hell,
  is_lub (periodic_height_values nm n E) (periodic_peak nm n E HE Hell).
Proof.
  intros. apply (proj2_sig (completeness _ _ _)).
Qed.

Theorem periodic_peak_upper : forall nm n E HE Hell t,
  0 <= t -> lattice_height_orbit nm (orbit_frame (periodic_word n) E) t <=
    periodic_peak nm n E HE Hell.
Proof.
  intros nm n E HE Hell t Ht.
  destruct (periodic_peak_lub nm n E HE Hell) as [Hb _].
  apply Hb; exists t; auto.
Qed.

Theorem periodic_peak_near : forall nm n E HE Hell eps,
  0 < eps -> exists t, 0 <= t /\
    periodic_peak nm n E HE Hell-eps < lattice_height_orbit nm (orbit_frame (periodic_word n) E) t.
Proof.
  intros nm n E HE Hell eps He.
  destruct (classic (exists t, 0 <= t /\ periodic_peak nm n E HE Hell-eps <
    lattice_height_orbit nm (orbit_frame (periodic_word n) E) t)) as [Hyes|Hno]; auto.
  destruct (periodic_peak_lub nm n E HE Hell) as [_ Hleast].
  assert (Hb : is_upper_bound (periodic_height_values nm n E) (periodic_peak nm n E HE Hell-eps)).
  { intros y [t [Ht Hy]]. subst y.
    destruct (Rle_dec (lattice_height_orbit nm (orbit_frame (periodic_word n) E) t)
      (periodic_peak nm n E HE Hell-eps)); auto.
    exfalso; apply Hno; exists t; split; lra. }
  specialize (Hleast _ Hb). lra.
Qed.

Theorem periodic_peak_is_limsup : forall nm n E HE Hell,
  has_limsup (lattice_height_orbit nm (orbit_frame (periodic_word n) E))
    (periodic_peak nm n E HE Hell).
Proof.
  intros nm n E HE Hell. split.
  - intros eps He. exists 0. intros t Ht.
    pose proof (periodic_peak_upper nm n E HE Hell t Ht); lra.
  - intros eps T He.
    destruct (periodic_peak_near nm n E HE Hell (eps/2) ltac:(lra)) as [t0 [Ht0 Hpeak]].
    destruct (periodic_height_late_approximation nm n E HE Hell t0 (eps/2) T ltac:(lra))
      as [t [Ht Hnear]]. exists t; split; [exact Ht|].
    apply Rabs_def2 in Hnear. lra.
Qed.

Theorem periodic_peak_positive : forall nm n E HE Hell, 0 < periodic_peak nm n E HE Hell.
Proof.
  intros nm n E HE Hell.
  pose proof (periodic_peak_upper nm n E HE Hell 0 ltac:(lra)) as Hb.
  assert (Hpos : 0 < lattice_height_orbit nm (orbit_frame (periodic_word n) E) 0).
  { unfold lattice_height_orbit, cusp_height. apply Rinv_0_lt_compat, systole_positive.
    rewrite mul3_determinant, diagonal_flow_unimodular, orbit_frame_unimodular by exact HE; ring. }
  lra.
Qed.

Definition periodic_block_values nm n E L y := exists t,
  0 <= t <= INR L*periodic_word_time n /\
  y = lattice_height_orbit nm (orbit_frame (periodic_word n) E) t.

Lemma periodic_block_values_nonempty : forall nm n E L,
  exists y, periodic_block_values nm n E L y.
Proof.
  intros nm n E L. exists (lattice_height_orbit nm (orbit_frame (periodic_word n) E) 0).
  exists 0; split; [pose proof (pos_INR L); pose proof (periodic_word_time_positive n); nra|reflexivity].
Qed.
Lemma periodic_block_values_bounded : forall nm n E (HE : det2 E = 1)
  (Hell : Rabs (trace2 (periodic_return n)) < 2) L,
  bound (periodic_block_values nm n E L).
Proof.
  intros nm n E HE Hell L. exists (periodic_peak nm n E HE Hell).
  intros y [t [Ht Hy]]. subst y. apply periodic_peak_upper; lra.
Qed.

Definition periodic_block_peak nm n E HE Hell L :=
  proj1_sig (completeness (periodic_block_values nm n E L)
    (periodic_block_values_bounded nm n E HE Hell L)
    (periodic_block_values_nonempty nm n E L)).

Lemma periodic_block_peak_lub : forall nm n E HE Hell L,
  is_lub (periodic_block_values nm n E L) (periodic_block_peak nm n E HE Hell L).
Proof. intros. apply (proj2_sig (completeness _ _ _)). Qed.

Theorem periodic_block_peak_upper : forall nm n E HE Hell L,
  periodic_block_peak nm n E HE Hell L <= periodic_peak nm n E HE Hell.
Proof.
  intros nm n E HE Hell L. destruct (periodic_block_peak_lub nm n E HE Hell L) as [_ Hleast].
  apply Hleast. intros y [t [Ht Hy]]. subst y; apply periodic_peak_upper; lra.
Qed.

Theorem periodic_block_value_bound : forall nm n E HE Hell L t,
  0 <= t <= INR L*periodic_word_time n ->
  lattice_height_orbit nm (orbit_frame (periodic_word n) E) t <= periodic_block_peak nm n E HE Hell L.
Proof.
  intros nm n E HE Hell L t Ht. destruct (periodic_block_peak_lub nm n E HE Hell L) as [Hb _].
  apply Hb; exists t; auto.
Qed.

Theorem periodic_block_peaks_converge : forall nm n E HE Hell eps,
  0 < eps -> exists N, forall L, (N <= L)%nat ->
    Rabs (periodic_block_peak nm n E HE Hell L-periodic_peak nm n E HE Hell) < eps.
Proof.
  intros nm n E HE Hell eps He.
  destruct (periodic_peak_near nm n E HE Hell eps He) as [t [Ht Hnear]].
  destruct (DaniCorrespondence.natural_cast_cofinal (t/periodic_word_time n)) as [N HN].
  exists N; intros L HL.
  assert (Htime : t <= INR L*periodic_word_time n).
  { pose proof (le_INR N L HL). pose proof (periodic_word_time_positive n) as Htau.
    apply (Rmult_lt_compat_r (periodic_word_time n)) in HN; [|exact Htau].
    replace (t/periodic_word_time n*periodic_word_time n) with t in HN by (field; lra). nra. }
  pose proof (periodic_block_value_bound nm n E HE Hell L t ltac:(lra)) as Hb.
  pose proof (periodic_block_peak_upper nm n E HE Hell L) as Hu.
  apply Rabs_def1; lra.
Qed.

Theorem periodic_repetition_choice : forall nm n E HE Hell eps N,
  0 < eps -> exists L, (N <= L)%nat /\
    Rabs (periodic_block_peak nm n E HE Hell L-periodic_peak nm n E HE Hell) < eps /\
    opnorm (sub2 (matrix_power (periodic_return n) L) id2) < eps.
Proof.
  intros nm n E HE Hell eps N He.
  destruct (periodic_block_peaks_converge nm n E HE Hell eps He) as [N0 HN0].
  destruct (EllipticRecurrence.periodic_return_recurrent n Hell eps (Nat.max N N0) He)
    as [L [HL Hnear]]. exists L; split; [lia|]. split; [apply HN0; lia|exact Hnear].
Qed.

Theorem periodic_block_peak_attained : forall nm n E HE Hell L,
  exists t, 0 <= t <= INR L*periodic_word_time n /\
    periodic_block_peak nm n E HE Hell L = lattice_height_orbit nm (orbit_frame (periodic_word n) E) t.
Proof.
  intros nm n E HE Hell L.
  assert (Hinterval : 0 <= INR L*periodic_word_time n).
  { pose proof (pos_INR L); pose proof (periodic_word_time_positive n); nra. }
  assert (Hcontinuous : continuity (lattice_height_orbit nm (orbit_frame (periodic_word n) E))).
  { apply (cusp_height_curve_continuous nm (scaled_flow_curve (orbit_frame (periodic_word n) E))).
    - apply scaled_flow_curve_continuous.
    - intro t. unfold scaled_flow_curve.
      rewrite mul3_determinant, flow_scale_determinant, orbit_frame_unimodular;
        try exact HE; try ring; pose proof (exp_pos t); lra. }
  destruct (continuity_ab_maj _ 0 (INR L*periodic_word_time n) Hinterval ltac:(auto))
    as [t [Ht Htin]]. exists t; split; [exact Htin|]. apply Rle_antisym.
  - destruct (periodic_block_peak_lub nm n E HE Hell L) as [_ Hleast].
    apply Hleast. intros y [u [Hu Hy]]. subst y; apply Ht; exact Hu.
  - apply periodic_block_value_bound; exact Htin.
Qed.

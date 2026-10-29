From Stdlib Require Import Reals Psatz Lia Arith Classical ClassicalChoice.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices ReturnBranches
  FiberProducts EuclideanNorm MatrixLimits SymbolicCoding StableCoding
  LatticeBasis PaperTarget NormGeometry NormalizedFlow LatticeReturns
  SystoleContinuity LatticeSystole SystoleCurves Matrix3Limits CompactMatrices
  PeriodicReturns DaniCorrespondence PeriodicWords PositionalLimits SymbolicCocycle TwoSidedCoding.
Open Scope R_scope.

Definition chart_parameter_coordinate (u v : point) t j :=
  match j with O => fst u | S O => snd u | S (S O) => fst v
  | S (S (S O)) => snd v | _ => t end.

Theorem bounded_chart_parameters_subsequence : forall u v E ts M C,
  (forall i, inside (u i)) -> (forall i, stable_inside (v i)) ->
  (forall i, det2 (E i) = 1) -> (forall i, opnorm (E i) <= M) ->
  (forall i, Rabs (ts i) <= C) ->
  exists ns a b F t, indices_tend_to_infinity ns /\ inside a /\ stable_inside b /\
    det2 F = 1 /\ point_converges (fun i => u (ns i)) a /\
    point_converges (fun i => v (ns i)) b /\
    matrix_cv (fun i => E (ns i)) F /\ Un_cv (fun i => ts (ns i)) t.
Proof.
  intros u v E ts M C Hu Hv HE HM HC.
  assert (Hbound : forall i j, (j < 5)%nat ->
    Rabs (chart_parameter_coordinate (u i) (v i) (ts i) j) <= Rabs C+1).
  { intros i j Hj. pose proof (Hu i) as HU; pose proof (Hv i) as HV.
    unfold inside,in_U in HU; unfold stable_inside,in_V in HV.
    pose proof (Rabs_pos C); pose proof (Rle_abs C).
    destruct j as [|[|[|[|[|j]]]]]; simpl; try lia;
      try (apply Rabs_le; split; lra). specialize (HC i); lra. }
  destruct (finite_coordinates_subsequence 5
    (fun i j => chart_parameter_coordinate (u i) (v i) (ts i) j) (Rabs C+1) Hbound)
    as [ns [L [Hns HL]]].
  assert (HU : point_converges (fun i => u (ns i)) (L 0%nat,L 1%nat)).
  { split; [exact (HL 0%nat ltac:(lia))|exact (HL 1%nat ltac:(lia))]. }
  assert (HV : point_converges (fun i => v (ns i)) (L 2%nat,L 3%nat)).
  { split; [exact (HL 2%nat ltac:(lia))|exact (HL 3%nat ltac:(lia))]. }
  assert (HT : Un_cv (fun i => ts (ns i)) (L 4%nat)) by exact (HL 4%nat ltac:(lia)).
  destruct (bounded_matrix2_subsequence (fun i => E (ns i)) M (fun i => HM (ns i)))
    as [ms [F [Hms HF]]].
  exists (fun i => ns (ms i)), (L 0%nat,L 1%nat), (L 2%nat,L 3%nat), F, (L 4%nat).
  split; [apply cofinal_composition; assumption|]. split.
  - unfold inside,in_U; simpl. split.
    + apply (scalar_limit_closed_interval _ _ _ _ (proj1 HU)); intro i; exact (proj1 (Hu (ns i))).
    + apply (scalar_limit_closed_interval _ _ _ _ (proj2 HU)); intro i; exact (proj2 (Hu (ns i))).
  - split.
    + unfold stable_inside,in_V; simpl. split.
      * apply (scalar_limit_closed_interval _ _ _ _ (proj1 HV)); intro i; exact (proj1 (Hv (ns i))).
      * apply (scalar_limit_closed_interval _ _ _ _ (proj2 HV)); intro i; exact (proj2 (Hv (ns i))).
    + split.
      * apply (unimodular_limit _ _ HF); exact (fun i => HE (ns (ms i))).
      * split; [exact (point_cv_subsequence _ _ ms HU Hms)|].
        split; [exact (point_cv_subsequence _ _ ms HV Hms)|].
        split; [exact HF|exact (scalar_cv_subsequence _ _ ms HT Hms)].
Qed.

Lemma diagonal_flow_sequence_limit : forall ts t,
  Un_cv ts t -> matrix3_cv (fun i => diagonal_flow (ts i)) (diagonal_flow t).
Proof.
  intros ts t Ht. apply matrix3_curve_sequence_limit; [|exact Ht].
  apply matrix_curve_from_components; unfold diagonal_flow, flow_scale; simpl; intro x; reg;
    pose proof (exp_pos x); nra.
Qed.

Theorem flowing_normalized_frame_limit : forall u v E ts a b F t,
  point_converges u a -> point_converges v b -> matrix_cv E F -> Un_cv ts t ->
  inside a -> stable_inside b ->
  matrix3_cv (fun i => mul3 (diagonal_flow (ts i))
    (normalized_frame (fst (u i)) (snd (u i)) (fst (v i)) (snd (v i)) (E i)))
    (mul3 (diagonal_flow t) (normalized_frame (fst a) (snd a) (fst b) (snd b) F)).
Proof.
  intros u v E ts a b F t Hu Hv HE Ht Ha Hb. apply matrix3_cv_product.
  - apply diagonal_flow_sequence_limit; exact Ht.
  - apply normalized_frame_sequence_limit; try assumption.
    pose proof (chart_weight_bounds _ _ _ _ Ha Hb); lra.
Qed.

Definition flowing_chart u v E t := mul3 (diagonal_flow t)
  (normalized_frame (fst u) (snd u) (fst v) (snd v) E).

Theorem bounded_flowing_charts_subsequence : forall u v E ts M C,
  (forall i, inside (u i)) -> (forall i, stable_inside (v i)) ->
  (forall i, det2 (E i) = 1) -> (forall i, opnorm (E i) <= M) ->
  (forall i, Rabs (ts i) <= C) ->
  exists ns A, indices_tend_to_infinity ns /\ det3 A = 1 /\
    matrix3_cv (fun i => flowing_chart (u (ns i)) (v (ns i)) (E (ns i)) (ts (ns i))) A.
Proof.
  intros u v E ts M C Hu Hv HE HM HC.
  destruct (bounded_chart_parameters_subsequence u v E ts M C Hu Hv HE HM HC)
    as [ns [a [b [F [t [Hns [Ha [Hb [HF [HU [HV [HEcv HT]]]]]]]]]]]].
  exists ns, (flowing_chart a b F t); split; [exact Hns|]. split.
  - unfold flowing_chart. rewrite mul3_determinant, diagonal_flow_unimodular,
      normalized_frame_unimodular; try assumption; ring.
  - apply flowing_normalized_frame_limit; assumption.
Qed.

Theorem bounded_chart_heights : forall nm M C,
  exists B, forall u v E t,
    inside u -> stable_inside v -> det2 E = 1 -> opnorm E <= M -> Rabs t <= C ->
    cusp_height nm (flowing_chart u v E t) <= B.
Proof.
  intros nm M C. apply NNPP; intro Hno.
  assert (Hchoose : forall n, exists p : point*point*mat2*R,
    inside (fst (fst (fst p))) /\ stable_inside (snd (fst (fst p))) /\
    det2 (snd (fst p)) = 1 /\ opnorm (snd (fst p)) <= M /\ Rabs (snd p) <= C /\
    INR n < cusp_height nm (flowing_chart (fst (fst (fst p))) (snd (fst (fst p))) (snd (fst p)) (snd p))).
  { intro n. apply NNPP; intro Hnone. apply Hno. exists (INR n).
    intros u v E t Hu Hv HE HM HC.
    destruct (Rle_dec (cusp_height nm (flowing_chart u v E t)) (INR n)) as [Hyes|Hbad]; auto.
    exfalso; apply Hnone; exists (((u,v),E),t); simpl; repeat first [assumption|split]; lra. }
  destruct (@choice nat (point*point*mat2*R)%type _ Hchoose) as [p Hp].
  set (u := fun i => fst (fst (fst (p i)))).
  set (v := fun i => snd (fst (fst (p i)))).
  set (E := fun i => snd (fst (p i))).
  set (ts := fun i => snd (p i)).
  destruct (bounded_flowing_charts_subsequence u v E ts M C
    ltac:(intro i; exact (proj1 (Hp i)))
    ltac:(intro i; exact (proj1 (proj2 (Hp i))))
    ltac:(intro i; exact (proj1 (proj2 (proj2 (Hp i)))))
    ltac:(intro i; exact (proj1 (proj2 (proj2 (proj2 (Hp i))))))
    ltac:(intro i; exact (proj1 (proj2 (proj2 (proj2 (proj2 (Hp i)))))))) as [ns [A [Hns [HA Hcv]]]].
  pose proof (cusp_height_sequence_limit nm _ A HA Hcv) as Hheight.
  destruct (Hheight 1 ltac:(lra)) as [I HI].
  destruct (natural_cast_cofinal (cusp_height nm A+1)) as [N HN].
  destruct (Hns N) as [J HJ].
  specialize (HI (Nat.max I J) ltac:(lia)).
  pose proof (HJ (Nat.max I J) ltac:(lia)) as Hidx.
  pose proof (le_INR _ _ Hidx) as Hcast.
  pose proof (Hp (ns (Nat.max I J))) as Hlarge.
  change (inside (u (ns (Nat.max I J))) /\ stable_inside (v (ns (Nat.max I J))) /\
    det2 (E (ns (Nat.max I J))) = 1 /\ opnorm (E (ns (Nat.max I J))) <= M /\
    Rabs (ts (ns (Nat.max I J))) <= C /\
    INR (ns (Nat.max I J)) < cusp_height nm
      (flowing_chart (u (ns (Nat.max I J))) (v (ns (Nat.max I J)))
        (E (ns (Nat.max I J))) (ts (ns (Nat.max I J))))) in Hlarge.
  unfold Rdist in HI; apply Rabs_def2 in HI; lra.
Qed.

Theorem bounded_periodic_representative_heights : forall nm M,
  exists B, forall n j E t,
    (j <= n)%nat -> det2 E = 1 -> opnorm E <= M ->
    0 <= t <= orbit_roof_time (orbit_shift j (periodic_word n)) ->
    cusp_height nm (periodic_lifted_representative n j E t) <= B.
Proof.
  intros nm M.
  set (K := (Rabs M+1)*(2*constant_power_bound+1)).
  destruct (bounded_chart_heights nm K (Rabs (ln 11)+1)) as [B HB].
  exists B; intros n j E t Hj HE HM Ht.
  apply HB.
  - apply u_code_inside.
  - apply v_code_inside.
  - rewrite det2_mul, HE, orbit_product_matches_future, factor_product_unimodular; ring.
  - assert (HP : opnorm (orbit_product j (periodic_word n)) <= 2*constant_power_bound).
    { rewrite orbit_product_matches_future.
      replace (fiber_product j (future_of (periodic_word n))) with (fiber_product j (periodic_future n)) by
        (apply fiber_product_extensional; intro k; symmetry; apply periodic_word_future).
      apply partial_period_uniform_bound; exact Hj. }
    eapply Rle_trans; [apply opnorm_submultiplicative|]. unfold K.
    pose proof (opnorm_nonnegative E); pose proof (Rle_abs M); pose proof (Rabs_pos M).
    pose proof constant_power_bound_nonnegative.
    eapply Rle_trans with ((Rabs M+1)*(2*constant_power_bound)).
    + apply Rmult_le_compat; auto using opnorm_nonnegative; lra.
    + nra.
  - assert (Hroof : orbit_roof_time (orbit_shift j (periodic_word n)) < ln 11).
    { unfold orbit_roof_time. apply ln_increasing;
      pose proof (orbit_roof_scale_bounds (orbit_shift j (periodic_word n))); lra. }
    rewrite Rabs_right by lra. pose proof (Rle_abs (ln 11)); lra.
Qed.

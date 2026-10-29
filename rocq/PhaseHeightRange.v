From Stdlib Require Import Reals Psatz Lia Arith Classical ClassicalChoice Ranalysis5.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  EllipticContinuity LimitingConvergence CompactMatrices
  PeakContinuity PeakLocalContinuity PeakPhasePath ParabolicPhases PaperTarget SystoleCurves.
Open Scope R_scope.

Lemma scalar_cv_from_tail : forall u l I,
  Un_cv (fun i => u (i+I)%nat) l -> Un_cv u l.
Proof.
  intros u l I Hu eps He. destruct (Hu eps He) as [N HN].
  exists (N+I)%nat; intros n Hn. specialize (HN (n-I)%nat ltac:(lia)).
  replace (n-I+I)%nat with n in HN by lia; exact HN.
Qed.
Lemma scalar_cv_eventually_in_open_interval : forall u t a b,
  Un_cv u t -> a < t < b -> exists I, forall i, (I <= i)%nat -> a < u i < b.
Proof.
  intros u t a b Hu Ht.
  set (e := Rmin (t-a) (b-t)/2).
  assert (He : 0 < e) by (unfold e; pose proof (Rmin_pos (t-a) (b-t) ltac:(lra) ltac:(lra)); lra).
  destruct (Hu e He) as [I HI]. exists I; intros i Hi; specialize (HI i Hi).
  unfold Rdist in HI; apply Rabs_def2 in HI. unfold e in HI.
  pose proof (Rmin_l (t-a) (b-t)); pose proof (Rmin_r (t-a) (b-t)); lra.
Qed.

Theorem parabolic_phase_peak_sequence_limit : forall nm X (HX : det2 X = 1) ts t,
  Un_cv ts t -> -2 < t < 2 ->
  Un_cv (fun i => parameter_peak nm X (parabolic_phase (ts i))) (parameter_peak nm X (parabolic_phase t)).
Proof.
  intros nm X HX ts t Ht Hrange.
  destruct (scalar_cv_eventually_in_open_interval ts t (-2) 2 Ht Hrange) as [I HI].
  apply (scalar_cv_from_tail _ _ I).
  apply (parameter_peak_sequence_limit nm (fun _ => X) X
    (fun i => parabolic_phase (ts (i+I)%nat)) (parabolic_phase t)).
  - intro i; apply parabolic_phase_valid; [exact HX|apply HI; lia].
  - apply parabolic_phase_valid; assumption.
  - apply matrix_cv_constant.
  - apply parabolic_phase_sequence_limit; [exact (scalar_cv_subsequence ts t _ Ht (cofinal_offset I))|lra].
Qed.

Theorem sequential_continuity_pt : forall f t,
  (forall u, Un_cv u t -> Un_cv (fun i => f (u i)) (f t)) -> continuity_pt f t.
Proof.
  intros f t Hseq. unfold continuity_pt,continue_in,limit1_in,limit_in; simpl.
  intros eps He; apply NNPP; intro Hno.
  assert (Hchoose : forall i, exists u, Rabs (u-t) < (1/2)^i /\ eps <= Rabs (f u-f t)).
  { intro i. apply NNPP; intro Hnone. apply Hno. exists ((1/2)^i); split; [apply pow_lt; lra|].
    intros u [_ Hu]. unfold Rdist in Hu |- *.
    destruct (Rlt_dec (Rabs (f u-f t)) eps) as [Hyes|Hbad]; auto.
    exfalso; apply Hnone; exists u; split; lra. }
  destruct (@choice nat R _ Hchoose) as [u Hu].
  assert (Hcv : Un_cv u t).
  { intros e Hpos. destruct (pow_lt_1_zero (1/2) ltac:(rewrite Rabs_right; lra) e Hpos) as [N HN].
    exists N; intros i Hi; specialize (HN i Hi).
    rewrite Rabs_right in HN by (apply Rle_ge,pow_le; lra).
    unfold Rdist; specialize (Hu i); lra. }
  destruct (Hseq u Hcv eps He) as [N HN]. specialize (HN N ltac:(lia)).
  pose proof (proj2 (Hu N)); unfold Rdist in HN; lra.
Qed.

Theorem parabolic_phase_peak_continuous : forall nm X (HX : det2 X = 1) t,
  -2 < t < 2 -> continuity_pt (fun u => parameter_peak nm X (parabolic_phase u)) t.
Proof.
  intros nm X HX t Ht; apply sequential_continuity_pt; intros u Hu.
  apply (parabolic_phase_peak_sequence_limit nm X HX u t Hu Ht).
Qed.

Theorem phase_height_realizes_levels : forall nm X (HX : det2 X = 1) H,
  parameter_peak nm X (parabolic_phase 0) < H ->
  exists t, 0 < t < 2 /\ parameter_peak nm X (parabolic_phase t) = H.
Proof.
  intros nm X HX H Hstart.
  destruct (parabolic_phase_height_bracket nm X HX H) as [b [Hb Hend]].
  destruct (IVT_interv (fun u => parameter_peak nm X (parabolic_phase u)-H) 0 b
    ltac:(intros a Ha; apply continuity_pt_minus;
      [apply (parabolic_phase_peak_continuous nm X HX a); lra|reg])
    ltac:(lra) ltac:(lra) ltac:(lra)) as [t [Ht Hvalue]].
  exists t; split.
  - split; [|lra]. destruct (Req_dec t 0) as [Hz|Hz]; [subst t; lra|lra].
  - lra.
Qed.

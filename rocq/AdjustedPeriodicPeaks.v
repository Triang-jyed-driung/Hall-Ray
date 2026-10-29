From Stdlib Require Import Reals Psatz Lia Arith Ranalysis5.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits DefectLimit
  DefectPhases EllipticConjugacy PeriodicReturns RotationDensity LimitingConvergence CompactMatrices
  PeakLocalContinuity PeakPhasePath ParabolicPhases PhaseHeightRange PeakContinuity
  PeakConvergence PeriodicHeights LimitingFamilies PaperTarget SystoleCurves.
Open Scope R_scope.

Lemma opnorm_self_difference : forall A, opnorm (sub2 A A) = 0.
Proof.
  intro A. replace (sub2 A A) with zero2 by
    (destruct A; apply mat2_ext; unfold sub2,add2,scale2,zero2; simpl; ring).
  apply opnorm_zero.
Qed.
Lemma identity_unimodular : det2 id2 = 1.
Proof. unfold id2,det2; simpl; ring. Qed.

Lemma matrix_limit_eventually_trace_bound : forall U A c,
  matrix_cv U A -> Rabs (trace2 A) < c ->
  exists I, forall i, (I <= i)%nat -> Rabs (trace2 (U i)) < c.
Proof.
  intros U A c HU HA. pose proof (matrix_cv_trace U A HU) as Htrace.
  destruct (Htrace ((c-Rabs (trace2 A))/2) ltac:(lra)) as [I HI].
  exists I; intros i Hi. specialize (HI i Hi); unfold Rdist in HI.
  pose proof (Rabs_triang (trace2 (U i)-trace2 A) (trace2 A)) as H.
  replace (trace2 (U i)-trace2 A+trace2 A) with (trace2 (U i)) in H by ring; lra.
Qed.

Theorem periodic_peak_approximation_with_trace_margin : forall nm X S HX HA Hphase c,
  det2 S = 1 -> orthogonal2 S -> Rabs (trace2 (phase_limit_original S)) < c -> c < 2 ->
  forall eps N, 0 < eps -> exists n, (N <= n)%nat /\ Rabs (trace2 (periodic_return n)) < c /\
    opnorm (sub2 (matrix_power constant_rotation n) S) < eps /\
    forall Hn, Rabs (periodic_peak nm n X HX Hn-
      limiting_peak nm X (phase_limit_original S) HX HA Hphase) < eps.
Proof.
  intros nm X S HX HA Hphase c HSd HSo Hc Hc2 eps N He.
  destruct (constant_rotation_dense_subsequence S HSd HSo) as [ns [Hns HS]].
  destruct (matrix_limit_eventually_trace_bound _ _ c (periodic_returns_matrix_limit ns S Hns HS) Hc)
    as [I HI].
  set (ms := fun i => ns (i+I)%nat).
  assert (Hms : indices_tend_to_infinity ms) by exact (cofinal_composition ns _ Hns (cofinal_offset I)).
  assert (Hrotation : matrix_cv (fun i => matrix_power constant_rotation (ms i)) S)
    by exact (matrix_cv_subsequence _ _ _ HS (cofinal_offset I)).
  assert (Hell : forall i, Rabs (trace2 (periodic_return (ms i))) < 2)
    by (intro i; unfold ms; pose proof (HI (i+I)%nat ltac:(lia)); lra).
  pose proof (periodic_peaks_converge nm ms (fun _ => X) X S (fun _ => HX) Hell HX HA Hphase
    Hms (matrix_cv_constant X) Hrotation) as Hpeaks.
  destruct (Hrotation eps He) as [J HJ]; destruct (Hpeaks eps He) as [K HK]; destruct (Hms N) as [M HM].
  set (i := Nat.max J (Nat.max K M)). exists (ms i); split; [apply HM; unfold i; lia|].
  split; [apply HI; lia|]. split; [apply HJ; unfold i; lia|]. intros Hn.
  rewrite (periodic_peak_unique_proofs nm (ms i) X HX HX Hn (Hell i)). exact (HK i ltac:(unfold i; lia)).
Qed.

Lemma phase_height_realizes_between : forall nm X (HX : det2 X = 1) H b,
  0 < b < 2 -> parameter_peak nm X (parabolic_phase 0) < H ->
  H < parameter_peak nm X (parabolic_phase b) ->
  exists t, 0 < t < b /\ parameter_peak nm X (parabolic_phase t) = H.
Proof.
  intros nm X HX H b Hb Hstart Hend.
  destruct (IVT_interv (fun u => parameter_peak nm X (parabolic_phase u)-H) 0 b
    ltac:(intros a Ha; apply continuity_pt_minus;
      [apply (parabolic_phase_peak_continuous nm X HX a); lra|reg])
    ltac:(lra) ltac:(lra) ltac:(lra)) as [t [Ht Hvalue]].
  exists t; split.
  - split; destruct (Req_dec t 0); destruct (Req_dec t b); subst; try lra.
  - lra.
Qed.
Lemma parabolic_phase_absolute_trace : forall t,
  0 <= t -> Rabs (trace2 (phase_limit_original (parabolic_phase t))) = t.
Proof.
  intros t Ht. rewrite parabolic_phase_trace; destruct parabolic_orientation;
    [rewrite Rabs_right|rewrite Rabs_Ropp,Rabs_right]; lra.
Qed.

Definition height_threshold nm := Rmax 1 (parameter_peak nm id2 (parabolic_phase 0)).

Theorem adjusted_periodic_peak_choice : forall nm H,
  height_threshold nm < H -> exists delta c, 0 < delta < 1 /\ 0 < c < 2 /\
  forall X (HX : det2 X = 1), opnorm (sub2 X id2) <= delta ->
  forall eps N, 0 < eps -> exists n, (N <= n)%nat /\ Rabs (trace2 (periodic_return n)) < c /\
    forall Hn, Rabs (periodic_peak nm n X HX Hn-H) < eps.
Proof.
  intros nm H HH.
  assert (Hstart : parameter_peak nm id2 (parabolic_phase 0) < H).
  { unfold height_threshold in HH; pose proof (Rmax_r 1 (parameter_peak nm id2 (parabolic_phase 0))); lra. }
  destruct (parabolic_phase_height_bracket nm id2 identity_unimodular H) as [b [Hb Hend]].
  pose proof (parabolic_phase_valid id2 0 identity_unimodular ltac:(lra)) as HV0.
  pose proof (parabolic_phase_valid id2 b identity_unimodular ltac:(lra)) as HVb.
  destruct (parameter_peak_joint_continuity nm id2 (parabolic_phase 0) HV0
    ((H-parameter_peak nm id2 (parabolic_phase 0))/2) ltac:(lra)) as [d0 [Hd0 H0]].
  destruct (parameter_peak_joint_continuity nm id2 (parabolic_phase b) HVb
    ((parameter_peak nm id2 (parabolic_phase b)-H)/2) ltac:(lra)) as [db [Hdb Hbcont]].
  set (delta := Rmin (1/2) (Rmin d0 db/2)).
  assert (Hd : 0 < delta) by (apply Rmin_pos; [lra|pose proof (Rmin_pos d0 db Hd0 Hdb); lra]).
  assert (Hdboth : delta < d0 /\ delta < db).
  { pose proof (Rmin_r (1/2) (Rmin d0 db/2)) as Hmin.
    change (delta <= Rmin d0 db/2) in Hmin.
    pose proof (Rmin_l d0 db); pose proof (Rmin_r d0 db); lra. }
  assert (Hhalf : delta <= 1/2) by apply Rmin_l.
  exists delta, ((b+2)/2). split; [lra|].
  split; [lra|]. intros X HX HXclose eps N He.
  assert (Hlow : parameter_peak nm X (parabolic_phase 0) < H).
  { pose proof (H0 X (parabolic_phase 0) (parabolic_phase_valid X 0 HX ltac:(lra))
      ltac:(lra) ltac:(rewrite opnorm_self_difference; lra)) as Hnear.
    apply Rabs_def2 in Hnear; lra. }
  assert (Hhigh : H < parameter_peak nm X (parabolic_phase b)).
  { pose proof (Hbcont X (parabolic_phase b) (parabolic_phase_valid X b HX ltac:(lra))
      ltac:(lra) ltac:(rewrite opnorm_self_difference; lra)) as Hnear.
    apply Rabs_def2 in Hnear; lra. }
  destruct (phase_height_realizes_between nm X HX H b Hb Hlow Hhigh) as [t [Ht Hvalue]].
  pose proof (parabolic_phase_special_orthogonal t ltac:(lra)) as [HSd HSo].
  pose proof (phase_limit_original_unimodular _ HSd) as HA.
  pose proof (parabolic_phase_elliptic t ltac:(lra)) as Hell.
  destruct (periodic_peak_approximation_with_trace_margin nm X (parabolic_phase t) HX HA Hell ((b+2)/2)
    HSd HSo ltac:(rewrite parabolic_phase_absolute_trace by lra; lra) ltac:(lra) eps N He)
    as [n [Hn [Htrace [Hclose Hpeak]]]].
  exists n; split; [exact Hn|]. split; [exact Htrace|].
  rewrite (parameter_peak_valid nm X (parabolic_phase t) HX HA Hell
    (parabolic_phase_valid X t HX ltac:(lra))) in Hvalue.
  intro Hp; specialize (Hpeak Hp); rewrite Hvalue in Hpeak; exact Hpeak.
Qed.

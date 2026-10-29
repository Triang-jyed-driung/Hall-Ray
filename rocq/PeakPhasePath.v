From Stdlib Require Import Reals Psatz Lia FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  DefectLimit DefectPhases EllipticConjugacy EllipticContinuity PeriodicReturns
  LimitingConvergence Matrix3Limits ParabolicPhases ParabolicDepth
  PeakLocalContinuity LimitingFamilies PaperTarget SystoleCurves.
Open Scope R_scope.

Lemma circle_matrix_sequence_limit : forall c s a b,
  Un_cv c a -> Un_cv s b ->
  matrix_cv (fun i => circle_matrix (c i) (s i)) (circle_matrix a b).
Proof.
  intros c s a b Hc Hs. apply coordinates_matrix_cv.
  unfold coordinate_cv,circle_matrix; simpl. repeat split; scalar_cv_algebra.
Qed.
Lemma matrix_cv_negative : forall U A,
  matrix_cv U A -> matrix_cv (fun i => scale2 (-1) (U i)) (scale2 (-1) A).
Proof.
  intros U A HU; apply matrix_cv_coordinates in HU; destruct HU as (H11&H12&H21&H22).
  apply coordinates_matrix_cv; unfold coordinate_cv,scale2; simpl.
  repeat split; scalar_cv_algebra.
Qed.

Theorem trace_phase_sequence_limit : forall side ts t,
  Un_cv ts t -> -2 <= t <= 2 ->
  matrix_cv (fun i => trace_phase side (ts i)) (trace_phase side t).
Proof.
  intros side ts t Ht Hrange.
  assert (Hsquare : Un_cv (fun i => (ts i)^2) (t^2)).
  { replace (fun i => (ts i)^2) with (fun i => ts i*ts i) by
      (apply functional_extensionality; intro i; simpl; ring).
    replace (t^2) with (t*t) by (simpl; ring); apply CV_mult; assumption. }
  assert (Hgap : Un_cv (fun i => trace_phase_gap (ts i)) (trace_phase_gap t)).
  { unfold trace_phase_gap. apply scalar_cv_square_root.
    - apply CV_minus; [apply real_constant_cv|exact Hsquare].
    - pose proof phase_amplitude_gt_two; nra. }
  unfold trace_phase; destruct side; apply circle_matrix_sequence_limit;
    unfold Rdiv; scalar_cv_algebra.
Qed.

Theorem parabolic_phase_sequence_limit : forall ts t,
  Un_cv ts t -> -2 <= t <= 2 ->
  matrix_cv (fun i => parabolic_phase (ts i)) (parabolic_phase t).
Proof.
  intros ts t Ht Hrange; unfold parabolic_phase; destruct parabolic_orientation.
  - apply trace_phase_sequence_limit; assumption.
  - apply matrix_cv_negative,trace_phase_sequence_limit; assumption.
Qed.
Lemma phase_original_sequence_limit : forall R S,
  matrix_cv R S -> matrix_cv (fun i => phase_limit_original (R i)) (phase_limit_original S).
Proof.
  intros R S HR; apply matrix_cv_right_product,matrix_cv_right_product,matrix_cv_left_product; exact HR.
Qed.

Lemma parabolic_phase_elliptic : forall t,
  -2 < t < 2 -> Rabs (trace2 (phase_limit_original (parabolic_phase t))) < 2.
Proof.
  intros t Ht; rewrite parabolic_phase_trace; destruct parabolic_orientation; apply Rabs_def1; lra.
Qed.
Theorem parabolic_phase_valid : forall X t,
  det2 X = 1 -> -2 < t < 2 -> valid_peak_parameters X (parabolic_phase t).
Proof.
  intros X t HX Ht.
  destruct (parabolic_phase_special_orthogonal t ltac:(lra)) as [Hd Ho].
  unfold valid_peak_parameters. split; [exact HX|]. split; [exact Hd|]. split; [exact Ho|].
  split; [apply phase_limit_original_unimodular; exact Hd|apply parabolic_phase_elliptic; exact Ht].
Qed.

Definition parabolic_approach n := 2-(1/2)^n.
Lemma parabolic_approach_range : forall n, 1 <= parabolic_approach n < 2.
Proof.
  intro n; unfold parabolic_approach.
  pose proof (pow_lt (1/2) n ltac:(lra)).
  pose proof (pow_incr (1/2) 1 n ltac:(lra)); rewrite pow1 in H0; lra.
Qed.
Lemma parabolic_approach_limit : Un_cv parabolic_approach 2.
Proof.
  intros eps He. destruct (pow_lt_1_zero (1/2) ltac:(rewrite Rabs_right; lra) eps He) as [N HN].
  exists N; intros n Hn; specialize (HN n Hn). unfold Rdist,parabolic_approach.
  replace (2-(1/2)^n-2) with (-((1/2)^n)) by ring. rewrite Rabs_Ropp; exact HN.
Qed.

Theorem parabolic_phase_heights_diverge : forall nm X (HX : det2 X = 1) B,
  exists I, forall i, (I <= i)%nat -> B < parameter_peak nm X (parabolic_phase (parabolic_approach i)).
Proof.
  intros nm X HX B.
  assert (Hdet : forall i, det2 (phase_limit_original (parabolic_phase (parabolic_approach i))) = 1).
  { intro i; apply phase_limit_original_unimodular.
    exact (proj1 (parabolic_phase_special_orthogonal (parabolic_approach i) ltac:(pose proof (parabolic_approach_range i); lra))). }
  assert (Hell : forall i, Rabs (trace2 (phase_limit_original (parabolic_phase (parabolic_approach i)))) < 2).
  { intro i; apply parabolic_phase_elliptic; pose proof (parabolic_approach_range i); lra. }
  assert (Htrace : (trace2 (phase_limit_original (parabolic_phase 2)))^2 = 4).
  { rewrite parabolic_phase_trace; destruct parabolic_orientation; nra. }
  destruct (limiting_peaks_diverge_at_parabolic nm X HX
    (fun i => phase_limit_original (parabolic_phase (parabolic_approach i)))
    (phase_limit_original (parabolic_phase 2)) Hdet Hell
    (phase_original_sequence_limit _ _ (parabolic_phase_sequence_limit _ _ parabolic_approach_limit ltac:(lra)))
    parabolic_endpoint_positive Htrace B) as [I HI].
  exists I; intros i Hi.
  rewrite (parameter_peak_valid nm X (parabolic_phase (parabolic_approach i)) HX (Hdet i) (Hell i)) by
    (apply parabolic_phase_valid; [exact HX|pose proof (parabolic_approach_range i); lra]).
  apply HI; exact Hi.
Qed.

Theorem parabolic_phase_height_bracket : forall nm X (HX : det2 X = 1) B,
  exists b, 0 < b < 2 /\ B < parameter_peak nm X (parabolic_phase b).
Proof.
  intros nm X HX B. destruct (parabolic_phase_heights_diverge nm X HX B) as [I HI].
  exists (parabolic_approach I); split; [pose proof (parabolic_approach_range I); lra|apply HI; lia].
Qed.

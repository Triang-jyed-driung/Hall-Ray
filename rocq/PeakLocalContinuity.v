From Stdlib Require Import Reals Psatz Lia Arith Classical ClassicalChoice ClassicalDescription FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  LimitingConvergence LimitingFamilies PeakContinuity PaperTarget SystoleCurves.
Open Scope R_scope.

Definition valid_peak_parameters X R :=
  det2 X = 1 /\ det2 R = 1 /\ orthogonal2 R /\
  det2 (phase_limit_original R) = 1 /\ Rabs (trace2 (phase_limit_original R)) < 2.

Definition parameter_peak nm X R :=
  match excluded_middle_informative (valid_peak_parameters X R) with
  | left H => limiting_peak nm X (phase_limit_original R) (proj1 H)
      (proj1 (proj2 (proj2 (proj2 H)))) (proj2 (proj2 (proj2 (proj2 H))))
  | right _ => 0
  end.

Lemma parameter_peak_valid : forall nm X R HX HA Hell,
  valid_peak_parameters X R ->
  parameter_peak nm X R = limiting_peak nm X (phase_limit_original R) HX HA Hell.
Proof.
  intros nm X R HX HA Hell HV. unfold parameter_peak.
  destruct (excluded_middle_informative (valid_peak_parameters X R)) as [Hyes|Hno]; [|contradiction].
  apply limiting_peak_unique_proofs.
Qed.

Theorem parameter_peak_sequence_limit : forall nm X Y R S,
  (forall i, valid_peak_parameters (X i) (R i)) -> valid_peak_parameters Y S ->
  matrix_cv X Y -> matrix_cv R S -> Un_cv (fun i => parameter_peak nm (X i) (R i)) (parameter_peak nm Y S).
Proof.
  intros nm X Y R S HV Hlimit HXY HRS.
  assert (HX : forall i, det2 (X i) = 1) by (intro i; exact (proj1 (HV i))).
  assert (HRd : forall i, det2 (R i) = 1) by (intro i; exact (proj1 (proj2 (HV i)))).
  assert (HRo : forall i, orthogonal2 (R i)) by (intro i; exact (proj1 (proj2 (proj2 (HV i))))).
  assert (HA : forall i, det2 (phase_limit_original (R i)) = 1)
    by (intro i; exact (proj1 (proj2 (proj2 (proj2 (HV i)))))).
  assert (Hell : forall i, Rabs (trace2 (phase_limit_original (R i))) < 2)
    by (intro i; exact (proj2 (proj2 (proj2 (proj2 (HV i)))))).
  destruct Hlimit as [HY [HSd [HSo [HAl Helll]]]].
  assert (Hsame : (fun i => parameter_peak nm (X i) (R i)) =
    (fun i => limiting_peak nm (X i) (phase_limit_original (R i)) (HX i) (HA i) (Hell i))).
  { apply functional_extensionality; intro i; apply parameter_peak_valid,HV. }
  rewrite Hsame, (parameter_peak_valid nm Y S HY HAl Helll ltac:(unfold valid_peak_parameters; auto)).
  apply limiting_peaks_joint_sequence_limit; assumption.
Qed.

Theorem parameter_peak_joint_continuity : forall nm X R,
  valid_peak_parameters X R -> forall eps, 0 < eps ->
  exists delta, 0 < delta /\ forall Y S,
    valid_peak_parameters Y S ->
    opnorm (sub2 Y X) < delta -> opnorm (sub2 S R) < delta ->
    Rabs (parameter_peak nm Y S-parameter_peak nm X R) < eps.
Proof.
  intros nm X R HV eps He. apply NNPP; intro Hno.
  assert (Hchoose : forall i, exists p : mat2*mat2,
    valid_peak_parameters (fst p) (snd p) /\
    opnorm (sub2 (fst p) X) < (1/2)^i /\ opnorm (sub2 (snd p) R) < (1/2)^i /\
    eps <= Rabs (parameter_peak nm (fst p) (snd p)-parameter_peak nm X R)).
  { intro i. apply NNPP; intro Hnone. apply Hno. exists ((1/2)^i); split; [apply pow_lt; lra|].
    intros Y S HY HX HS.
    destruct (Rlt_dec (Rabs (parameter_peak nm Y S-parameter_peak nm X R)) eps) as [Hyes|Hbad]; auto.
    exfalso; apply Hnone; exists (Y,S); simpl; repeat first [assumption|split]; lra. }
  destruct (@choice nat (mat2*mat2)%type _ Hchoose) as [p Hp].
  assert (HXcv : matrix_cv (fun i => fst (p i)) X).
  { intros e Hpos. destruct (pow_lt_1_zero (1/2) ltac:(rewrite Rabs_right; lra) e Hpos) as [N HN].
    exists N; intros i Hi; specialize (HN i Hi).
    rewrite Rabs_right in HN by (apply Rle_ge,pow_le; lra).
    pose proof (proj1 (proj2 (Hp i))); lra. }
  assert (HRcv : matrix_cv (fun i => snd (p i)) R).
  { intros e Hpos. destruct (pow_lt_1_zero (1/2) ltac:(rewrite Rabs_right; lra) e Hpos) as [N HN].
    exists N; intros i Hi; specialize (HN i Hi).
    rewrite Rabs_right in HN by (apply Rle_ge,pow_le; lra).
    pose proof (proj1 (proj2 (proj2 (Hp i)))); lra. }
  pose proof (parameter_peak_sequence_limit nm (fun i => fst (p i)) X (fun i => snd (p i)) R
    (fun i => proj1 (Hp i)) HV HXcv HRcv) as Hcv.
  destruct (Hcv eps He) as [N HN]. specialize (HN N ltac:(lia)).
  pose proof (proj2 (proj2 (proj2 (Hp N)))) as Hbad.
  exact (Rlt_not_le _ _ HN Hbad).
Qed.

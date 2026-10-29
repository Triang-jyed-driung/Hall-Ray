From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import MatrixAlgebra ReturnIdentity FiberProducts EuclideanNorm MatrixLimits
  LatticeBasis PaperTarget NormGeometry DaniCorrespondence LatticeSystole
  SystoleContinuity SystoleCurves SymbolicCoding NormalizedFlow TwoSidedCoding LatticeReturns.
Open Scope R_scope.

Definition matrix3_cv (U : nat -> mat3) (L : mat3) :=
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> matrices_close3 eps L (U n).
Definition coordinate_cv3 (U : nat -> mat3) (L : mat3) :=
  Un_cv (fun n => b11 (U n)) (b11 L) /\ Un_cv (fun n => b12 (U n)) (b12 L) /\
  Un_cv (fun n => b13 (U n)) (b13 L) /\ Un_cv (fun n => b21 (U n)) (b21 L) /\
  Un_cv (fun n => b22 (U n)) (b22 L) /\ Un_cv (fun n => b23 (U n)) (b23 L) /\
  Un_cv (fun n => b31 (U n)) (b31 L) /\ Un_cv (fun n => b32 (U n)) (b32 L) /\
  Un_cv (fun n => b33 (U n)) (b33 L).

Lemma eventual_conjunction : forall (P Q : nat -> Prop),
  (exists N, forall n, (N <= n)%nat -> P n) ->
  (exists N, forall n, (N <= n)%nat -> Q n) ->
  exists N, forall n, (N <= n)%nat -> P n /\ Q n.
Proof.
  intros P Q [N HN] [M HM]. exists (Nat.max N M); intros n Hn; split; [apply HN|apply HM]; lia.
Qed.
Lemma scalar_cv_eventual_bound : forall u l eps,
  Un_cv u l -> 0 < eps -> exists N, forall n, (N <= n)%nat -> Rabs (u n-l) <= eps.
Proof.
  intros u l eps H He. destruct (H eps He) as [N HN]. exists N; intros n Hn.
  specialize (HN n Hn); unfold Rdist in HN; lra.
Qed.

Theorem matrix3_cv_coordinates : forall U L, matrix3_cv U L -> coordinate_cv3 U L.
Proof.
  intros U L H. repeat split; intros eps He;
    destruct (H (eps/2) ltac:(lra)) as [N HN]; exists N; intros n Hn;
    specialize (HN n Hn); unfold matrices_close3, entries_bounded3, matrix_difference3 in HN;
    simpl in HN; unfold Rdist; lra.
Qed.
Theorem coordinates_matrix3_cv : forall U L, coordinate_cv3 U L -> matrix3_cv U L.
Proof.
  intros U L (H11&H12&H13&H21&H22&H23&H31&H32&H33) eps He.
  unfold matrices_close3, entries_bounded3, matrix_difference3; simpl.
  repeat apply eventual_conjunction; apply scalar_cv_eventual_bound; assumption.
Qed.

Ltac scalar_cv_algebra :=
  repeat first [assumption|apply real_constant_cv|apply CV_plus|apply CV_minus|apply CV_mult|apply CV_opp].

Theorem matrix3_cv_product : forall U V L M,
  matrix3_cv U L -> matrix3_cv V M -> matrix3_cv (fun n => mul3 (U n) (V n)) (mul3 L M).
Proof.
  intros U V L M HU HV. apply matrix3_cv_coordinates in HU,HV.
  destruct HU as (H11&H12&H13&H21&H22&H23&H31&H32&H33).
  destruct HV as (J11&J12&J13&J21&J22&J23&J31&J32&J33).
  apply coordinates_matrix3_cv. unfold coordinate_cv3, mul3; simpl.
  repeat split; scalar_cv_algebra.
Qed.
Theorem matrix3_cv_scale : forall c d U L,
  Un_cv c d -> matrix3_cv U L -> matrix3_cv (fun n => scale3 (c n) (U n)) (scale3 d L).
Proof.
  intros c d U L Hc HU. apply matrix3_cv_coordinates in HU.
  destruct HU as (H11&H12&H13&H21&H22&H23&H31&H32&H33).
  apply coordinates_matrix3_cv. unfold coordinate_cv3, scale3; simpl.
  repeat split; scalar_cv_algebra.
Qed.
Theorem matrix_cv_product : forall U V L M,
  matrix_cv U L -> matrix_cv V M -> matrix_cv (fun n => mul2 (U n) (V n)) (mul2 L M).
Proof.
  intros U V L M HU HV. apply matrix_cv_coordinates in HU,HV.
  destruct HU as (H11&H12&H21&H22); destruct HV as (J11&J12&J21&J22).
  apply coordinates_matrix_cv. unfold coordinate_cv, mul2; simpl.
  repeat split; scalar_cv_algebra.
Qed.
Theorem matrix_cv_adjugate : forall U L,
  matrix_cv U L -> matrix_cv (fun n => adj2 (U n)) (adj2 L).
Proof.
  intros U L HU. apply matrix_cv_coordinates in HU. destruct HU as (H11&H12&H21&H22).
  apply coordinates_matrix_cv. unfold coordinate_cv, adj2; simpl.
  repeat split; scalar_cv_algebra.
Qed.

Theorem matrix3_curve_sequence_limit : forall f u l,
  matrix_curve_continuous f -> Un_cv u l -> matrix3_cv (fun n => f (u n)) (f l).
Proof.
  intros f u l Hf Hu eps He. destruct (Hf l eps He) as [d [Hd Hb]].
  destruct (Hu d Hd) as [N HN]. exists N; intros n Hn; apply Hb.
  specialize (HN n Hn); exact HN.
Qed.

Theorem systole_sequence_limit : forall nm U L,
  det3 L = 1 -> matrix3_cv U L -> Un_cv (fun n => systole nm (U n)) (systole nm L).
Proof.
  intros nm U L HL HU eps He.
  destruct (systole_continuous nm L HL eps He) as [d [Hd Hb]].
  destruct (HU d Hd) as [N HN]. exists N; intros n Hn. apply Hb, HN; exact Hn.
Qed.
Theorem cusp_height_sequence_limit : forall nm U L,
  det3 L = 1 -> matrix3_cv U L -> Un_cv (fun n => cusp_height nm (U n)) (cusp_height nm L).
Proof.
  intros nm U L HL HU. unfold cusp_height. apply continuity_seq.
  - apply continuity_pt_inv; [reg|pose proof (systole_positive nm L HL); lra].
  - apply systole_sequence_limit; assumption.
Qed.

Lemma frame_normalizer_continuous : forall x, 0 < x -> continuity_pt frame_normalizer x.
Proof.
  intros x Hx. unfold frame_normalizer, positive_cube_root. reg.
  - apply derivable_continuous_pt. exists (/x). apply derivable_pt_lim_ln; exact Hx.
  - pose proof (exp_pos (ln x * /3)); lra.
Qed.

Theorem normalized_frame_sequence_limit : forall u v E a b F,
  point_converges u a -> point_converges v b -> matrix_cv E F ->
  0 < chart_weight (fst a) (snd a) (fst b) (snd b) ->
  matrix3_cv (fun n => normalized_frame (fst (u n)) (snd (u n)) (fst (v n)) (snd (v n)) (E n))
    (normalized_frame (fst a) (snd a) (fst b) (snd b) F).
Proof.
  intros u v E a b F [Hu1 Hu2] [Hv1 Hv2] HE Hweight.
  assert (Hw : Un_cv (fun n => chart_weight (fst (u n)) (snd (u n)) (fst (v n)) (snd (v n)))
    (chart_weight (fst a) (snd a) (fst b) (snd b))).
  { unfold chart_weight; scalar_cv_algebra. }
  assert (Hc : Un_cv (fun n => frame_normalizer (chart_weight (fst (u n)) (snd (u n)) (fst (v n)) (snd (v n))))
    (frame_normalizer (chart_weight (fst a) (snd a) (fst b) (snd b)))).
  { apply continuity_seq; [apply frame_normalizer_continuous; exact Hweight|exact Hw]. }
  apply matrix_cv_coordinates in HE. destruct HE as (H11&H12&H21&H22).
  unfold normalized_frame, chart. apply matrix3_cv_scale; [exact Hc|].
  apply coordinates_matrix3_cv. unfold coordinate_cv3, mul3, block3, raw_chart; simpl.
  repeat split; scalar_cv_algebra.
Qed.

Theorem orbit_frame_sequence_limit : forall z w E F,
  point_converges (fun n => u_code (z n)) (u_code w) ->
  point_converges (fun n => v_code (z n)) (v_code w) -> matrix_cv E F ->
  matrix3_cv (fun n => orbit_frame (z n) (E n)) (orbit_frame w F).
Proof.
  intros z w E F Hu Hv HE. apply normalized_frame_sequence_limit; try assumption.
  pose proof (chart_weight_bounds _ _ _ _ (u_code_inside w) (v_code_inside w)); lra.
Qed.

Theorem flowing_orbit_frame_sequence_limit : forall z w E F t r,
  point_converges (fun n => u_code (z n)) (u_code w) ->
  point_converges (fun n => v_code (z n)) (v_code w) -> matrix_cv E F -> Un_cv t r ->
  matrix3_cv (fun n => mul3 (diagonal_flow (t n)) (orbit_frame (z n) (E n)))
    (mul3 (diagonal_flow r) (orbit_frame w F)).
Proof.
  intros z w E F t r Hu Hv HE Ht. apply matrix3_cv_product.
  - apply matrix3_curve_sequence_limit; [|exact Ht].
    apply matrix_curve_from_components; unfold diagonal_flow, flow_scale; simpl; intro x; reg;
      pose proof (exp_pos x); nra.
  - apply orbit_frame_sequence_limit; assumption.
Qed.

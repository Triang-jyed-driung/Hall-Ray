From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices
  LatticeBasis PaperTarget NormGeometry DaniCorrespondence LatticeSystole SystoleContinuity.
Open Scope R_scope.

Definition matrix_curve_continuous (f : R -> mat3) :=
  forall t eps, 0 < eps -> exists delta, 0 < delta /\ forall u,
    Rabs (u-t) < delta -> matrices_close3 eps (f t) (f u).

Lemma scalar_continuity_estimate : forall f t eps,
  continuity_pt f t -> 0 < eps -> exists delta, 0 < delta /\ forall u,
    Rabs (u-t) < delta -> Rabs (f u-f t) <= eps.
Proof.
  intros f t eps Hc He.
  unfold continuity_pt, continue_in, limit1_in, limit_in in Hc; simpl in Hc.
  destruct (Hc eps He) as [d [Hd Hb]]. exists d; split; [exact Hd|].
  intros u Hu. destruct (Req_dec t u) as [Hsame|Hdiff].
  - subst u. replace (f t-f t) with 0 by ring. rewrite Rabs_R0; lra.
  - apply Rlt_le, Hb. repeat split; auto.
Qed.

Lemma epsilon_delta_conjunction : forall t (P Q : R -> Prop),
  (exists d, 0 < d /\ forall u, Rabs (u-t) < d -> P u) ->
  (exists d, 0 < d /\ forall u, Rabs (u-t) < d -> Q u) ->
  exists d, 0 < d /\ forall u, Rabs (u-t) < d -> P u /\ Q u.
Proof.
  intros t P Q [d [Hd HP]] [e [He HQ]]. exists (Rmin d e); split.
  - apply Rmin_pos; assumption.
  - intros u Hu. split.
    + apply HP. pose proof (Rmin_l d e); lra.
    + apply HQ. pose proof (Rmin_r d e); lra.
Qed.

Theorem matrix_curve_from_components : forall f,
  continuity (fun t => b11 (f t)) -> continuity (fun t => b12 (f t)) ->
  continuity (fun t => b13 (f t)) -> continuity (fun t => b21 (f t)) ->
  continuity (fun t => b22 (f t)) -> continuity (fun t => b23 (f t)) ->
  continuity (fun t => b31 (f t)) -> continuity (fun t => b32 (f t)) ->
  continuity (fun t => b33 (f t)) -> matrix_curve_continuous f.
Proof.
  intros f H11 H12 H13 H21 H22 H23 H31 H32 H33 t eps He.
  unfold matrices_close3, entries_bounded3, matrix_difference3; simpl.
  repeat apply epsilon_delta_conjunction;
    apply scalar_continuity_estimate; auto.
Qed.

Theorem systole_curve_continuous : forall nm f,
  matrix_curve_continuous f -> (forall t, det3 (f t) = 1) ->
  continuity (fun t => systole nm (f t)).
Proof.
  intros nm f Hf Hdet t.
  unfold continuity_pt, continue_in, limit1_in, limit_in; simpl.
  intros eps He. destruct (systole_continuous nm (f t) (Hdet t) eps He) as [d [Hd Hb]].
  destruct (Hf t d Hd) as [e [Heps Hclose]].
  exists e; split; [exact Heps|]. intros u [_ Hu]. apply Hb, Hclose; exact Hu.
Qed.

Theorem compact_curve_systole_bounds : forall nm f a b,
  a <= b -> matrix_curve_continuous f -> (forall t, det3 (f t) = 1) ->
  exists m M, 0 < m /\ forall t, a <= t <= b ->
    m <= systole nm (f t) <= M.
Proof.
  intros nm f a b Hab Hf Hdet.
  pose proof (systole_curve_continuous nm f Hf Hdet) as Hc.
  destruct (continuity_ab_min (fun t => systole nm (f t)) a b Hab ltac:(auto))
    as [u [Hu Huint]].
  destruct (continuity_ab_maj (fun t => systole nm (f t)) a b Hab ltac:(auto))
    as [v [Hv Hvint]].
  exists (systole nm (f u)), (systole nm (f v)). split.
  - apply systole_positive, Hdet.
  - intros t Ht. split; [apply Hu|apply Hv]; exact Ht.
Qed.

Definition cusp_height nm A := /systole nm A.

Theorem cusp_height_curve_continuous : forall nm f,
  matrix_curve_continuous f -> (forall t, det3 (f t) = 1) ->
  continuity (fun t => cusp_height nm (f t)).
Proof.
  intros nm f Hf Hdet t. unfold cusp_height. apply continuity_pt_inv.
  - apply systole_curve_continuous; assumption.
  - pose proof (systole_positive nm (f t) (Hdet t)); lra.
Qed.

Theorem compact_curve_height_maximum : forall nm f a b,
  a <= b -> matrix_curve_continuous f -> (forall t, det3 (f t) = 1) ->
  exists t0, a <= t0 <= b /\ forall t, a <= t <= b ->
    cusp_height nm (f t) <= cusp_height nm (f t0).
Proof.
  intros nm f a b Hab Hf Hdet.
  pose proof (cusp_height_curve_continuous nm f Hf Hdet) as Hc.
  destruct (continuity_ab_maj (fun t => cusp_height nm (f t)) a b Hab ltac:(auto))
    as [t0 [Ht Htin]]. exists t0; auto.
Qed.

Definition scaled_flow_curve A t := mul3 (flow_scale (exp t)) A.

Theorem scaled_flow_curve_continuous : forall A, matrix_curve_continuous (scaled_flow_curve A).
Proof.
  intro A. apply matrix_curve_from_components;
    unfold scaled_flow_curve, mul3, flow_scale; simpl; intro t; reg;
    pose proof (exp_pos t); nra.
Qed.

Lemma flow_scale_determinant : forall r, r <> 0 -> det3 (flow_scale r) = 1.
Proof. intros r Hr. unfold det3, flow_scale; simpl; field; exact Hr. Qed.

Theorem flow_systole_continuous : forall nm A,
  det3 A = 1 -> continuity (fun t => systole nm (scaled_flow_curve A t)).
Proof.
  intros nm A HA. apply systole_curve_continuous.
  - apply scaled_flow_curve_continuous.
  - intro t. unfold scaled_flow_curve. rewrite mul3_determinant, HA.
    rewrite flow_scale_determinant; [ring|pose proof (exp_pos t); lra].
Qed.

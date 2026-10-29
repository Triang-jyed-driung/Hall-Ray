From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra ReturnIdentity LatticeBasis
  PaperTarget DaniCorrespondence LatticeSystole.
Open Scope R_scope.

Definition approximation_systole nm x r :=
  systole nm (mul3 (flow_scale r) (hx (fst x) (snd x))).

Definition has_scale_systole_constant nm x rho : Prop :=
  (forall eps, 0 < eps < rho -> exists R0, 0 < R0 /\
    forall r, R0 <= r -> (rho-eps)^2 <= (approximation_systole nm x r)^3) /\
  (forall eps, 0 < eps -> forall R0, exists r,
    0 < r /\ R0 <= r /\ (approximation_systole nm x r)^3 <= (rho+eps)^2).

Theorem dani_vector_systole_equivalence : forall nm x rho,
  0 < rho -> (has_dani_constant nm x rho <-> has_scale_systole_constant nm x rho).
Proof.
  intros nm x rho Hrho. split.
  - intros [Hlower Hupper]. split.
    + intros eps He. destruct (Hlower eps He) as [R0 [HR Hb]].
      exists R0; split; [exact HR|]. intros r Hr.
      apply systole_cube_greatest_lower_bound. intros z Hz.
      destruct (signed_lattice_vector_representation nm
        (mul3 (flow_scale r) (hx (fst x) (snd x))) z Hz)
        as [q [p1 [p2 [Hnon Hlen]]]].
      rewrite Hlen. apply (Hb r q p1 p2 Hr Hnon).
    + intros eps He R0.
      destruct (Hupper eps He R0) as [r [q [p1 [p2 [Hr [Hlate [Hnon Hb]]]]]]].
      exists r; split; [exact Hr|]. split; [exact Hlate|].
      eapply Rle_trans; [|exact Hb]. apply systole_cube_lower_bound.
      rewrite approximation_lattice_vector_independent.
      apply approximation_index_nonzero_iff; exact Hnon.
  - intros [Hlower Hupper]. split.
    + intros eps He. destruct (Hlower eps He) as [R0 [HR Hb]].
      exists R0; split; [exact HR|]. intros r q p1 p2 Hr Hnon.
      eapply Rle_trans; [apply Hb; exact Hr|]. apply systole_cube_lower_bound.
      rewrite approximation_lattice_vector_independent.
      apply approximation_index_nonzero_iff; exact Hnon.
    + intros eps He R0.
      destruct (Hupper (eps/2) ltac:(lra) R0) as [r [Hr [Hlate Hb]]].
      assert (Hmargin : 0 < (rho+eps)^2-(rho+eps/2)^2) by nra.
      destruct (systole_cube_near nm
        (mul3 (flow_scale r) (hx (fst x) (snd x)))
        ((rho+eps)^2-(rho+eps/2)^2) Hmargin) as [z [Hz Hsmall]].
      destruct (signed_lattice_vector_representation nm
        (mul3 (flow_scale r) (hx (fst x) (snd x))) z Hz)
        as [q [p1 [p2 [Hnon Hlen]]]].
      exists r,q,p1,p2. split; [exact Hr|]. split; [exact Hlate|].
      split; [exact Hnon|].
      unfold approximation_systole in Hb. rewrite Hlen in Hsmall.
      unfold approximation_flow_length. rewrite approximation_lattice_vector_independent. lra.
Qed.

Theorem dani_correspondence_scale_systole : forall nm x rho,
  ~ rational_vector x -> 0 < rho ->
  (has_approximation_constant nm x rho <-> has_scale_systole_constant nm x rho).
Proof.
  intros nm x rho Hi Hr. rewrite (dani_correspondence_vector_form nm x rho Hi Hr).
  apply dani_vector_systole_equivalence; exact Hr.
Qed.

Definition flow_systole nm x t := approximation_systole nm x (exp t).

(* Epsilon form of liminf_{t -> infinity} lambda(g_t h_x Z^3)^3 = rho^2. *)
Definition has_flow_systole_constant nm x rho : Prop :=
  (forall eps, 0 < eps < rho -> exists T,
    forall t, T <= t -> (rho-eps)^2 <= (flow_systole nm x t)^3) /\
  (forall eps, 0 < eps -> forall T, exists t,
    T <= t /\ (flow_systole nm x t)^3 <= (rho+eps)^2).

Lemma exponential_nondecreasing : forall a b, a <= b -> exp a <= exp b.
Proof.
  intros a b Hab. destruct (Rle_lt_or_eq_dec a b Hab) as [Hlt|Heq].
  - apply Rlt_le, exp_increasing; exact Hlt.
  - subst b; lra.
Qed.

Lemma logarithmic_scale_bound : forall r T,
  0 < r -> exp T <= r -> T <= ln r.
Proof.
  intros r T Hr Hb. destruct (Rle_dec T (ln r)) as [Hyes|Hno]; auto.
  assert (H : exp (ln r) < exp T) by (apply exp_increasing; lra).
  rewrite exp_ln in H by exact Hr. lra.
Qed.

Theorem scale_time_systole_equivalence : forall nm x rho,
  has_scale_systole_constant nm x rho <-> has_flow_systole_constant nm x rho.
Proof.
  intros nm x rho. split.
  - intros [Hlower Hupper]. split.
    + intros eps He. destruct (Hlower eps He) as [R0 [HR Hb]].
      exists (ln R0). intros t Ht. unfold flow_systole. apply Hb.
      pose proof (exponential_nondecreasing (ln R0) t Ht) as Hexp.
      rewrite exp_ln in Hexp by exact HR. exact Hexp.
    + intros eps He T. destruct (Hupper eps He (exp T)) as [r [Hr [Hlate Hb]]].
      exists (ln r). split; [apply logarithmic_scale_bound; assumption|].
      unfold flow_systole. rewrite exp_ln by exact Hr. exact Hb.
  - intros [Hlower Hupper]. split.
    + intros eps He. destruct (Hlower eps He) as [T Hb].
      exists (exp T); split; [apply exp_pos|]. intros r Hr.
      assert (Hrpos : 0 < r) by (pose proof (exp_pos T); lra).
      specialize (Hb (ln r) (logarithmic_scale_bound r T Hrpos Hr)).
      unfold flow_systole in Hb. rewrite exp_ln in Hb by exact Hrpos. exact Hb.
    + intros eps He R0. destruct (Hupper eps He R0) as [t [Ht Hb]].
      exists (exp t). split; [apply exp_pos|]. split.
      * pose proof (exp_ineq1_le t); lra.
      * exact Hb.
Qed.

Theorem dani_correspondence : forall nm x rho,
  ~ rational_vector x -> 0 < rho ->
  (has_approximation_constant nm x rho <-> has_flow_systole_constant nm x rho).
Proof.
  intros nm x rho Hi Hr.
  rewrite (dani_correspondence_scale_systole nm x rho Hi Hr).
  apply scale_time_systole_equivalence.
Qed.

From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import ScalarEstimates.
Open Scope R_scope.

(* This is a characterization of a finite limsup at positive infinity.
   Both the eventual upper bound and arbitrarily late near-attainment
   are required. It is not a definition chosen to hide the conclusion. *)
Definition has_limsup (f : R -> R) (A : R) : Prop :=
  (forall eps, 0 < eps -> exists T, forall t, T <= t -> f t < A+eps) /\
  (forall eps T, 0 < eps -> exists t, T <= t /\ A-eps < f t).

Definition tends_to_zero (e : nat -> R) : Prop :=
  forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat -> Rabs (e n) < eps.

Section BlockIntervals.
Variable s : nat -> R.
Hypothesis increasing : forall n, s n < s (S n).
Hypothesis cofinal : forall T, exists n, T < s n.

Lemma starts_monotone : forall n m, (n <= m)%nat -> s n <= s m.
Proof.
  intros n m H. induction H; [lra|]. specialize (increasing m). lra.
Qed.

Lemma finite_cover : forall m t,
  s O <= t -> t < s m -> exists n, (n < m)%nat /\ s n <= t < s (S n).
Proof.
  induction m as [|m IH]; intros t H0 Hm; [lra|].
  destruct (Rle_dec (s m) t) as [Hmt|Hmt].
  - exists m. split; [lia|lra].
  - destruct (IH t H0 ltac:(lra)) as [n [Hn Ht]]. exists n. split; [lia|exact Ht].
Qed.

Lemma tail_cover : forall N t,
  s N <= t -> exists n, (N <= n)%nat /\ s n <= t < s (S n).
Proof.
  intros N t HNt. destruct (cofinal t) as [m Hm].
  pose proof (starts_monotone O N (Nat.le_0_l N)) as H0N.
  destruct (finite_cover m t ltac:(lra) Hm) as [n [Hnm Ht]].
  exists n. split; [|exact Ht].
  destruct (le_dec N n); auto.
  assert (HS : (S n <= N)%nat) by lia.
  pose proof (starts_monotone (S n) N HS). lra.
Qed.

(* This is precisely the inference at the end of Section 6, Step 3.
   It proves the inference, not the unformalized construction of the blocks. *)
Theorem block_maxima_limsup : forall f A e,
  tends_to_zero e ->
  (forall n t, s n <= t <= s (S n) -> f t <= A+e n) ->
  (forall n, exists t, s n <= t <= s (S n) /\ A-e n <= f t) ->
  has_limsup f A.
Proof.
  intros f A e He Hupper Hpeak. split.
  - intros eps Heps. destruct (He eps Heps) as [N HN].
    exists (s N). intros t Ht.
    destruct (tail_cover N t Ht) as [n [Hn Hnt]].
    specialize (Hupper n t ltac:(lra)). specialize (HN n Hn).
    pose proof (Rle_abs (e n)). lra.
  - intros eps T Heps. destruct (He eps Heps) as [N HN].
    destruct (cofinal T) as [m Hm].
    set (n := Nat.max N m).
    destruct (Hpeak n) as [t [Ht Hval]]. exists t. split.
    + pose proof (starts_monotone m n (Nat.le_max_r N m)). lra.
    + specialize (HN n (Nat.le_max_l N m)). pose proof (Rle_abs (e n)). lra.
Qed.

Corollary summable_block_errors_limsup : forall f A,
  (forall n t, s n <= t <= s (S n) -> f t <= A+3*(1/2)^n) ->
  (forall n, exists t, s n <= t <= s (S n) /\ A-3*(1/2)^n <= f t) ->
  has_limsup f A.
Proof.
  intros f A Hu Hp. eapply block_maxima_limsup; [|exact Hu|exact Hp].
  intros eps Heps. destruct (geometric_error_vanishes eps Heps) as [N HN].
  exists N. intros n Hn. rewrite Rabs_right.
  - apply HN; exact Hn.
  - apply Rle_ge, Rmult_le_pos; [lra|apply pow_le; lra].
Qed.
End BlockIntervals.

(* Section 6, Step 4: vanishing perturbations and fixed time shifts preserve
   a finite limsup. The geometric task is to prove this perturbation condition
   for the two lattice orbits, rather than assume the desired limsup. *)
Definition asymptotic_difference (f g : R -> R) : Prop :=
  forall eps, 0 < eps -> exists T, forall t, T <= t -> Rabs (f t-g t) < eps.

Theorem limsup_stable_under_vanishing_error : forall f g A,
  has_limsup f A -> asymptotic_difference f g -> has_limsup g A.
Proof.
  intros f g A [Hu Hp] Hd. split.
  - intros eps Heps.
    destruct (Hu (eps/2) ltac:(lra)) as [T1 H1].
    destruct (Hd (eps/2) ltac:(lra)) as [T2 H2].
    exists (Rmax T1 T2). intros t Ht.
    assert (HT1 : T1 <= t) by (pose proof (Rmax_l T1 T2); lra).
    assert (HT2 : T2 <= t) by (pose proof (Rmax_r T1 T2); lra).
    specialize (H1 t HT1). specialize (H2 t HT2).
    apply Rabs_def2 in H2. lra.
  - intros eps T Heps.
    destruct (Hd (eps/2) ltac:(lra)) as [T2 H2].
    destruct (Hp (eps/2) (Rmax T T2) ltac:(lra)) as [t [Ht Hft]].
    exists t. pose proof (Rmax_l T T2). pose proof (Rmax_r T T2).
    specialize (H2 t ltac:(lra)). apply Rabs_def2 in H2. split; lra.
Qed.

Theorem limsup_time_shift : forall f A c,
  has_limsup f A -> has_limsup (fun t => f (t+c)) A.
Proof.
  intros f A c [Hu Hp]. split.
  - intros eps Heps. destruct (Hu eps Heps) as [T HT].
    exists (T-c). intros t Ht. apply HT; lra.
  - intros eps T Heps. destruct (Hp eps (T+c) Heps) as [t [Ht Hv]].
    exists (t-c). split; [lra|]. replace (t-c+c) with t by ring. exact Hv.
Qed.

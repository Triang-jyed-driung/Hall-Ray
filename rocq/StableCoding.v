From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import ReturnBranches ReturnIdentity StableBranches SymbolicCoding.
Open Scope R_scope.

Definition stable_inside (p : point) := in_V (fst p) (snd p).
Definition psi_branch (s : bool) (p : point) : point :=
  if s then (psi_a1 (fst p) (snd p), psi_a2 (fst p) (snd p))
       else (psi_b1 (fst p) (snd p), psi_b2 (fst p) (snd p)).
Fixpoint stable_prefix (n : nat) (w : future) (p : point) : point :=
  match n with O => p | S k => psi_branch (w O) (stable_prefix k (shift w) p) end.
Definition stable_approx (w : future) (n : nat) := stable_prefix n w (0,0).

Lemma stable_origin_inside : stable_inside (0,0).
Proof. unfold stable_inside, in_V; simpl; lra. Qed.
Lemma psi_branch_inside : forall s p, stable_inside p -> stable_inside (psi_branch s p).
Proof.
  intros [] [v w]; unfold stable_inside, psi_branch; simpl;
    auto using psi_a_invariant, psi_b_invariant.
Qed.
Lemma stable_prefix_inside : forall n w p,
  stable_inside p -> stable_inside (stable_prefix n w p).
Proof. induction n; intros w p Hp; simpl; auto using psi_branch_inside. Qed.
Lemma stable_approx_inside : forall w n, stable_inside (stable_approx w n).
Proof. intros; apply stable_prefix_inside, stable_origin_inside. Qed.
Lemma psi_branch_contraction : forall s p q e,
  stable_inside p -> stable_inside q -> 0 <= e -> close e p q ->
  close (e/900) (psi_branch s p) (psi_branch s q).
Proof.
  intros [] [v w] [v' w'] e Hp Hq He [Hv Hw]; unfold close, psi_branch; simpl;
    [apply psi_a_contraction|apply psi_b_contraction]; assumption.
Qed.
Lemma stable_rectangle_diameter : forall p q,
  stable_inside p -> stable_inside q -> close (2/5) p q.
Proof.
  intros [v w] [v' w']; unfold stable_inside, in_V, close; simpl.
  intros; split; apply Rabs_le; lra.
Qed.

Lemma stable_prefix_contraction : forall n w p q e,
  stable_inside p -> stable_inside q -> 0 <= e -> close e p q ->
  close (e*(1/900)^n) (stable_prefix n w p) (stable_prefix n w q).
Proof.
  induction n; intros w p q e Hp Hq He Hclose; simpl.
  - replace (e*1) with e by ring; exact Hclose.
  - replace (e*((1/900)*(1/900)^n)) with ((e*(1/900)^n)/900) by field.
    apply psi_branch_contraction; auto using stable_prefix_inside.
    apply Rmult_le_pos; auto; apply pow_le; lra.
Qed.
Lemma stable_prefix_split : forall n k w p,
  stable_prefix (n+k) w p = stable_prefix n w (stable_prefix k (shift_by n w) p).
Proof.
  induction n; intros k w p; simpl; [reflexivity|]. rewrite IHn; reflexivity.
Qed.
Lemma stable_approx_tail_bound : forall w n m,
  (n <= m)%nat -> close ((2/5)*(1/900)^n) (stable_approx w n) (stable_approx w m).
Proof.
  intros w n m Hnm. replace m with (n+(m-n))%nat by lia.
  unfold stable_approx; rewrite stable_prefix_split.
  apply stable_prefix_contraction; auto using stable_origin_inside, stable_prefix_inside.
  - lra.
  - apply stable_rectangle_diameter; auto using stable_origin_inside, stable_prefix_inside.
Qed.

Lemma stable_coding_cauchy : forall w,
  Cauchy_crit (fun n => fst (stable_approx w n)) /\
  Cauchy_crit (fun n => snd (stable_approx w n)).
Proof.
  intro w.
  assert (Hcommon : forall eps, 0 < eps -> exists N, forall n m,
    (N <= n)%nat -> (N <= m)%nat -> close eps (stable_approx w n) (stable_approx w m)).
  { intros eps He.
    destruct (pow_lt_1_zero (1/900) ltac:(rewrite Rabs_right; lra) eps He) as [N HN].
    exists N. intros n m Hn Hm.
    destruct (stable_approx_tail_bound w N n Hn) as [Hnx Hny].
    destruct (stable_approx_tail_bound w N m Hm) as [Hmx Hmy].
    specialize (HN N (Nat.le_refl N)).
    rewrite Rabs_right in HN by (apply Rle_ge, pow_le; lra).
    rewrite Rabs_minus_sym in Hnx, Hny, Hmx, Hmy.
    pose proof (abs_triangle_difference (fst (stable_approx w n)) (fst (stable_approx w m)) (fst (stable_approx w N))).
    pose proof (abs_triangle_difference (snd (stable_approx w n)) (snd (stable_approx w m)) (snd (stable_approx w N))).
    split; simpl; lra. }
  split; intros eps He; destruct (Hcommon (eps/2) ltac:(lra)) as [N HN];
    exists N; intros n m Hn Hm; specialize (HN n m Hn Hm);
    unfold close in HN; unfold Rdist; lra.
Qed.

Definition stable_coded_x (w : future) :=
  proj1_sig (R_complete (fun n => fst (stable_approx w n)) (proj1 (stable_coding_cauchy w))).
Definition stable_coded_y (w : future) :=
  proj1_sig (R_complete (fun n => snd (stable_approx w n)) (proj2 (stable_coding_cauchy w))).
Definition stable_coded (w : future) : point := (stable_coded_x w, stable_coded_y w).

Theorem stable_coded_converges : forall w,
  point_converges (stable_approx w) (stable_coded w).
Proof.
  intro w. split;
    [exact (proj2_sig (R_complete _ (proj1 (stable_coding_cauchy w))))
    |exact (proj2_sig (R_complete _ (proj2 (stable_coding_cauchy w))))].
Qed.
Theorem stable_coded_inside : forall w, stable_inside (stable_coded w).
Proof.
  intro w. destruct (stable_coded_converges w) as [Hx Hy].
  unfold stable_inside, in_V. split; split.
  - apply (@Rle_cv_lim (fun _ => -1/50) (fun n => fst (stable_approx w n)));
      auto using constant_converges.
    intro n; pose proof (stable_approx_inside w n); unfold stable_inside, in_V in *; lra.
  - apply (@Rle_cv_lim (fun n => fst (stable_approx w n)) (fun _ => 1/50));
      auto using constant_converges.
    intro n; pose proof (stable_approx_inside w n); unfold stable_inside, in_V in *; lra.
  - apply (@Rle_cv_lim (fun _ => -1/5) (fun n => snd (stable_approx w n)));
      auto using constant_converges.
    intro n; pose proof (stable_approx_inside w n); unfold stable_inside, in_V in *; lra.
  - apply (@Rle_cv_lim (fun n => snd (stable_approx w n)) (fun _ => 1/5));
      auto using constant_converges.
    intro n; pose proof (stable_approx_inside w n); unfold stable_inside, in_V in *; lra.
Qed.

Lemma psi_branch_preserves_limits : forall s p q,
  (forall n, stable_inside (p n)) -> stable_inside q -> point_converges p q ->
  point_converges (fun n => psi_branch s (p n)) (psi_branch s q).
Proof.
  intros s p q Hi Hq [Hx Hy].
  assert (Hcommon : forall eps, 0 < eps -> exists N, forall n, (N <= n)%nat ->
    close (eps/900) (psi_branch s (p n)) (psi_branch s q)).
  { intros eps He. destruct (Hx eps He) as [Nx HNx].
    destruct (Hy eps He) as [Ny HNy]. exists (Nat.max Nx Ny).
    intros n Hn. apply psi_branch_contraction; auto; [lra|].
    specialize (HNx n ltac:(lia)). specialize (HNy n ltac:(lia)). unfold Rdist in *; split; lra. }
  split; intros eps He; destruct (Hcommon eps He) as [N HN]; exists N;
    intros n Hn; specialize (HN n Hn); unfold close in HN; unfold Rdist; lra.
Qed.

Theorem stable_coded_recursion : forall w,
  stable_coded w = psi_branch (w O) (stable_coded (shift w)).
Proof.
  intro w.
  pose proof (psi_branch_preserves_limits (w O) (stable_approx (shift w)) (stable_coded (shift w))
    (stable_approx_inside (shift w)) (stable_coded_inside (shift w)) (stable_coded_converges (shift w)))
    as [Hbx Hby].
  destruct (stable_coded_converges w) as [Hx Hy].
  assert (Hsx := successor_converges _ _ Hx). assert (Hsy := successor_converges _ _ Hy).
  change (Un_cv (fun n => fst (stable_approx w (S n)))
    (fst (psi_branch (w O) (stable_coded (shift w))))) in Hbx.
  change (Un_cv (fun n => snd (stable_approx w (S n)))
    (snd (psi_branch (w O) (stable_coded (shift w))))) in Hby.
  destruct (stable_coded w), (psi_branch (w O) (stable_coded (shift w))); simpl in *.
  f_equal; [exact (@UL_sequence _ _ _ Hsx Hbx)|exact (@UL_sequence _ _ _ Hsy Hby)].
Qed.

Lemma stable_prefix_agreement : forall n w z p,
  (forall k, (k < n)%nat -> w k = z k) -> stable_prefix n w p = stable_prefix n z p.
Proof.
  induction n; intros w z p H; simpl; [reflexivity|]. rewrite (H O ltac:(lia)).
  f_equal; apply IHn; intros k Hk; apply H; lia.
Qed.
Lemma stable_coded_prefix : forall n w,
  stable_coded w = stable_prefix n w (stable_coded (shift_by n w)).
Proof.
  induction n; intro w; simpl; [reflexivity|].
  rewrite (stable_coded_recursion w), (IHn (shift w)); reflexivity.
Qed.
Theorem common_past_estimate : forall n w z,
  (forall k, (k < n)%nat -> w k = z k) ->
  close ((2/5)*(1/900)^n) (stable_coded w) (stable_coded z).
Proof.
  intros n w z H. rewrite (stable_coded_prefix n w), (stable_coded_prefix n z).
  rewrite <- (stable_prefix_agreement n w z (stable_coded (shift_by n z)) H).
  apply stable_prefix_contraction; auto using stable_coded_inside; [lra|].
  apply stable_rectangle_diameter; apply stable_coded_inside.
Qed.
Theorem stable_coded_extensional : forall w z,
  (forall n, w n = z n) -> stable_coded w = stable_coded z.
Proof.
  intros w z H.
  assert (Happrox : forall n, stable_approx w n = stable_approx z n).
  { intro n; apply stable_prefix_agreement; intros; apply H. }
  destruct (stable_coded_converges w) as [Hwx Hwy].
  destruct (stable_coded_converges z) as [Hzx Hzy].
  assert (Hwx' : Un_cv (fun n => fst (stable_approx z n)) (fst (stable_coded w))).
  { intros eps He; destruct (Hwx eps He) as [N HN]; exists N; intros n Hn.
    rewrite <- Happrox; apply HN; exact Hn. }
  assert (Hwy' : Un_cv (fun n => snd (stable_approx z n)) (snd (stable_coded w))).
  { intros eps He; destruct (Hwy eps He) as [N HN]; exists N; intros n Hn.
    rewrite <- Happrox; apply HN; exact Hn. }
  destruct (stable_coded w), (stable_coded z); simpl in *; f_equal;
    [exact (@UL_sequence _ _ _ Hwx' Hzx)|exact (@UL_sequence _ _ _ Hwy' Hzy)].
Qed.

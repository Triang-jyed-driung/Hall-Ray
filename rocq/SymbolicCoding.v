From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import ReturnBranches Contraction.
Open Scope R_scope.

Definition point := (R*R)%type.
Definition inside (p : point) := in_U (fst p) (snd p).
Definition close (e : R) (p q : point) :=
  Rabs (fst p-fst q) <= e /\ Rabs (snd p-snd q) <= e.
Definition branch (s : bool) (p : point) : point :=
  if s then (phi_a1 (fst p) (snd p), phi_a2 (fst p) (snd p))
       else (phi_b1 (fst p) (snd p), phi_b2 (fst p) (snd p)).
Definition future := nat -> bool.
Definition shift (w : future) : future := fun n => w (S n).
Definition shift_by (k : nat) (w : future) : future := fun n => w (k+n)%nat.

Fixpoint prefix (k : nat) (w : future) (p : point) : point :=
  match k with O => p | S n => branch (w O) (prefix n (shift w) p) end.
Definition approx (w : future) (n : nat) := prefix n w (0,0).

Lemma origin_inside : inside (0,0).
Proof. unfold inside, in_U; simpl; lra. Qed.
Lemma branch_inside : forall s p, inside p -> inside (branch s p).
Proof.
  intros [] [x y]; unfold inside, branch; simpl;
  auto using phi_a_invariant, phi_b_invariant.
Qed.
Lemma prefix_inside : forall n w p, inside p -> inside (prefix n w p).
Proof.
  induction n; intros w p Hp; simpl; auto using branch_inside.
Qed.
Lemma approx_inside : forall w n, inside (approx w n).
Proof. intros; apply prefix_inside, origin_inside. Qed.

Lemma branch_contraction : forall s p q e,
  inside p -> inside q -> 0 <= e -> close e p q ->
  close (e/900) (branch s p) (branch s q).
Proof.
  intros [] [x y] [x' y'] e Hp Hq He [Hx Hy]; unfold close, branch; simpl;
  [apply phi_a_contraction|apply phi_b_contraction]; assumption.
Qed.

Lemma rectangle_diameter : forall p q, inside p -> inside q -> close (2/5) p q.
Proof.
  intros [x y] [x' y']; unfold inside, in_U, close; simpl.
  intros. split; apply Rabs_le; lra.
Qed.

Lemma prefix_contraction : forall n w p q e,
  inside p -> inside q -> 0 <= e -> close e p q ->
  close (e*(1/900)^n) (prefix n w p) (prefix n w q).
Proof.
  induction n as [|n IH]; intros w p q e Hp Hq He Hpq; simpl.
  - replace (e*1) with e by ring. exact Hpq.
  - replace (e*((1/900)*(1/900)^n)) with ((e*(1/900)^n)/900) by field.
    apply branch_contraction; auto using prefix_inside.
    + apply Rmult_le_pos; auto. apply pow_le; lra.
Qed.

Lemma prefix_split : forall n k w p,
  prefix (n+k) w p = prefix n w (prefix k (shift_by n w) p).
Proof.
  induction n as [|n IH]; intros k w p; simpl.
  - unfold shift_by. reflexivity.
  - rewrite IH. f_equal.
Qed.

Lemma approx_tail_bound : forall w n m,
  (n <= m)%nat -> close ((2/5)*(1/900)^n) (approx w n) (approx w m).
Proof.
  intros w n m Hnm. replace m with (n+(m-n))%nat by lia.
  unfold approx. rewrite prefix_split.
  apply prefix_contraction; auto using origin_inside, prefix_inside.
  - lra.
  - apply rectangle_diameter; auto using origin_inside, prefix_inside.
Qed.

Lemma abs_triangle_difference : forall a b c,
  Rabs (a-b) <= Rabs (a-c)+Rabs (b-c).
Proof.
  intros a b c. replace (a-b) with ((a-c)+ -(b-c)) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_Ropp. lra.
Qed.

Lemma coding_cauchy : forall w,
  Cauchy_crit (fun n => fst (approx w n)) /\
  Cauchy_crit (fun n => snd (approx w n)).
Proof.
  intro w.
  assert (Hcommon : forall eps, 0 < eps -> exists N, forall n m,
    (N <= n)%nat -> (N <= m)%nat ->
    close eps (approx w n) (approx w m)).
  { intros eps He.
    destruct (pow_lt_1_zero (1/900) ltac:(rewrite Rabs_right; lra)
                eps He) as [N HN].
    exists N. intros n m Hn Hm.
    destruct (approx_tail_bound w N n Hn) as [Hnx Hny].
    destruct (approx_tail_bound w N m Hm) as [Hmx Hmy].
    specialize (HN N (Nat.le_refl N)).
    rewrite Rabs_right in HN; [|apply Rle_ge, pow_le; lra].
    rewrite Rabs_minus_sym in Hnx, Hny, Hmx, Hmy.
    pose proof (abs_triangle_difference (fst (approx w n)) (fst (approx w m)) (fst (approx w N))).
    pose proof (abs_triangle_difference (snd (approx w n)) (snd (approx w m)) (snd (approx w N))).
    unfold close. split; lra. }
  split; intros eps He;
  destruct (Hcommon (eps/2) ltac:(lra)) as [N HN]; exists N;
  intros n m Hn Hm; specialize (HN n m Hn Hm); unfold close in HN;
  unfold Rdist; lra.
Qed.

Definition coded_x (w : future) :=
  proj1_sig (R_complete (fun n => fst (approx w n)) (proj1 (coding_cauchy w))).
Definition coded_y (w : future) :=
  proj1_sig (R_complete (fun n => snd (approx w n)) (proj2 (coding_cauchy w))).
Definition coded (w : future) : point := (coded_x w, coded_y w).

Theorem coded_converges : forall w,
  Un_cv (fun n => fst (approx w n)) (fst (coded w)) /\
  Un_cv (fun n => snd (approx w n)) (snd (coded w)).
Proof.
  intro w. split;
  [exact (proj2_sig (R_complete _ (proj1 (coding_cauchy w))))
  |exact (proj2_sig (R_complete _ (proj2 (coding_cauchy w))))].
Qed.

Lemma constant_converges : forall c, Un_cv (fun _ : nat => c) c.
Proof.
  intros c eps He. exists O. intros n Hn.
  unfold Rdist. replace (c-c) with 0 by ring. rewrite Rabs_R0. exact He.
Qed.

Theorem coded_inside : forall w, inside (coded w).
Proof.
  intro w. destruct (coded_converges w) as [Hx Hy].
  unfold inside, in_U. split; split.
  - apply (@Rle_cv_lim (fun _ => -1/5) (fun n => fst (approx w n)));
      auto using constant_converges.
    intro n. pose proof (approx_inside w n). unfold inside, in_U in *. lra.
  - apply (@Rle_cv_lim (fun n => fst (approx w n)) (fun _ => 1/5));
      auto using constant_converges.
    intro n. pose proof (approx_inside w n). unfold inside, in_U in *. lra.
  - apply (@Rle_cv_lim (fun _ => -1/50) (fun n => snd (approx w n)));
      auto using constant_converges.
    intro n. pose proof (approx_inside w n). unfold inside, in_U in *. lra.
  - apply (@Rle_cv_lim (fun n => snd (approx w n)) (fun _ => 1/50));
      auto using constant_converges.
    intro n. pose proof (approx_inside w n). unfold inside, in_U in *. lra.
Qed.

Definition point_converges (p : nat -> point) (q : point) :=
  Un_cv (fun n => fst (p n)) (fst q) /\
  Un_cv (fun n => snd (p n)) (snd q).

Lemma branch_preserves_limits : forall s p q,
  (forall n, inside (p n)) -> inside q -> point_converges p q ->
  point_converges (fun n => branch s (p n)) (branch s q).
Proof.
  intros s p q Hi Hq [Hx Hy].
  assert (Hcommon : forall eps, 0 < eps -> exists N, forall n,
    (N <= n)%nat -> close (eps/900) (branch s (p n)) (branch s q)).
  { intros eps He. destruct (Hx eps He) as [Nx HNx].
    destruct (Hy eps He) as [Ny HNy]. exists (Nat.max Nx Ny).
    intros n Hn. apply branch_contraction; auto; [lra|].
    specialize (HNx n ltac:(lia)). specialize (HNy n ltac:(lia)).
    unfold Rdist in *. split; lra. }
  split; intros eps He; destruct (Hcommon eps He) as [N HN];
    exists N; intros n Hn; specialize (HN n Hn);
    unfold close in HN; unfold Rdist; lra.
Qed.

Lemma successor_converges : forall f l,
  Un_cv f l -> Un_cv (fun n => f (S n)) l.
Proof.
  intros f l H eps He. destruct (H eps He) as [N HN].
  exists N. intros n Hn. apply HN; lia.
Qed.

Theorem coded_recursion : forall w, coded w = branch (w O) (coded (shift w)).
Proof.
  intro w.
  pose proof (branch_preserves_limits (w O) (approx (shift w)) (coded (shift w))
    (approx_inside (shift w)) (coded_inside (shift w)) (coded_converges (shift w)))
    as [Hbx Hby].
  destruct (coded_converges w) as [Hx Hy].
  assert (Hsx := successor_converges _ _ Hx).
  assert (Hsy := successor_converges _ _ Hy).
  change (Un_cv (fun n => fst (approx w (S n)))
               (fst (branch (w O) (coded (shift w))))) in Hbx.
  change (Un_cv (fun n => snd (approx w (S n)))
               (snd (branch (w O) (coded (shift w))))) in Hby.
  destruct (coded w) as [x y]; destruct (branch (w O) (coded (shift w))) as [u v].
  simpl in *. f_equal;
  [exact (@UL_sequence _ _ _ Hsx Hbx)|exact (@UL_sequence _ _ _ Hsy Hby)].
Qed.

Lemma coded_head_unique : forall w z,
  coded w = coded z -> w O = z O.
Proof.
  intros w z H. rewrite (coded_recursion w), (coded_recursion z) in H.
  pose proof (coded_inside (shift w)) as Hw.
  pose proof (coded_inside (shift z)) as Hz.
  unfold inside in Hw, Hz.
  destruct (w O) eqn:Ew; destruct (z O) eqn:Ez; auto;
    unfold branch in H; inversion H.
  - exfalso. exact (phi_disjoint _ _ _ _ Hw Hz H2).
  - exfalso. exact (phi_disjoint _ _ _ _ Hz Hw (eq_sym H2)).
Qed.

Lemma coded_shift_unique : forall w z,
  coded w = coded z -> coded (shift w) = coded (shift z).
Proof.
  intros w z H. pose proof (coded_head_unique w z H) as Hhead.
  rewrite (coded_recursion w), (coded_recursion z), Hhead in H.
  pose proof (coded_inside (shift w)) as Hw.
  pose proof (coded_inside (shift z)) as Hz.
  unfold inside in Hw, Hz.
  destruct (coded (shift w)) as [x y]; destruct (coded (shift z)) as [u v].
  simpl in *. destruct (z O); unfold branch in H; simpl in H; inversion H.
  - destruct (phi_a_injective x y u v Hw Hz H1 H2); subst; reflexivity.
  - destruct (phi_b_injective x y u v Hw Hz H1 H2); subst; reflexivity.
Qed.

Theorem coded_future_injective : forall w z,
  coded w = coded z -> forall n, w n = z n.
Proof.
  intros w z H n. revert w z H. induction n as [|n IH]; intros w z H.
  - exact (coded_head_unique w z H).
  - change (shift w n = shift z n). apply IH, coded_shift_unique; exact H.
Qed.

Lemma coded_prefix : forall n w,
  coded w = prefix n w (coded (shift_by n w)).
Proof.
  induction n as [|n IH]; intro w; simpl.
  - reflexivity.
  - rewrite (coded_recursion w). rewrite (IH (shift w)). reflexivity.
Qed.

Lemma prefix_agreement : forall n w z p,
  (forall k, (k < n)%nat -> w k = z k) -> prefix n w p = prefix n z p.
Proof.
  induction n as [|n IH]; intros w z p H; simpl; auto.
  rewrite (H O ltac:(lia)). f_equal. apply IH.
  intros k Hk. unfold shift. apply H; lia.
Qed.

Theorem common_future_estimate : forall n w z,
  (forall k, (k < n)%nat -> w k = z k) ->
  close ((2/5)*(1/900)^n) (coded w) (coded z).
Proof.
  intros n w z H. rewrite (coded_prefix n w), (coded_prefix n z).
  rewrite <- (prefix_agreement n w z (coded (shift_by n z)) H).
  apply prefix_contraction; auto using coded_inside.
  - lra.
  - apply rectangle_diameter; apply coded_inside.
Qed.

Theorem coded_extensional : forall w z,
  (forall n, w n = z n) -> coded w = coded z.
Proof.
  intros w z H.
  assert (Happrox : forall n, approx w n = approx z n).
  { intro n. apply prefix_agreement. intros; apply H. }
  destruct (coded_converges w) as [Hwx Hwy].
  destruct (coded_converges z) as [Hzx Hzy].
  assert (Hwx' : Un_cv (fun n => fst (approx z n)) (fst (coded w))).
  { intros eps He. destruct (Hwx eps He) as [N HN].
    exists N. intros n Hn. rewrite <- Happrox. apply HN; auto. }
  assert (Hwy' : Un_cv (fun n => snd (approx z n)) (snd (coded w))).
  { intros eps He. destruct (Hwy eps He) as [N HN].
    exists N. intros n Hn. rewrite <- Happrox. apply HN; auto. }
  destruct (coded w), (coded z); simpl in *. f_equal;
    [exact (@UL_sequence _ _ _ Hwx' Hzx)|exact (@UL_sequence _ _ _ Hwy' Hzy)].
Qed.

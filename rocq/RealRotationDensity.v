From Stdlib Require Import Reals Psatz Lia ZArith Classical.
Open Scope R_scope.

Definition irrational_rotation_number (x : R) :=
  forall m z : Z, m <> 0%Z -> IZR m*x+IZR z <> 0.
Definition integer_span (x r : R) := exists m z : Z, r = IZR m*x+IZR z.

Lemma span_one : forall x, integer_span x 1.
Proof. intro x. exists 0%Z, 1%Z. simpl; ring. Qed.
Lemma span_generator : forall x, integer_span x x.
Proof. intro x. exists 1%Z, 0%Z. simpl; ring. Qed.
Lemma span_subtract : forall x a b,
  integer_span x a -> integer_span x b -> integer_span x (a-b).
Proof.
  intros x a b [m [z Ha]] [n [w Hb]]. exists (m-n)%Z, (z-w)%Z.
  rewrite !minus_IZR, Ha, Hb. ring.
Qed.
Lemma span_integer_scale : forall x a k,
  integer_span x a -> integer_span x (IZR k*a).
Proof.
  intros x a k [m [z Ha]]. exists (k*m)%Z, (k*z)%Z.
  rewrite !mult_IZR, Ha; ring.
Qed.

(* Greatest lower bound of a nonempty set of positive reals. *)
Lemma positive_set_infimum : forall E : R -> Prop,
  (exists a, E a) -> (forall a, E a -> 0 < a) ->
  { d : R | 0 <= d /\ (forall a, E a -> d <= a) /\
    forall eps, 0 < eps -> exists a, E a /\ a < d+eps }.
Proof.
  intros E Hnonempty Hpositive.
  set (F := fun t => exists a, E a /\ t = -a).
  assert (HFnonempty : exists t, F t).
  { destruct Hnonempty as [a Ha]. exists (-a), a. auto. }
  assert (HFbound : bound F).
  { exists 0. intros t [a [Ha Ht]]. subst. pose proof (Hpositive a Ha); lra. }
  destruct (completeness F HFbound HFnonempty) as [u [Hu Hleast]].
  exists (-u). split.
  - assert (u <= 0) by (apply Hleast; intros t [a [Ha Ht]]; subst; pose proof (Hpositive a Ha); lra).
    lra.
  - split.
    + intros a Ha. assert (-a <= u) by (apply Hu; exists a; auto). lra.
    + intros eps He. apply NNPP. intro Hnone.
      assert (Hupper : is_upper_bound F (u-eps)).
      { intros t [a [Ha Ht]]. subst t.
        assert (~a < -u+eps) by (intro H; apply Hnone; exists a; auto). lra. }
      pose proof (Hleast (u-eps) Hupper). lra.
Qed.

Lemma span_discrete_step : forall x d,
  0 < d -> integer_span x d ->
  (forall r, integer_span x r -> 0 < r -> d <= r) ->
  forall h, integer_span x h -> exists k : Z, h = IZR k*d.
Proof.
  intros x d Hd Hspan Hlower h Hh.
  set (k := Int_part (h/d)).
  pose proof (base_Int_part (h/d)) as Hfloor.
  change (IZR k <= h/d /\ IZR k-h/d > -1) in Hfloor.
  assert (Hscale : h/d*d = h) by (field; lra).
  assert (Hlo : IZR k*d <= h).
  { pose proof (Rmult_le_compat_r d _ _ ltac:(lra) (proj1 Hfloor)). rewrite Hscale in H; exact H. }
  assert (Hhi : h < (IZR k+1)*d).
  { assert (Hf : h/d < IZR k+1) by lra.
    pose proof (Rmult_lt_compat_r d _ _ Hd Hf). rewrite Hscale in H; exact H. }
  assert (Hrspan : integer_span x (h-IZR k*d)) by (apply span_subtract; auto using span_integer_scale).
  assert (Hzero : h-IZR k*d = 0).
  { destruct (Req_dec (h-IZR k*d) 0); auto.
    pose proof (Hlower _ Hrspan ltac:(lra)). lra. }
  exists k. lra.
Qed.

Theorem irrational_span_arbitrarily_small : forall x,
  irrational_rotation_number x -> forall eps, 0 < eps ->
  exists h, integer_span x h /\ 0 < h < eps.
Proof.
  intros x Hirr.
  set (E := fun h => integer_span x h /\ 0 < h).
  assert (HE : exists h, E h) by (exists 1; split; [apply span_one|lra]).
  destruct (positive_set_infimum E HE ltac:(intros a Ha; exact (proj2 Ha)))
    as [d [Hd [Hlower Happrox]]].
  assert (Hd0 : d = 0).
  { destruct (Req_dec d 0); auto.
    assert (Hdpos : 0 < d) by lra.
    destruct (Happrox (d/2) ltac:(lra)) as [r [Hr Hnear]].
    pose proof (Hlower r Hr) as Hdr.
    assert (Hrd : r = d).
    { destruct (Req_dec r d); auto.
      destruct (Happrox ((r-d)/2) ltac:(lra)) as [s [Hs Hsnear]].
      pose proof (Hlower s Hs) as Hds.
      assert (Hdiff : E (r-s)).
      { split; [apply span_subtract; [exact (proj1 Hr)|exact (proj1 Hs)]|lra]. }
      pose proof (Hlower (r-s) Hdiff). lra. }
    assert (Hdspan : integer_span x d) by (rewrite <- Hrd; exact (proj1 Hr)).
    assert (Hstep : forall h, integer_span x h -> exists k : Z, h = IZR k*d).
    { apply span_discrete_step; auto. intros h Hh Hpos. apply Hlower; split; assumption. }
    destruct (Hstep 1 (span_one x)) as [k Hk].
    destruct (Hstep x (span_generator x)) as [l Hl].
    assert (Hknz : k <> 0%Z) by (intro H0; rewrite H0 in Hk; simpl in Hk; nra).
    exfalso. apply (Hirr k (-l)%Z Hknz). rewrite opp_IZR, Hl.
    replace (IZR k*(IZR l*d)+ -IZR l) with (IZR l*(IZR k*d)-IZR l) by ring.
    rewrite <- Hk; ring. }
  intros eps He. destruct (Happrox eps He) as [h [[Hspan Hpos] Hsmall]].
  exists h. rewrite Hd0 in Hsmall. split; [exact Hspan|lra].
Qed.

Lemma nonnegative_integer_part : forall r,
  0 <= r -> (0 <= Int_part r)%Z.
Proof.
  intros r Hr. pose proof (base_Int_part r) as H.
  destruct (Z_le_gt_dec 0 (Int_part r)) as [Hnonnegative|Hnegative]; auto.
  assert (Hle : (Int_part r <= -1)%Z) by lia.
  pose proof (IZR_le _ _ Hle). simpl in H0. lra.
Qed.

Lemma scaled_floor_approximation : forall t h,
  0 <= t -> 0 < h -> exists k : Z,
    (0 <= k)%Z /\ 0 <= t-IZR k*h < h.
Proof.
  intros t h Ht Hh. exists (Int_part (t/h)). split.
  - apply nonnegative_integer_part.
    unfold Rdiv. apply Rmult_le_pos; [exact Ht|apply Rlt_le, Rinv_0_lt_compat; exact Hh].
  - pose proof (base_Int_part (t/h)) as Hfloor.
    assert (Hscale : t/h*h = t) by (field; lra).
    pose proof (Rmult_le_compat_r h _ _ ltac:(lra) (proj1 Hfloor)) as Hlo.
    assert (Hf : t/h < IZR (Int_part (t/h))+1) by lra.
    pose proof (Rmult_lt_compat_r h _ _ Hh Hf) as Hhi.
    rewrite Hscale in Hlo, Hhi. split; lra.
Qed.

(* Forward powers, not merely the two-sided integer subgroup. *)
Theorem irrational_forward_rotation_dense : forall x,
  irrational_rotation_number x -> forall y eps, 0 < eps ->
  exists n : nat, exists z : Z, Rabs (INR n*x-y-IZR z) < eps.
Proof.
  intros x Hirr y eps He.
  destruct (irrational_span_arbitrarily_small x Hirr (Rmin eps 1) ltac:(apply Rmin_pos; lra))
    as [h [[m [z Hz]] [Hh Hsmall]]].
  pose proof (Rmin_l eps 1). pose proof (Rmin_r eps 1).
  assert (Hm : m <> 0%Z).
  { intro Hm0. rewrite Hm0 in Hz; simpl in Hz.
    assert (0 < IZR z < 1) by nra.
    assert (Hz0 : (0 < z)%Z) by (apply lt_IZR; simpl; lra).
    assert (Hz1 : (z < 1)%Z) by (apply lt_IZR; simpl; lra). lia. }
  destruct (Z_lt_ge_dec 0 m) as [Hmpos|Hmneg].
  - destruct (scaled_floor_approximation (frac_part y) h ltac:(pose proof (base_fp y); lra) Hh)
      as [k [Hk Hrem]].
    exists (Z.to_nat (k*m)), (-k*z-Int_part y)%Z.
    rewrite INR_IZR_INZ, Z2Nat.id by nia.
    repeat first [rewrite minus_IZR|rewrite opp_IZR|rewrite mult_IZR].
    unfold frac_part in Hrem. rewrite Hz in Hrem.
    apply Rabs_def1; nra.
  - destruct (scaled_floor_approximation (frac_part (-y)) h ltac:(pose proof (base_fp (-y)); lra) Hh)
      as [k [Hk Hrem]].
    exists (Z.to_nat (k*(-m))), (k*z+Int_part (-y))%Z.
    rewrite INR_IZR_INZ, Z2Nat.id by nia.
    repeat first [rewrite plus_IZR|rewrite opp_IZR|rewrite mult_IZR].
    unfold frac_part in Hrem. rewrite Hz in Hrem.
    apply Rabs_def1; nra.
Qed.

Theorem irrational_forward_rotation_dense_late : forall x,
  irrational_rotation_number x -> forall y eps N, 0 < eps ->
  exists n : nat, exists z : Z, (N <= n)%nat /\ Rabs (INR n*x-y-IZR z) < eps.
Proof.
  intros x Hirr y eps N He.
  destruct (irrational_forward_rotation_dense x Hirr (y-INR N*x) eps He) as [n [z H]].
  exists (N+n)%nat, z. split; [lia|]. rewrite plus_INR.
  replace ((INR N+INR n)*x-y-IZR z) with (INR n*x-(y-INR N*x)-IZR z) by ring. exact H.
Qed.

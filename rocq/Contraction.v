From Stdlib Require Import Reals Psatz.
From HallRay Require Import ReturnBranches.
Open Scope R_scope.

Lemma abs_linear_bound : forall a b dx dy eps,
  0 <= eps -> Rabs a <= 501/50 -> Rabs b <= 6/5 ->
  Rabs dx <= eps -> Rabs dy <= eps ->
  Rabs (a*dx+b*dy) <= (561/50)*eps.
Proof.
  intros a b dx dy eps He Ha Hb Hx Hy.
  eapply Rle_trans; [apply Rabs_triang|]. rewrite !Rabs_mult.
  assert (Hx' : Rabs a*Rabs dx <= (501/50)*eps).
  { apply Rmult_le_compat; auto using Rabs_pos. }
  assert (Hy' : Rabs b*Rabs dy <= (6/5)*eps).
  { apply Rmult_le_compat; auto using Rabs_pos. } lra.
Qed.

Lemma large_denominator_bound : forall D z eps,
  (503/5)^2 <= D -> 0 <= eps ->
  Rabs (D*z) <= (561/50)*eps -> Rabs z <= eps/900.
Proof.
  intros D z eps HD He Hz.
  rewrite Rabs_mult, Rabs_right in Hz; [|simpl in HD; lra].
  assert (Hlow : (503/5)^2*Rabs z <= D*Rabs z).
  { apply Rmult_le_compat_r; auto using Rabs_pos. }
  lra.
Qed.

Theorem phi_a_contraction : forall x y x' y' eps,
  in_U x y -> in_U x' y' -> 0 <= eps ->
  Rabs (x-x') <= eps -> Rabs (y-y') <= eps ->
  Rabs (phi_a1 x y-phi_a1 x' y') <= eps/900 /\
  Rabs (phi_a2 x y-phi_a2 x' y') <= eps/900.
Proof.
  intros x y x' y' eps Hu Hu' He Hx Hy.
  pose proof (da_bounds x y Hu) as Hd.
  pose proof (da_bounds x' y' Hu') as Hd'.
  assert (Hda : da x y <> 0) by lra.
  assert (Hda' : da x' y' <> 0) by lra.
  assert (HD : (503/5)^2 <= da x y*da x' y').
  { pose proof (Rmult_le_compat (503/5) (da x y) (503/5) (da x' y')
                  ltac:(lra) ltac:(lra) ltac:(lra) ltac:(lra)). nra. }
  split.
  - apply (large_denominator_bound (da x y*da x' y')); auto.
    assert (Hid : da x y*da x' y'*(phi_a1 x y-phi_a1 x' y') =
                  (10-y)*(x-x')+(x-1)*(y-y')).
    { unfold phi_a1. field_simplify; [unfold da; ring|split; assumption]. }
    rewrite Hid. apply abs_linear_bound; auto.
    + unfold in_U in Hu. rewrite Rabs_right; lra.
    + unfold in_U in Hu. rewrite Rabs_left; lra.
  - apply (large_denominator_bound (da x y*da x' y')); auto.
    assert (Hid : da x y*da x' y'*(phi_a2 x y-phi_a2 x' y') =
                  (x-x')+10*(y-y')).
    { unfold phi_a2. field_simplify; [unfold da; ring|split; assumption]. }
    rewrite Hid.
    eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_mult.
    replace (Rabs 10) with 10 by (rewrite Rabs_right; lra). lra.
Qed.

Lemma reflect_U : forall x y, in_U x y -> in_U x (-y).
Proof. unfold in_U; intros; lra. Qed.

Lemma phi_b1_reflect : forall x y, phi_b1 x y = phi_a1 x (-y).
Proof.
  intros. unfold phi_b1, phi_a1, da, db.
  replace (101-x-10*(-y)) with (101-x+10*y) by ring.
  replace (10- -y) with (10+y) by ring. reflexivity.
Qed.
Lemma phi_b2_reflect : forall x y, phi_b2 x y = -phi_a2 x (-y).
Proof.
  intros. unfold phi_b2, phi_a2, da, db, Rdiv.
  replace (101-x-10*(-y)) with (101-x+10*y) by ring. ring.
Qed.

Theorem phi_b_contraction : forall x y x' y' eps,
  in_U x y -> in_U x' y' -> 0 <= eps ->
  Rabs (x-x') <= eps -> Rabs (y-y') <= eps ->
  Rabs (phi_b1 x y-phi_b1 x' y') <= eps/900 /\
  Rabs (phi_b2 x y-phi_b2 x' y') <= eps/900.
Proof.
  intros x y x' y' eps Hu Hu' He Hx Hy.
  assert (Hry : Rabs (-y- -y') <= eps).
  { replace (-y- -y') with (-(y-y')) by ring. rewrite Rabs_Ropp. exact Hy. }
  destruct (phi_a_contraction x (-y) x' (-y') eps
              (reflect_U x y Hu) (reflect_U x' y' Hu') He Hx Hry) as [H1 H2].
  rewrite !phi_b1_reflect, !phi_b2_reflect.
  replace (-phi_a2 x (-y)- -phi_a2 x' (-y')) with
          (-(phi_a2 x (-y)-phi_a2 x' (-y'))) by ring.
  rewrite Rabs_Ropp. split; assumption.
Qed.

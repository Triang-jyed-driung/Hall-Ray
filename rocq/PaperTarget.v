From Stdlib Require Import Reals Psatz Lia ZArith.
Open Scope R_scope.

(* Statement of the paper's main theorem, proved as hall_ray in
   HallRayTheorem.v. This file only defines its mathematical objects. *)

Definition vector2 := (R*R)%type.
Definition vzero : vector2 := (0,0).
Definition vadd (x y : vector2) : vector2 := (fst x+fst y, snd x+snd y).
Definition vscale (r : R) (x : vector2) : vector2 := (r*fst x,r*snd x).

Record planar_norm := {
  length2 : vector2 -> R;
  length2_nonnegative : forall v, 0 <= length2 v;
  length2_zero : length2 vzero = 0;
  length2_definite : forall v, length2 v = 0 -> v = vzero;
  length2_homogeneous : forall r v, length2 (vscale r v) = Rabs r*length2 v;
  length2_triangle : forall u v, length2 (vadd u v) <= length2 u+length2 v
}.

(* A concrete instance ensures that the quantified norm interface is inhabited. *)
Definition l1_planar_norm : planar_norm.
Proof.
  refine {| length2 := fun v => Rabs (fst v)+Rabs (snd v) |}.
  - intro v. pose proof (Rabs_pos (fst v)). pose proof (Rabs_pos (snd v)). lra.
  - unfold vzero; simpl. rewrite Rabs_R0. ring.
  - intros [x y] H. simpl in H.
    pose proof (Rabs_pos x). pose proof (Rabs_pos y).
    assert (Hx : x = 0).
    { destruct (Rcase_abs x); [rewrite (Rabs_left x) in H by lra|rewrite (Rabs_right x) in H by lra]; lra. }
    assert (Hy : y = 0).
    { destruct (Rcase_abs y); [rewrite (Rabs_left y) in H by lra|rewrite (Rabs_right y) in H by lra]; lra. }
    subst. reflexivity.
  - intros r [x y]. unfold vscale; simpl. rewrite !Rabs_mult. ring.
  - intros [x y] [u v]. unfold vadd; simpl.
    pose proof (Rabs_triang x u). pose proof (Rabs_triang y v). lra.
Defined.

Definition approximation_vector (x : vector2) (q : nat) (p1 p2 : Z) : vector2 :=
  (INR q*fst x-IZR p1, INR q*snd x-IZR p2).
Definition approximation_value (nm : planar_norm) (x : vector2)
    (q : nat) (p1 p2 : Z) :=
  sqrt (INR q)*length2 nm (approximation_vector x q p1 p2).

(* Epsilon formulation of liminf_q sqrt(q) min_p ||qx-p|| = rho.
   Lower bounds quantify over ALL integer p; upper bounds exhibit p and
   arbitrarily large q. This avoids postulating a nearest-point oracle. *)
Definition has_approximation_constant (nm : planar_norm) (x : vector2) (rho : R) :=
  (forall eps, 0 < eps -> exists Q, forall q,
     (Q <= q)%nat -> (0 < q)%nat -> forall p1 p2,
     rho-eps <= approximation_value nm x q p1 p2) /\
  (forall eps, 0 < eps -> forall Q, exists q p1 p2,
     (Q <= q)%nat /\ (0 < q)%nat /\
     approximation_value nm x q p1 p2 <= rho+eps).

Definition rational_vector (x : vector2) : Prop :=
  exists q p1 p2, (0 < q)%nat /\
    fst x = IZR p1/INR q /\ snd x = IZR p2/INR q.

Definition hall_ray_claim : Prop :=
  forall nm : planar_norm, exists rho0, 0 < rho0 /\
    forall rho, 0 < rho < rho0 -> exists x : vector2,
      ~rational_vector x /\ has_approximation_constant nm x rho.

Lemma nat_cast_integer : forall n, IZR (Z.of_nat n) = INR n.
Proof. intro n. rewrite INR_IZR_INZ. reflexivity. Qed.

Lemma rational_multiple_error_zero : forall nm x q p1 p2 k,
  (0 < q)%nat -> fst x = IZR p1/INR q -> snd x = IZR p2/INR q ->
  approximation_value nm x (k*q) (Z.of_nat k*p1) (Z.of_nat k*p2) = 0.
Proof.
  intros nm [x y] q p1 p2 k Hq Hx Hy. simpl in Hx, Hy.
  assert (HqR : INR q <> 0).
  { apply not_0_INR. lia. }
  unfold approximation_value, approximation_vector; simpl fst; simpl snd.
  rewrite mult_INR, !mult_IZR, !nat_cast_integer, Hx, Hy.
  assert (Hz1 : INR k*INR q*(IZR p1/INR q)-INR k*IZR p1 = 0) by (field; exact HqR).
  assert (Hz2 : INR k*INR q*(IZR p2/INR q)-INR k*IZR p2 = 0) by (field; exact HqR).
  rewrite Hz1, Hz2. change (sqrt (INR k*INR q)*length2 nm vzero = 0).
  rewrite length2_zero. ring.
Qed.

Theorem positive_constant_irrational : forall nm x rho,
  0 < rho -> has_approximation_constant nm x rho -> ~rational_vector x.
Proof.
  intros nm x rho Hr [Hlower Hupper] [q [p1 [p2 [Hq [Hx Hy]]]]].
  destruct (Hlower (rho/2) ltac:(lra)) as [Q HQ].
  specialize (HQ ((S Q)*q)%nat ltac:(nia) ltac:(nia)
                 (Z.of_nat (S Q)*p1)%Z (Z.of_nat (S Q)*p2)%Z).
  rewrite (rational_multiple_error_zero nm x q p1 p2 (S Q) Hq Hx Hy) in HQ. lra.
Qed.

Theorem approximation_constant_unique : forall nm x rho eta,
  has_approximation_constant nm x rho ->
  has_approximation_constant nm x eta -> rho = eta.
Proof.
  intros nm x rho eta [Hrl Hru] [Hel Heu].
  assert (Horder : forall a b,
    (forall eps, 0 < eps -> exists Q, forall q,
      (Q <= q)%nat -> (0 < q)%nat -> forall p1 p2,
      a-eps <= approximation_value nm x q p1 p2) ->
    (forall eps, 0 < eps -> forall Q, exists q p1 p2,
      (Q <= q)%nat /\ (0 < q)%nat /\ approximation_value nm x q p1 p2 <= b+eps) -> a <= b).
  { intros a b Hl Hu. destruct (Rle_dec a b); auto.
    destruct (Hl ((a-b)/3) ltac:(lra)) as [Q HQ].
    destruct (Hu ((a-b)/3) ltac:(lra) Q) as [q [p1 [p2 [Hq [Hpos Hval]]]]].
    specialize (HQ q Hq Hpos p1 p2). lra. }
  pose proof (Horder rho eta Hrl Heu). pose proof (Horder eta rho Hel Hru). lra.
Qed.

Theorem approximation_constant_nonnegative : forall nm x rho,
  has_approximation_constant nm x rho -> 0 <= rho.
Proof.
  intros nm x rho [Hl Hu]. destruct (Rle_dec 0 rho); auto.
  destruct (Hu (-rho/2) ltac:(lra) O) as [q [p1 [p2 [Hq [Hpos Hv]]]]].
  unfold approximation_value in Hv.
  pose proof (sqrt_pos (INR q)).
  pose proof (length2_nonnegative nm (approximation_vector x q p1 p2)).
  assert (0 <= sqrt (INR q)*length2 nm (approximation_vector x q p1 p2))
    by (apply Rmult_le_pos; assumption). lra.
Qed.

Theorem rational_constant_zero : forall nm x,
  rational_vector x -> has_approximation_constant nm x 0.
Proof.
  intros nm x [q [p1 [p2 [Hq [Hx Hy]]]]]. split.
  - intros eps He. exists O. intros n Hn Hpos a b.
    unfold approximation_value.
    pose proof (sqrt_pos (INR n)).
    pose proof (length2_nonnegative nm (approximation_vector x n a b)).
    assert (0 <= sqrt (INR n)*length2 nm (approximation_vector x n a b))
      by (apply Rmult_le_pos; assumption). lra.
  - intros eps He Q. exists ((S Q)*q)%nat.
    exists (Z.of_nat (S Q)*p1)%Z, (Z.of_nat (S Q)*p2)%Z.
    repeat split; try nia.
    rewrite (rational_multiple_error_zero nm x q p1 p2 (S Q) Hq Hx Hy). lra.
Qed.

From Stdlib Require Import Reals Psatz Lia Arith.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices
  LatticeBasis LatticeReturns LatticeOrbit PeriodicReturns PeriodicWords
  DefectLimit SymbolicCocycle LatticeSystole SystoleCurves StableForgetting.
Open Scope R_scope.

Definition periodic_position_frame n E k j r :=
  mul3 (diagonal_flow r)
    (orbit_frame (orbit_shift j (periodic_word n))
      (mul2 (mul2 E (matrix_power (periodic_return n) k))
        (orbit_product j (periodic_word n)))).

Theorem periodic_lattice_position : forall n E k j r,
  same_lattice
    (mul3 (diagonal_flow (INR k*periodic_word_time n+
      orbit_time j (periodic_word n)+r)) (orbit_frame (periodic_word n) E))
    (periodic_position_frame n E k j r).
Proof.
  intros n E k j r.
  pose proof (orbit_lattice_return (periodic_word n) E (k*(S n)+j) r) as H.
  destruct (periodic_word_iterates n k j) as [Hs [Ht Hp]].
  rewrite Hs,Ht,Hp, <- mul2_assoc in H; exact H.
Qed.

Theorem periodic_forward_orbit_cover : forall n E t,
  0 <= t -> exists k j r,
    (j <= n)%nat /\ 0 <= r < orbit_roof_time (orbit_shift j (periodic_word n)) /\
    t = INR k*periodic_word_time n+orbit_time j (periodic_word n)+r /\
    same_lattice (mul3 (diagonal_flow t) (orbit_frame (periodic_word n) E))
      (periodic_position_frame n E k j r).
Proof.
  intros n E t Ht.
  destruct (orbit_forward_segment_cover (periodic_word n) t Ht) as [m [r [Hr Htime]]].
  set (k := (m/(S n))%nat).
  set (j := (m mod (S n))%nat).
  assert (Hj : (j <= n)%nat) by (unfold j; pose proof (Nat.mod_upper_bound m (S n) ltac:(lia)); lia).
  assert (Hm : m = (k*(S n)+j)%nat).
  { unfold k,j. pose proof (Nat.div_mod m (S n) ltac:(lia)); nia. }
  rewrite Hm in Hr,Htime.
  destruct (periodic_word_iterates n k j) as [Hs [Htimecycle Hp]].
  rewrite Hs in Hr. rewrite Htimecycle in Htime.
  exists k,j,r. split; [exact Hj|]. split; [exact Hr|]. split; [exact Htime|].
  rewrite Htime; apply periodic_lattice_position.
Qed.

Lemma periodic_position_frame_unimodular : forall n E k j r,
  det2 E = 1 -> det3 (periodic_position_frame n E k j r) = 1.
Proof.
  intros n E k j r HE. unfold periodic_position_frame.
  rewrite mul3_determinant, diagonal_flow_unimodular, orbit_frame_unimodular; [ring|].
  rewrite !det2_mul, HE, matrix_power_unimodular,
    orbit_product_matches_future, factor_product_unimodular; try ring.
  apply periodic_return_unimodular.
Qed.

Theorem periodic_height_position : forall nm n E k j r,
  det2 E = 1 ->
  lattice_height_orbit nm (orbit_frame (periodic_word n) E)
    (INR k*periodic_word_time n+orbit_time j (periodic_word n)+r) =
  cusp_height nm (periodic_position_frame n E k j r).
Proof.
  intros nm n E k j r HE. unfold lattice_height_orbit, cusp_height.
  f_equal. apply systole_same_lattice.
  - rewrite mul3_determinant, diagonal_flow_unimodular, orbit_frame_unimodular by exact HE; ring.
  - apply periodic_position_frame_unimodular; exact HE.
  - apply periodic_lattice_position.
Qed.

Theorem periodic_height_forward_cover : forall nm n E t,
  det2 E = 1 -> 0 <= t -> exists k j r,
    (j <= n)%nat /\ 0 <= r < orbit_roof_time (orbit_shift j (periodic_word n)) /\
    lattice_height_orbit nm (orbit_frame (periodic_word n) E) t =
      cusp_height nm (periodic_position_frame n E k j r).
Proof.
  intros nm n E t HE Ht.
  destruct (periodic_forward_orbit_cover n E t Ht) as [k [j [r [Hj [Hr [Htime Hl]]]]]].
  exists k,j,r. split; [exact Hj|]. split; [exact Hr|].
  rewrite Htime; apply periodic_height_position; exact HE.
Qed.

Lemma orbit_frame_left_product : forall z F E,
  orbit_frame z (mul2 F E) = mul3 (block3 1 F) (orbit_frame z E).
Proof.
  intros z F E. unfold orbit_frame, NormalizedFlow.normalized_frame, chart.
  rewrite NormalizedFlow.scale3_product_right, <- mul3_assoc, NormalizedFlow.block3_product.
  replace (1*1) with 1 by ring. reflexivity.
Qed.

Lemma diagonal_flow_block_commutes : forall F t,
  mul3 (diagonal_flow t) (block3 1 F) = mul3 (block3 1 F) (diagonal_flow t).
Proof.
  intros [] t. apply mat3_ext; unfold diagonal_flow, flow_scale, block3, mul3; simpl; ring.
Qed.

Definition fiber_translate E P := mul2 (mul2 E P) (adj2 E).

Lemma fiber_translate_unimodular : forall E P,
  det2 E = 1 -> det2 P = 1 -> det2 (fiber_translate E P) = 1.
Proof.
  intros E P HE HP. unfold fiber_translate.
  rewrite !det2_mul, adjugate_determinant, HE, HP; ring.
Qed.

Lemma fiber_translate_action : forall z E P r,
  det2 E = 1 ->
  mul3 (diagonal_flow r) (orbit_frame z (mul2 E P)) =
    mul3 (block3 1 (fiber_translate E P)) (mul3 (diagonal_flow r) (orbit_frame z E)).
Proof.
  intros z E P r HE. unfold fiber_translate.
  rewrite <- mul3_assoc, <- diagonal_flow_block_commutes, mul3_assoc,
    <- orbit_frame_left_product.
  replace (mul2 (mul2 (mul2 E P) (adj2 E)) E) with (mul2 E P).
  - reflexivity.
  - rewrite mul2_assoc, (DefectLimit.adjugate_left_identity E HE), mul2_id_right; reflexivity.
Qed.

Theorem periodic_lattice_cycle : forall n E k r,
  det2 E = 1 -> same_lattice
    (mul3 (diagonal_flow (INR k*periodic_word_time n+r)) (orbit_frame (periodic_word n) E))
    (mul3 (block3 1 (fiber_translate E (matrix_power (periodic_return n) k)))
      (mul3 (diagonal_flow r) (orbit_frame (periodic_word n) E))).
Proof.
  intros n E k r HE. pose proof (periodic_lattice_position n E k 0 r) as H.
  unfold periodic_position_frame in H. cbn [orbit_time orbit_shift orbit_product] in H.
  rewrite mul2_id_right, Rplus_0_r in H.
  rewrite fiber_translate_action in H by exact HE. exact H.
Qed.

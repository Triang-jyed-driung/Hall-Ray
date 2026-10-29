From Stdlib Require Import Reals Psatz Lia Arith List ZArith.
From HallRay Require Import MatrixAlgebra EuclideanNorm MatrixLimits ConcreteCocycle FiberProducts
  SymbolicCoding SymbolicCocycle DefectLimit PeriodicReturns WordPrefixes PrefixFibers
  NestedWords BlockConstruction ConstructedWords ConstructedCodes BoundaryWords
  TwoSidedCoding LatticeReturns PeriodicWords.
Open Scope R_scope.

Lemma opnorm_from_difference : forall A B,
  opnorm A <= opnorm (sub2 A B)+opnorm B.
Proof.
  intros A B; pose proof (opnorm_subadditive (sub2 A B) B).
  rewrite <- matrix_difference_decomposition in H; exact H.
Qed.

Lemma bounded_product_perturbation : forall A B F P K t,
  0 <= K -> 0 <= t <= 1 -> opnorm F <= 2 -> opnorm P <= K ->
  opnorm (sub2 A F) <= 2*t -> opnorm (sub2 B P) <= K*t ->
  opnorm (sub2 (mul2 A B) (mul2 F P)) <= 6*K*t.
Proof.
  intros A B F P K t HK Ht HF HP HA HB.
  assert (HBnorm : opnorm B <= 2*K).
  { pose proof (opnorm_from_difference B P); nra. }
  pose proof (opnorm_difference_triangle (mul2 A B) (mul2 F B) (mul2 F P)) as Htri.
  rewrite <-matrix_multiply_difference_left, <-matrix_multiply_difference_right in Htri.
  pose proof (opnorm_submultiplicative (sub2 A F) B) as H1.
  pose proof (opnorm_submultiplicative F (sub2 B P)) as H2.
  assert (Hbound1 : opnorm (sub2 A F)*opnorm B <= (2*t)*(2*K)).
  { apply Rmult_le_compat; try apply opnorm_nonnegative; assumption. }
  assert (Hbound2 : opnorm F*opnorm (sub2 B P) <= 2*(K*t)).
  { apply Rmult_le_compat; try apply opnorm_nonnegative; assumption. }
  nra.
Qed.

Section Fibers.
Variable nm : PaperTarget.planar_norm.
Variables H delta K : R.
Variable tau : nat -> R.
Variable states : nat -> block_state.
Hypothesis indices : forall i, state_index (states i)=i.
Hypothesis good : forall i, good_block_state delta tau (states i).
Hypothesis steps : forall i, block_step nm H delta K (states i) (states (S i)).
Hypothesis Hd : 0 < delta < 1.
Hypothesis HK : 1 <= K.
Local Abbreviation xs := (construction_prefix states).
Local Abbreviation ord := (construction_order states).
Local Abbreviation reps := (construction_repetitions states).
Local Abbreviation start := (construction_start states).
Local Abbreviation z := (construction_word states).
Local Abbreviation F i := (stage_fiber (xs i) (ord i)).

Lemma construction_reference_norm : forall i, opnorm (F i) <= 2.
Proof.
  intro i; pose proof (proj1 (proj2 (good i))) as Hb; rewrite indices in Hb.
  change (opnorm (sub2 (F i) id2) <= fiber_budget delta i) in Hb.
  pose proof (fiber_budget_within delta i ltac:(lra)).
  pose proof (matrix_near_identity_norm (F i)); lra.
Qed.

Lemma construction_periodic_fiber_norm : forall i j,
  opnorm (fiber_product j (periodic_future (ord (S i)))) <= K.
Proof.
  intros i j; pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (steps i)))))) j) as Hb.
  change (opnorm (fiber_product j (periodic_future (ord (S i))))+
    opnorm (adj2 (fiber_product j (periodic_future (ord (S i))))) <= K) in Hb.
  pose proof (opnorm_nonnegative (adj2 (fiber_product j (periodic_future (ord (S i)))))); lra.
Qed.

Lemma construction_word_future : forall k, future_of z k=construction_future states k.
Proof. intro k; apply splice_nonnegative_symbol. Qed.

Lemma construction_orbit_prefix : forall i,
  orbit_product (start i) z=fiber_product (start i) (construction_future states).
Proof. intro i; rewrite orbit_product_matches_future; apply fiber_product_extensional; apply construction_word_future. Qed.
Lemma construction_orbit_local : forall i j,
  orbit_product j (orbit_shift (start i) z)=
    fiber_product j (shift_by (start i) (construction_future states)).
Proof.
  intros i j; rewrite orbit_product_matches_future; apply fiber_product_extensional; intro k.
  unfold future_of; rewrite orbit_shift_by_matches; unfold bi_shift_by,shift_by.
  replace (Z.of_nat k+Z.of_nat (start i))%Z with (Z.of_nat (start i+k)) by lia.
  apply splice_nonnegative_symbol.
Qed.
Lemma construction_periodic_orbit : forall i j,
  orbit_product j (periodic_word (ord (S i)))=fiber_product j (periodic_future (ord (S i))).
Proof. intros; rewrite orbit_product_matches_future; apply fiber_product_extensional,periodic_word_future. Qed.

Theorem construction_cumulative_fiber_error : forall i j,
  (j <= reps (S i)*S (ord (S i)))%nat ->
  opnorm (sub2
    (mul2 (orbit_product (start i) z) (orbit_product j (orbit_shift (start i) z)))
    (mul2 (F i) (orbit_product j (periodic_word (ord (S i)))))) <= 6*K*(1/600)^(ord i).
Proof.
  intros i j Hj; rewrite construction_orbit_prefix,construction_orbit_local,construction_periodic_orbit.
  apply bounded_product_perturbation; try lra.
  - split; [apply pow_le; lra|pose proof (pow_incr (1/600) 1 (ord i) ltac:(lra)); rewrite pow1 in H0; exact H0].
  - apply construction_reference_norm.
  - apply construction_periodic_fiber_norm.
  - eapply Rle_trans; [apply (construction_prefix_fiber_error nm H delta K tau states indices good steps)|].
    apply Rmult_le_compat_r; [apply pow_le; lra|apply construction_reference_norm].
  - eapply Rle_trans; [apply (construction_local_fiber_error nm H delta K tau states indices good steps i j Hj)|].
    apply Rmult_le_compat_r; [apply pow_le; lra|apply construction_periodic_fiber_norm].
Qed.

Theorem construction_cumulative_fiber_bounds : forall i j,
  (j <= reps (S i)*S (ord (S i)))%nat -> 6*K*(1/600)^(ord i) <= 1 ->
  opnorm (mul2 (orbit_product (start i) z) (orbit_product j (orbit_shift (start i) z))) <= 2*K+1 /\
  opnorm (mul2 (F i) (orbit_product j (periodic_word (ord (S i))))) <= 2*K+1.
Proof.
  intros i j Hj Hsmall.
  assert (Href : opnorm (mul2 (F i) (orbit_product j (periodic_word (ord (S i))))) <= 2*K).
  { rewrite construction_periodic_orbit; eapply Rle_trans; [apply opnorm_submultiplicative|].
    apply Rmult_le_compat; try apply opnorm_nonnegative;
      [apply construction_reference_norm|apply construction_periodic_fiber_norm]. }
  pose proof (construction_cumulative_fiber_error i j Hj).
  pose proof (opnorm_from_difference
    (mul2 (orbit_product (start i) z) (orbit_product j (orbit_shift (start i) z)))
    (mul2 (F i) (orbit_product j (periodic_word (ord (S i)))))); split; lra.
Qed.
End Fibers.

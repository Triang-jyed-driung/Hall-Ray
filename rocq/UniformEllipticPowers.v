From Stdlib Require Import Reals Psatz Lia Arith Classical ClassicalChoice.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits ConcreteCocycle
  DefectLimit PeriodicReturns EllipticConjugacy EllipticRecurrence EllipticContinuity EllipticPowers
  CompactMatrices Matrix3Limits DaniCorrespondence SymbolicCoding SymbolicCocycle.
Open Scope R_scope.

Theorem uniform_elliptic_powers_bound : forall M c,
  c < 2 -> exists B, forall A k,
    det2 A = 1 -> opnorm A <= M -> Rabs (trace2 A) <= c -> opnorm (matrix_power A k) <= B.
Proof.
  intros M c Hc. apply NNPP; intro Hno.
  assert (Hchoose : forall n, exists p : mat2*nat,
    det2 (fst p) = 1 /\ opnorm (fst p) <= M /\ Rabs (trace2 (fst p)) <= c /\
    INR n < opnorm (matrix_power (fst p) (snd p))).
  { intro n; apply NNPP; intro Hnone; apply Hno; exists (INR n).
    intros A k HA HM Htrace.
    destruct (Rle_dec (opnorm (matrix_power A k)) (INR n)) as [Hyes|Hbad]; auto.
    exfalso; apply Hnone; exists (A,k); simpl; repeat split; try assumption; lra. }
  destruct (@choice nat (mat2*nat)%type _ Hchoose) as [p Hp].
  set (U := fun n => fst (p n)). set (ks := fun n => snd (p n)).
  destruct (bounded_matrix2_subsequence U M ltac:(intro n; exact (proj1 (proj2 (Hp n)))))
    as [ns [A [Hns Hcv]]].
  assert (HA : det2 A = 1) by (apply (unimodular_limit _ _ Hcv); intro i; exact (proj1 (Hp (ns i)))).
  assert (Hell : Rabs (trace2 A) < 2).
  { pose proof (matrix_cv_trace _ _ Hcv) as Htracecv.
    assert (Hrange : -c <= trace2 A <= c).
    { apply (scalar_limit_closed_interval _ _ (-c) c Htracecv); intro i.
      pose proof (proj1 (proj2 (proj2 (Hp (ns i))))) as Hb.
      change (Rabs (trace2 (U (ns i))) <= c) in Hb.
      pose proof (Rle_abs (trace2 (U (ns i)))); pose proof (Rle_abs (-trace2 (U (ns i)))).
      rewrite Rabs_Ropp in H0; lra. }
    apply Rabs_def1; lra. }
  pose proof (oriented_elliptic_basis_sequence_limit _ A Hcv HA Hell) as HGcv.
  destruct (convergent_matrix_norm_bounded _ _ HGcv) as [C [HC Hb]].
  destruct (convergent_matrix_norm_bounded _ _ (matrix_cv_adjugate _ _ HGcv)) as [D [HD Hd]].
  assert (Hpower : forall i, opnorm (matrix_power (U (ns i)) (ks (ns i))) <= C*D).
  { intro i.
    assert (HUi : det2 (U (ns i)) = 1) by exact (proj1 (Hp (ns i))).
    assert (HElli : Rabs (trace2 (U (ns i))) < 2).
    { pose proof (proj1 (proj2 (proj2 (Hp (ns i))))); change (Rabs (trace2 (U (ns i))) <= c) in H; lra. }
    destruct (oriented_elliptic_basis_valid (U (ns i)) HUi HElli) as [HG Horth].
    rewrite (any_conjugation_power_reconstruction (U (ns i)) (oriented_elliptic_basis (U (ns i))) (ks (ns i)) HG).
    pose proof (opnorm_submultiplicative (oriented_elliptic_basis (U (ns i)))
      (matrix_power (mul2 (mul2 (adj2 (oriented_elliptic_basis (U (ns i)))) (U (ns i)))
        (oriented_elliptic_basis (U (ns i)))) (ks (ns i)))) as Hinner.
    rewrite (orthogonal_opnorm _ (orthogonal_power _ _ Horth)) in Hinner.
    eapply Rle_trans; [apply opnorm_submultiplicative|].
    apply Rmult_le_compat; [apply opnorm_nonnegative|apply opnorm_nonnegative|specialize (Hb i); lra|apply Hd]. }
  destruct (natural_cast_cofinal (C*D)) as [N HN]. destruct (Hns N) as [I HI].
  specialize (HI I ltac:(lia)); pose proof (le_INR _ _ HI) as Hcast.
  specialize (Hpower I). pose proof (proj2 (proj2 (proj2 (Hp (ns I))))) as Hlarge.
  change (INR (ns I) < opnorm (matrix_power (U (ns I)) (ks (ns I)))) in Hlarge. lra.
Qed.

Lemma periodic_returns_norm_bound : forall n,
  opnorm (periodic_return n) <= constant_power_bound*opnorm defect_limit+2.
Proof.
  intro n. pose proof (periodic_return_asymptotic_bound n) as Herror.
  pose proof (pow_incr (1/500) 1 n ltac:(lra)) as Hpow; rewrite pow1 in Hpow.
  assert (Hmodel : opnorm (mul2 (matrix_power constant_return n) defect_limit) <=
    constant_power_bound*opnorm defect_limit).
  { eapply Rle_trans; [apply opnorm_submultiplicative|].
    apply Rmult_le_compat_r; [apply opnorm_nonnegative|apply constant_powers_uniformly_bounded]. }
  rewrite (matrix_difference_decomposition (periodic_return n) (mul2 (matrix_power constant_return n) defect_limit)).
  pose proof (opnorm_subadditive (sub2 (periodic_return n) (mul2 (matrix_power constant_return n) defect_limit))
    (mul2 (matrix_power constant_return n) defect_limit)); lra.
Qed.

Theorem periodic_fibers_uniform_trace_margin : forall c,
  c < 2 -> exists K, 1 <= K /\ forall n j,
    Rabs (trace2 (periodic_return n)) <= c ->
    opnorm (fiber_product j (periodic_future n))+
    opnorm (adj2 (fiber_product j (periodic_future n))) <= K.
Proof.
  intros c Hc.
  destruct (uniform_elliptic_powers_bound (constant_power_bound*opnorm defect_limit+2) c Hc) as [B HB].
  set (C := Rabs B+1).
  assert (HC : 0 < C) by (unfold C; pose proof (Rabs_pos B); lra).
  assert (HBC : B <= C) by (unfold C; pose proof (Rle_abs B); lra).
  exists (6*C*constant_power_bound+1); split.
  - pose proof constant_power_bound_nonnegative; nra.
  - intros n j Htrace.
    assert (Hpow : opnorm (matrix_power (periodic_return n) (j/S n)) <= C).
    { eapply Rle_trans; [apply HB; [apply periodic_return_unimodular|apply periodic_returns_norm_bound|exact Htrace]|exact HBC]. }
    assert (Hrem : (j mod S n <= n)%nat) by (pose proof (Nat.mod_upper_bound j (S n) ltac:(lia)); lia).
    pose proof (partial_period_uniform_bound n (j mod S n) Hrem) as Hr.
    assert (Hbound : opnorm (fiber_product j (periodic_future n)) <= 2*C*constant_power_bound).
    { rewrite periodic_product_remainder. eapply Rle_trans; [apply opnorm_submultiplicative|].
      replace (2*C*constant_power_bound) with (C*(2*constant_power_bound)) by ring.
      apply Rmult_le_compat; auto using opnorm_nonnegative. }
    pose proof (opnorm_adjugate_bound (fiber_product j (periodic_future n))); lra.
Qed.

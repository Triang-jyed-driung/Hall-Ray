From Stdlib Require Import Reals Psatz Lia Arith List ClassicalChoice.
From HallRay Require Import MatrixAlgebra EuclideanNorm SymbolicCoding SymbolicCocycle
  DefectLimit PeriodicReturns PeriodicHeights WordPrefixes PrefixFibers
  NestedWords BlockConstruction ConstructedWords ConstructedCodes ConstructedFibers ConstructedPeaks
  TwoSidedCoding LatticeReturns PeriodicWords ReturnBlocks BlockRealization
  Concatenation ScalarEstimates StableForgetting PaperTarget ApproximationRealization AdjustedPeriodicPeaks.
Import ListNotations.
Open Scope R_scope.

Theorem symbolic_height_ray : symbolic_height_ray_claim.
Proof.
  intro nm; exists (height_threshold nm); intros H HH.
  destruct (infinite_block_states nm H HH) as [delta [K [Hd [HK Hconstruct]]]].
  assert (Hrad := fun i : nat => constructed_block_comparison_radius nm H delta K Hd HK
    ((1/2)^i) (pow_lt (1/2) i ltac:(lra))).
  apply choice in Hrad; destruct Hrad as [tau Htau].
  destruct (Hconstruct tau (fun i => proj1 (Htau i)))
    as [states [Hinitial [Hindices [Hgood Hsteps]]]].
  exists (construction_word states).
  apply (block_controls_realize_height nm (construction_word states)
    (fun i => construction_start states (S i)) H (fun i => 3*(1/2)^i)).
  - intro i; apply (construction_starts_increase nm H delta K states Hindices Hsteps).
  - intros eps Heps; destruct (geometric_error_vanishes eps Heps) as [N HN].
    exists N; intros n Hn; rewrite Rabs_right.
    + apply HN; exact Hn.
    + apply Rle_ge,Rmult_le_pos; [lra|apply pow_le; lra].
  - intro i.
    assert (Hnonempty : state_prefix (states (S i)) <> []).
    { intro Hem; pose proof (proj1 (Hgood (S i))) as Hlen.
      rewrite Hindices,Hem in Hlen; cbn in Hlen; lia. }
    destruct (proj2 (proj2 (Hgood (S i)))) as [Hem|[Hbudget Htol]]; [contradiction|].
    rewrite Hindices in Htol.
    change ((1/600)^(construction_order states (S i)) < tau (S i)) in Htol.
    pose proof ((proj2 (Htau (S i))) tau states Hinitial Hindices Hgood Hsteps (S i) Htol) as Hclose.
    unfold constructed_block_close in Hclose.
    destruct (Hsteps (S i)) as [_ [_ [_ [_ [Hell [_ [Hpeak _]]]]]]].
    specialize (Hpeak Hell); rewrite Hindices in Hpeak.
    rewrite periodic_block_peak_returns in Hpeak
      by (exact (construction_repetitions_positive nm H delta K states Hindices Hsteps (S i))).
    change (Rabs (return_block_peak nm (periodic_word (construction_order states (S (S i))))
      (stage_fiber (construction_prefix states (S i)) (construction_order states (S i)))
      (construction_repetitions states (S (S i))*S (construction_order states (S (S i))))-H)
      < 2*(1/2)^(S i+3)) in Hpeak.
    set (a := return_block_peak nm
      (orbit_shift (construction_start states (S i)) (construction_word states))
      (orbit_product (construction_start states (S i)) (construction_word states))
      (construction_repetitions states (S (S i))*S (construction_order states (S (S i))))) in *.
    set (b := return_block_peak nm (periodic_word (construction_order states (S (S i))))
      (stage_fiber (construction_prefix states (S i)) (construction_order states (S i)))
      (construction_repetitions states (S (S i))*S (construction_order states (S (S i))))) in *.
    assert (Htri : Rabs (a-H) <= Rabs (a-b)+Rabs (b-H)).
    { replace (a-H) with ((a-b)+(b-H)) by ring; apply Rabs_triang. }
    replace (construction_start states (S (S i))-construction_start states (S i))%nat with
      (construction_repetitions states (S (S i))*S (construction_order states (S (S i))))%nat
      by (rewrite (construction_start_step nm H delta K states Hsteps (S i)); lia).
    replace (S i+3)%nat with (S (S (S (S i)))) in Hpeak by lia.
    cbn [pow] in Hclose,Hpeak.
    change (Rabs (a-H) <= 3*(1/2)^i).
    pose proof (pow_le (1/2) i ltac:(lra)); nra.
Qed.

Theorem hall_ray : hall_ray_claim.
Proof. apply hall_ray_from_symbolic_heights; exact symbolic_height_ray. Qed.

Print Assumptions hall_ray.

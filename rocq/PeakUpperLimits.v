From Stdlib Require Import Reals Psatz Lia Arith Classical ClassicalChoice.
From HallRay Require Import MatrixAlgebra ReturnIdentity FiberProducts EuclideanNorm MatrixLimits
  SymbolicCoding DefectLimit PeriodicReturns EllipticConjugacy EllipticContinuity
  TwoSidedCoding LatticeReturns PeriodicWords PeriodicOrbits PeriodicHeights
  LimitingConvergence CompactMatrices PositionalSubsequences PositionalLimits
  LimitingFamilies SegmentLimits PaperTarget SystoleCurves StableForgetting.
Open Scope R_scope.

Theorem elliptic_powers_in_circle : forall A,
  det2 A = 1 -> Rabs (trace2 A) < 2 -> forall k, in_elliptic_circle A (matrix_power A k).
Proof.
  intros A HA Hell k. induction k as [|k IH].
  - apply elliptic_circle_identity; assumption.
  - cbn [matrix_power]. apply elliptic_circle_product; try assumption.
    apply elliptic_return_in_circle; assumption.
Qed.

Theorem periodic_peak_near_segment : forall nm n X HX Hell eps,
  0 < eps -> exists j E t,
    (j <= n)%nat /\ in_elliptic_circle (periodic_return n) E /\
    0 <= t <= orbit_roof_time (orbit_shift j (periodic_word n)) /\
    periodic_peak nm n X HX Hell-eps <
      cusp_height nm (periodic_lifted_representative n j (mul2 X E) t).
Proof.
  intros nm n X HX Hell eps He.
  destruct (periodic_peak_near nm n X HX Hell eps He) as [s [Hs Hpeak]].
  destruct (periodic_height_forward_cover nm n X s HX Hs) as [k [j [t [Hj [Ht Hvalue]]]]].
  exists j, (matrix_power (periodic_return n) k), t. split; [exact Hj|]. split.
  - apply elliptic_powers_in_circle; [apply periodic_return_unimodular|exact Hell].
  - split; [lra|]. rewrite Hvalue in Hpeak. exact Hpeak.
Qed.

Theorem periodic_peaks_upper_limit : forall nm ns X Y S
  (HX : forall i, det2 (X i) = 1)
  (Hell : forall i, Rabs (trace2 (periodic_return (ns i))) < 2)
  (HY : det2 Y = 1) (HA : det2 (phase_limit_original S) = 1)
  (Hphase : Rabs (trace2 (phase_limit_original S)) < 2),
  indices_tend_to_infinity ns -> matrix_cv X Y ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  forall eps, 0 < eps -> exists I, forall i, (I <= i)%nat ->
    periodic_peak nm (ns i) (X i) (HX i) (Hell i) <
      limiting_peak nm Y (phase_limit_original S) HY HA Hphase+eps.
Proof.
  intros nm ns X Y S HX Hell HY HA Hphase Hns HXY HS eps He.
  set (D := limiting_peak nm Y (phase_limit_original S) HY HA Hphase).
  apply NNPP; intro Hno.
  assert (Hbad : arbitrarily_late (fun i => D+eps <= periodic_peak nm (ns i) (X i) (HX i) (Hell i))).
  { intro I. apply NNPP; intro Hnone. apply Hno. exists I; intros i Hi.
    destruct (Rlt_dec (periodic_peak nm (ns i) (X i) (HX i) (Hell i)) (D+eps)) as [Hyes|Hbad]; auto.
    exfalso; apply Hnone; exists i; split; [exact Hi|lra]. }
  destruct (arbitrarily_late_subsequence _ Hbad) as [ss [Hss Hbadss]].
  assert (Hchoice : forall i, exists p : nat*mat2*R,
    (fst (fst p) <= ns (ss i))%nat /\
    in_elliptic_circle (periodic_return (ns (ss i))) (snd (fst p)) /\
    0 <= snd p <= orbit_roof_time (orbit_shift (fst (fst p)) (periodic_word (ns (ss i)))) /\
    periodic_peak nm (ns (ss i)) (X (ss i)) (HX (ss i)) (Hell (ss i))-eps/2 <
      cusp_height nm (periodic_lifted_representative (ns (ss i)) (fst (fst p))
        (mul2 (X (ss i)) (snd (fst p))) (snd p))).
  { intro i. destruct (periodic_peak_near_segment nm (ns (ss i)) (X (ss i))
      (HX (ss i)) (Hell (ss i)) (eps/2) ltac:(lra)) as [j [E [t [Hj [HE [Ht Hvalue]]]]]].
    exists ((j,E),t); simpl; auto. }
  destruct (@choice nat (nat*mat2*R)%type _ Hchoice) as [p Hp].
  set (js := fun i => fst (fst (p i))).
  set (E := fun i => snd (fst (p i))).
  set (ts := fun i => snd (p i)).
  destruct (periodic_segment_family_upper_limit nm (fun i => ns (ss i)) js
    (fun i => X (ss i)) Y E ts S (cofinal_composition ns ss Hns Hss)
    ltac:(intro i; exact (proj1 (Hp i)))
    (matrix_cv_subsequence X Y ss HXY Hss) HY
    (matrix_cv_subsequence _ _ ss HS Hss) Hphase
    ltac:(intro i; exact (proj1 (proj2 (Hp i))))
    ltac:(intro i; exact (proj1 (proj2 (proj2 (Hp i))))))
    as [ks [L [Hks [Hfamily Hcv]]]].
  pose proof (limiting_peak_upper nm Y (phase_limit_original S) HY HA Hphase L Hfamily) as Hupper.
  change (cusp_height nm L <= D) in Hupper.
  destruct (Hcv (eps/4) ltac:(lra)) as [I HI].
  specialize (HI I ltac:(lia)).
  pose proof (proj2 (proj2 (proj2 (Hp (ks I))))) as Hlarge.
  change (periodic_peak nm (ns (ss (ks I))) (X (ss (ks I))) (HX (ss (ks I)))
    (Hell (ss (ks I)))-eps/2 < cusp_height nm
      (periodic_lifted_representative (ns (ss (ks I))) (js (ks I))
        (mul2 (X (ss (ks I))) (E (ks I))) (ts (ks I)))) in Hlarge.
  specialize (Hbadss (ks I)). unfold Rdist in HI; apply Rabs_def2 in HI; lra.
Qed.

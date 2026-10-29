From Stdlib Require Import Reals Psatz Lia.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  DefectLimit PeriodicReturns SymbolicCocycle PeriodicHeights
  AdjustedPeriodicPeaks UniformEllipticPowers PaperTarget.
Open Scope R_scope.

Theorem adjusted_periodic_blocks : forall nm H,
  height_threshold nm < H -> exists delta K, 0 < delta < 1 /\ 1 <= K /\
  forall X (HX : det2 X = 1), opnorm (sub2 X id2) <= delta ->
  forall eps N, 0 < eps -> exists n,
    (N <= n)%nat /\ Rabs (trace2 (periodic_return n)) < 2 /\
    (forall Hn, Rabs (periodic_peak nm n X HX Hn-H) < eps) /\
    forall j, opnorm (fiber_product j (periodic_future n))+
      opnorm (adj2 (fiber_product j (periodic_future n))) <= K.
Proof.
  intros nm H HH. destruct (adjusted_periodic_peak_choice nm H HH) as [delta [c [Hd [Hc Hchoice]]]].
  destruct (periodic_fibers_uniform_trace_margin c ltac:(lra)) as [K [HK Hbound]].
  exists delta,K; split; [exact Hd|]. split; [exact HK|].
  intros X HX HXclose eps N He.
  destruct (Hchoice X HX HXclose eps N He) as [n [Hn [Htrace Hpeak]]].
  exists n; split; [exact Hn|]. split; [lra|]. split; [exact Hpeak|].
  intro j; apply Hbound; lra.
Qed.

Theorem adjusted_repeated_block_choice : forall nm H,
  height_threshold nm < H -> exists delta K, 0 < delta < 1 /\ 1 <= K /\
  forall X (HX : det2 X = 1), opnorm (sub2 X id2) <= delta ->
  forall eps eta N L0, 0 < eps -> 0 < eta ->
  exists n L, (N <= n)%nat /\ (L0 <= L)%nat /\
    Rabs (trace2 (periodic_return n)) < 2 /\
    (forall j, opnorm (fiber_product j (periodic_future n))+
      opnorm (adj2 (fiber_product j (periodic_future n))) <= K) /\
    (forall Hn, Rabs (periodic_block_peak nm n X HX Hn L-H) < 2*eps) /\
    opnorm (sub2 (matrix_power (periodic_return n) L) id2) < eta.
Proof.
  intros nm H HH. destruct (adjusted_periodic_blocks nm H HH) as [delta [K [Hd [HK Hchoice]]]].
  exists delta,K; split; [exact Hd|]. split; [exact HK|].
  intros X HX HXclose eps eta N L0 Heps Heta.
  destruct (Hchoice X HX HXclose eps N Heps) as [n [Hn [Hell [Hpeak Hfibers]]]].
  destruct (periodic_repetition_choice nm n X HX Hell (Rmin eps eta) L0
    ltac:(apply Rmin_pos; assumption)) as [L [HL [Hmaximum Hnear]]].
  exists n,L; split; [exact Hn|]. split; [exact HL|]. split; [exact Hell|].
  split; [exact Hfibers|]. split.
  - intro Hproof.
    pose proof (Hpeak Hproof) as Htarget.
    rewrite (PeakContinuity.periodic_peak_unique_proofs nm n X HX HX Hell Hproof) in Hmaximum.
    assert (Hsame : periodic_block_peak nm n X HX Hell L = periodic_block_peak nm n X HX Hproof L).
    { destruct (periodic_block_peak_lub nm n X HX Hell L) as [Hb Hleast].
      destruct (periodic_block_peak_lub nm n X HX Hproof L) as [Hb' Hleast'].
      apply Rle_antisym; [apply Hleast|apply Hleast']; assumption. }
    rewrite Hsame in Hmaximum.
    pose proof (Rmin_l eps eta). apply Rabs_def2 in Hmaximum,Htarget.
    apply Rabs_def1; lra.
  - pose proof (Rmin_r eps eta); lra.
Qed.

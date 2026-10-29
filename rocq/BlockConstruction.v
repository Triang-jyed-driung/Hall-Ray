From Stdlib Require Import Reals Psatz Lia Arith List ClassicalChoice.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm MatrixLimits
  SymbolicCoding SymbolicCocycle DefectLimit PeriodicReturns PeriodicHeights
  WordPrefixes PrefixFibers BlockSelection AdjustedPeriodicPeaks.
Open Scope R_scope.
Import ListNotations.

Record block_state := BlockState {
  state_index : nat; state_prefix : list bool; state_order : nat; state_repetitions : nat
}.
Definition good_block_state delta (tau : nat -> R) s :=
  (state_index s <= length (state_prefix s))%nat /\
  opnorm (sub2 (stage_fiber (state_prefix s) (state_order s)) id2) <= fiber_budget delta (state_index s) /\
  (state_prefix s=[] \/
    (4*(1/600)^(state_order s) <= delta*(1/2)^(state_index s+2) /\
     (1/600)^(state_order s) < tau (state_index s))).

Definition block_step nm H delta K s t :=
  state_index t=S (state_index s) /\
  (state_order s < state_order t)%nat /\
  (S (state_index s) <= state_repetitions t)%nat /\
  state_prefix t=state_prefix s++repeated_return_word (state_order t) (state_repetitions t) /\
  Rabs (trace2 (periodic_return (state_order t))) < 2 /\
  (forall j, opnorm (fiber_product j (periodic_future (state_order t)))+
    opnorm (adj2 (fiber_product j (periodic_future (state_order t)))) <= K) /\
  (forall Hn, Rabs (periodic_block_peak nm (state_order t)
    (stage_fiber (state_prefix s) (state_order s)) (stage_fiber_unimodular _ _) Hn
    (state_repetitions t)-H) < 2*(1/2)^(state_index s+3)) /\
  opnorm (sub2 (matrix_power (periodic_return (state_order t)) (state_repetitions t)) id2) <
    delta*(1/2)^(state_index s+3).

Section Extension.
Variable nm : PaperTarget.planar_norm.
Variables H delta K : R.
Hypothesis Hd : 0 < delta < 1.
Hypothesis HK : 1 <= K.
Hypothesis select_block : forall X (HX : det2 X = 1), opnorm (sub2 X id2) <= delta ->
  forall eps eta N L0, 0 < eps -> 0 < eta -> exists n L,
    (N <= n)%nat /\ (L0 <= L)%nat /\ Rabs (trace2 (periodic_return n)) < 2 /\
    (forall j, opnorm (fiber_product j (periodic_future n))+opnorm (adj2 (fiber_product j (periodic_future n))) <= K) /\
    (forall Hn, Rabs (periodic_block_peak nm n X HX Hn L-H) < 2*eps) /\
    opnorm (sub2 (matrix_power (periodic_return n) L) id2) < eta.
Variable tau : nat -> R.
Hypothesis Htau : forall i, 0 < tau i.

Theorem extend_good_block_state : forall s,
  good_block_state delta tau s -> exists t, good_block_state delta tau t /\ block_step nm H delta K s t.
Proof.
  intros s [Hlength [Hbudget Hguard]].
  set (e := (1/2)^(state_index s+3)).
  assert (He : 0 < e) by (apply pow_lt; lra).
  assert (Heta : 0 < delta*e) by nra.
  set (g := Rmin (delta*e/4) (tau (S (state_index s)))).
  assert (Hg : 0 < g) by (apply Rmin_pos; [nra|apply Htau]).
  destruct (pow_lt_1_zero (1/600) ltac:(rewrite Rabs_right; lra) g Hg) as [N HN].
  assert (HF : opnorm (sub2 (stage_fiber (state_prefix s) (state_order s)) id2) <= delta).
  { pose proof (fiber_budget_within delta (state_index s) ltac:(lra)); lra. }
  destruct (select_block (stage_fiber (state_prefix s) (state_order s)) (stage_fiber_unimodular _ _) HF
    e (delta*e) (Nat.max N (S (state_order s))) (S (state_index s)) He Heta)
    as [n [L [Hn [HL [Hell [Hfibers [Hpeak Hterminal]]]]]]].
  assert (Hnew : (state_order s < n)%nat) by lia.
  specialize (HN n ltac:(lia)); rewrite Rabs_right in HN by (apply Rle_ge,pow_le; lra).
  assert (Hsmall : 4*(1/600)^n <= delta*e).
  { pose proof (Rmin_l (delta*e/4) (tau (S (state_index s)))); fold g in H0; lra. }
  assert (Htolerance : (1/600)^n < tau (S (state_index s))).
  { pose proof (Rmin_r (delta*e/4) (tau (S (state_index s)))); fold g in H0; lra. }
  exists (BlockState (S (state_index s)) (state_prefix s++repeated_return_word n L) n L).
  split.
  - unfold good_block_state; cbn [state_index state_prefix state_order state_repetitions]. split.
    + rewrite length_app,repeated_return_length; nia.
    + split.
      * apply (appended_stage_budget_step delta (state_index s) (state_prefix s) (state_order s) n L Hd ltac:(lia) Hbudget).
        -- unfold e in Hterminal; lra.
        -- tauto.
      * right. replace (S (state_index s)+2)%nat with (state_index s+3)%nat by lia.
        split; [exact Hsmall|exact Htolerance].
  - unfold block_step; cbn [state_index state_prefix state_order state_repetitions].
    repeat first [assumption|reflexivity|split].
Qed.
End Extension.

Definition initial_block_state := BlockState 0 [] 0 0.
Lemma initial_block_state_good : forall delta tau,
  good_block_state delta tau initial_block_state.
Proof.
  intros delta tau; unfold good_block_state,initial_block_state; simpl.
  rewrite empty_stage_fiber,opnorm_self_difference,fiber_budget_zero; repeat split; auto; lra.
Qed.

Fixpoint iterate_choice {A : Type} (f : A -> A) (a : A) (i : nat) :=
  match i with O => a | S j => f (iterate_choice f a j) end.

Theorem infinite_block_states : forall nm H,
  height_threshold nm < H -> exists delta K, 0 < delta < 1 /\ 1 <= K /\
  forall tau : nat -> R, (forall i, 0 < tau i) ->
  exists states : nat -> block_state,
    states 0%nat=initial_block_state /\
    (forall i, state_index (states i)=i) /\
    (forall i, good_block_state delta tau (states i)) /\
    forall i, block_step nm H delta K (states i) (states (S i)).
Proof.
  intros nm H HH; destruct (adjusted_repeated_block_choice nm H HH) as [delta [K [Hd [HK Hselect]]]].
  exists delta,K; split; [exact Hd|]. split; [exact HK|]. intros tau Htau.
  set (G := {s : block_state | good_block_state delta tau s}).
  assert (Hnext : forall g : G, exists h : G, block_step nm H delta K (proj1_sig g) (proj1_sig h)).
  { intro g. destruct (extend_good_block_state nm H delta K Hd Hselect tau Htau (proj1_sig g) (proj2_sig g))
      as [t [Ht Hstep]]. exists (exist _ t Ht); exact Hstep. }
  destruct (@choice G G (fun g h => block_step nm H delta K (proj1_sig g) (proj1_sig h)) Hnext) as [f Hf].
  set (g0 := (exist _ initial_block_state (initial_block_state_good delta tau) : G)).
  set (states := fun i => proj1_sig (iterate_choice f g0 i)).
  exists states; split; [reflexivity|].
  assert (Hsteps : forall i, block_step nm H delta K (states i) (states (S i))).
  { intro i; exact (Hf (iterate_choice f g0 i)). }
  split.
  - intro i; induction i as [|i IH]; [reflexivity|].
    pose proof (proj1 (Hsteps i)); lia.
  - split; [intro i; exact (proj2_sig (iterate_choice f g0 i))|exact Hsteps].
Qed.

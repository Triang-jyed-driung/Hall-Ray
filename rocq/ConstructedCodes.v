From Stdlib Require Import Reals Psatz Lia Arith List ZArith.
From HallRay Require Import SymbolicCoding SymbolicCocycle PeriodicReturns WordPrefixes PrefixFibers
  NestedWords BlockConstruction ConstructedWords BoundaryWords TwoSidedCoding LatticeReturns PeriodicWords.
Import ListNotations.
Open Scope R_scope.

Definition construction_word states := splice_word (fun _ => true) (construction_future states).

Section Codes.
Variable nm : PaperTarget.planar_norm.
Variables H delta K : R.
Variable tau : nat -> R.
Variable states : nat -> block_state.
Hypothesis initial : states 0%nat=initial_block_state.
Hypothesis indices : forall i, state_index (states i)=i.
Hypothesis good : forall i, good_block_state delta tau (states i).
Hypothesis steps : forall i, block_step nm H delta K (states i) (states (S i)).
Local Abbreviation xs := (construction_prefix states).
Local Abbreviation ord := (construction_order states).
Local Abbreviation reps := (construction_repetitions states).
Local Abbreviation start := (construction_start states).
Local Abbreviation z := (construction_word states).

Lemma construction_boundary_past : forall i k,
  (k < ord i)%nat ->
  z (Z.of_nat (start i)-1-Z.of_nat k)%Z = periodic_word (ord (S i)) (-1-Z.of_nat k)%Z.
Proof.
  intros [|i] k Hk.
  - unfold construction_order in Hk; rewrite initial in Hk; cbn in Hk; lia.
  - pose proof (construction_repetitions_positive nm H delta K states indices steps i) as HL.
    pose proof (construction_orders_increase nm H delta K states steps (S i)) as Hord.
    pose proof (construction_start_step nm H delta K states steps i) as Hr.
    assert (Hpast : (S k <= start (S i))%nat) by nia.
    replace (Z.of_nat (start (S i))-1-Z.of_nat k)%Z with (Z.of_nat (start (S i)-S k)) by lia.
    unfold construction_word; rewrite splice_nonnegative_symbol.
    unfold construction_future.
    rewrite (nested_future_symbol xs
      (construction_nested nm H delta K states steps)
      (construction_growing delta tau states indices good)
      (S i) (start (S i)-S k)%nat ltac:(unfold construction_start in *; lia)).
    rewrite (construction_append nm H delta K states steps i),app_nth2
      by (unfold construction_start in *; nia).
    replace (start (S i)-S k-length (xs i))%nat with
      (length (repeated_return_word (ord (S i)) (reps (S i)))-S k)%nat
      by (rewrite repeated_return_length; unfold construction_start in *; lia).
    rewrite repeated_return_suffix by lia.
    rewrite periodic_word_short_past by lia; reflexivity.
Qed.

Lemma construction_boundary_future : forall i t,
  (t < reps (S i)*S (ord (S i))+ord i)%nat ->
  z (Z.of_nat (start i)+Z.of_nat t)%Z = periodic_word (ord (S i)) (Z.of_nat t).
Proof.
  intros i t Ht. replace (Z.of_nat (start i)+Z.of_nat t)%Z with (Z.of_nat (start i+t)) by lia.
  unfold construction_word; rewrite splice_nonnegative_symbol.
  change (construction_future states (start i+t)%nat = future_of (periodic_word (ord (S i))) t).
  rewrite periodic_word_future.
  exact (construction_local_future_agreement nm H delta K tau states indices good steps i t Ht).
Qed.

Theorem construction_block_codes : forall i j,
  (j < reps (S i)*S (ord (S i)))%nat ->
  close ((2/5)*(1/900)^(ord i))
    (u_code (orbit_shift (start i+j) z)) (u_code (orbit_shift j (periodic_word (ord (S i))))) /\
  close ((2/5)*(1/900)^(ord i))
    (v_code (orbit_shift (start i+j) z)) (v_code (orbit_shift j (periodic_word (ord (S i))))).
Proof.
  intros i j Hj; split.
  - apply u_code_common_future.
    apply (shifted_window_future z (periodic_word (ord (S i))) (start i) (ord i)
      (reps (S i)*S (ord (S i)))); [apply construction_boundary_future|exact Hj].
  - apply v_code_common_past.
    apply (shifted_window_past z (periodic_word (ord (S i))) (start i) (ord i)
      (reps (S i)*S (ord (S i)))).
    + intros t Ht; apply construction_boundary_future; lia.
    + apply construction_boundary_past.
    + exact Hj.
Qed.
End Codes.

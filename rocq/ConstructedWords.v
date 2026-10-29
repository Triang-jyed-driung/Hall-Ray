From Stdlib Require Import Reals Psatz Lia Arith List FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm SymbolicCoding SymbolicCocycle
  DefectLimit PeriodicReturns WordPrefixes PrefixFibers NestedWords BlockConstruction.
Import ListNotations.
Open Scope R_scope.

Section Construction.
Variable nm : PaperTarget.planar_norm.
Variables H delta K : R.
Variable tau : nat -> R.
Variable states : nat -> block_state.
Hypothesis initial : states 0%nat=initial_block_state.
Hypothesis indices : forall i, state_index (states i)=i.
Hypothesis good : forall i, good_block_state delta tau (states i).
Hypothesis steps : forall i, block_step nm H delta K (states i) (states (S i)).

Definition construction_prefix i := state_prefix (states i).
Definition construction_order i := state_order (states i).
Definition construction_repetitions i := state_repetitions (states i).
Definition construction_start i := length (construction_prefix i).
Definition construction_future := nested_future construction_prefix.

Lemma construction_append : forall i,
  construction_prefix (S i)=construction_prefix i++
    repeated_return_word (construction_order (S i)) (construction_repetitions (S i)).
Proof. intro i; exact (proj1 (proj2 (proj2 (proj2 (steps i))))). Qed.
Lemma construction_orders_increase : forall i,
  (construction_order i < construction_order (S i))%nat.
Proof. intro i; exact (proj1 (proj2 (steps i))). Qed.
Lemma construction_repetitions_positive : forall i,
  (0 < construction_repetitions (S i))%nat.
Proof. intro i; pose proof (proj1 (proj2 (proj2 (steps i)))); rewrite indices in H0; unfold construction_repetitions; lia. Qed.
Lemma construction_nested : forall i, word_prefix (construction_prefix i) (construction_prefix (S i)).
Proof. intro i; eexists; apply construction_append. Qed.
Lemma construction_growing : forall i, (i <= length (construction_prefix i))%nat.
Proof. intro i; pose proof (proj1 (good i)); rewrite indices in H0; exact H0. Qed.
Lemma construction_start_zero : construction_start 0=0%nat.
Proof. unfold construction_start,construction_prefix; rewrite initial; reflexivity. Qed.
Lemma construction_start_step : forall i,
  construction_start (S i)=(construction_start i+
    construction_repetitions (S i)*S (construction_order (S i)))%nat.
Proof. intro i; unfold construction_start; rewrite construction_append,length_app,repeated_return_length; reflexivity. Qed.
Lemma construction_starts_increase : forall i, (construction_start i < construction_start (S i))%nat.
Proof. intro i; rewrite construction_start_step; pose proof (construction_repetitions_positive i); nia. Qed.

Theorem construction_future_block_agreement : forall i,
  same_prefix (construction_start (S i)+construction_order (S i)) construction_future
    (stage_future (construction_prefix i) (construction_order (S i))).
Proof.
  intro i. pose proof (nested_future_extra_a_agreement construction_prefix construction_nested construction_growing
    (S i) (construction_order (S i)) (construction_order (S (S i)))
    (construction_repetitions (S (S i))) (construction_append (S i))
    ltac:(pose proof (construction_orders_increase (S i)); lia)
    (construction_repetitions_positive (S i))) as Ha.
  rewrite construction_append,appended_stage_future in Ha.
  rewrite <- construction_append in Ha; exact Ha.
Qed.

Theorem construction_local_future_agreement : forall i,
  same_prefix (construction_repetitions (S i)*S (construction_order (S i))+construction_order i)
    (shift_by (construction_start i) construction_future) (periodic_future (construction_order (S i))).
Proof.
  intros i k Hk; unfold shift_by.
  pose proof (construction_orders_increase i) as Horder.
  pose proof (construction_future_block_agreement i (k+construction_start i)%nat
    ltac:(rewrite construction_start_step; lia)) as Ha.
  unfold stage_future in Ha; rewrite prepend_word_after in Ha by (unfold construction_start; lia).
  replace (k+construction_start i-length (construction_prefix i))%nat with k in Ha
    by (unfold construction_start; lia). rewrite Nat.add_comm; exact Ha.
Qed.

Theorem construction_prefix_fiber_error : forall i,
  opnorm (sub2 (fiber_product (construction_start i) construction_future)
    (stage_fiber (construction_prefix i) (construction_order i))) <=
  opnorm (stage_fiber (construction_prefix i) (construction_order i))*(1/600)^(construction_order i).
Proof.
  intro i; apply (nested_stage_fiber_error construction_prefix construction_nested construction_growing
    i (construction_order i) (construction_order (S i)) (construction_repetitions (S i))).
  - apply construction_append.
  - pose proof (construction_orders_increase i); lia.
  - apply construction_repetitions_positive.
Qed.

Theorem construction_local_fiber_error : forall i j,
  (j <= construction_repetitions (S i)*S (construction_order (S i)))%nat ->
  opnorm (sub2 (fiber_product j (shift_by (construction_start i) construction_future))
    (fiber_product j (periodic_future (construction_order (S i))))) <=
  opnorm (fiber_product j (periodic_future (construction_order (S i))))*(1/600)^(construction_order i).
Proof.
  intros i j Hj; apply symbolic_relative_absolute_bound.
  intros k Hk; apply construction_local_future_agreement; lia.
Qed.
End Construction.

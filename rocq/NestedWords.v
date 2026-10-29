From Stdlib Require Import Reals Psatz Lia Arith List.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm SymbolicCoding SymbolicCocycle
  DefectLimit PeriodicReturns WordPrefixes PrefixFibers LimitingConvergence.
Import ListNotations.
Open Scope R_scope.

Definition word_prefix (xs ys : list bool) := exists rest, ys=xs++rest.
Lemma word_prefix_reflexive : forall xs, word_prefix xs xs.
Proof. intro xs; exists []; rewrite app_nil_r; reflexivity. Qed.
Lemma word_prefix_transitive : forall xs ys zs,
  word_prefix xs ys -> word_prefix ys zs -> word_prefix xs zs.
Proof.
  intros xs ys zs [a Ha] [b Hb]; exists (a++b); rewrite Hb,Ha,app_assoc; reflexivity.
Qed.
Lemma word_prefix_length : forall xs ys, word_prefix xs ys -> (length xs <= length ys)%nat.
Proof. intros xs ys [r Hr]; rewrite Hr,length_app; lia. Qed.
Lemma word_prefix_nth : forall xs ys k,
  word_prefix xs ys -> (k < length xs)%nat -> nth k ys true = nth k xs true.
Proof. intros xs ys k [r Hr] Hk; rewrite Hr,app_nth1; auto. Qed.

Definition nested_future (xs : nat -> list bool) : future := fun k => nth k (xs (S k)) true.

Section NestedPrefixes.
Variable xs : nat -> list bool.
Hypothesis nested : forall i, word_prefix (xs i) (xs (S i)).
Hypothesis growing : forall i, (i <= length (xs i))%nat.

Lemma nested_prefix_monotone : forall i j, (i <= j)%nat -> word_prefix (xs i) (xs j).
Proof.
  intros i j Hij; induction Hij; [apply word_prefix_reflexive|].
  eapply word_prefix_transitive; [exact IHHij|apply nested].
Qed.

Theorem nested_future_symbol : forall i k,
  (k < length (xs i))%nat -> nested_future xs k = nth k (xs i) true.
Proof.
  intros i k Hk; unfold nested_future.
  destruct (le_dec i (S k)) as [Hsmall|Hlarge].
  - apply word_prefix_nth; [apply nested_prefix_monotone; exact Hsmall|exact Hk].
  - symmetry; apply word_prefix_nth.
    + apply nested_prefix_monotone; lia.
    + specialize (growing (S k)); lia.
Qed.

Theorem nested_future_prefix_agreement : forall i w,
  same_prefix (length (xs i)) (nested_future xs) (prepend_word (xs i) w).
Proof.
  intros i w k Hk; rewrite (nested_future_symbol i k Hk),prepend_word_before by exact Hk; reflexivity.
Qed.

Theorem nested_finite_stage_code_limit : forall ns,
  point_converges (fun i => coded (stage_future (xs i) (ns i))) (coded (nested_future xs)).
Proof.
  intro ns; apply (geometric_point_limit _ _ (fun i => length (xs i)) (2/5) (1/900)).
  - intros N; exists N; intros i Hi; specialize (growing i); lia.
  - lra.
  - lra.
  - exists 0%nat; intros i Hi; apply common_future_estimate.
    intros k Hk; symmetry; apply (nested_future_prefix_agreement i (periodic_future (ns i)) k Hk).
Qed.

Theorem nested_future_extra_a_agreement : forall i n m L,
  xs (S i)=xs i++repeated_return_word m L -> (n <= m)%nat -> (0 < L)%nat ->
  same_prefix (length (xs i)+n) (nested_future xs) (stage_future (xs i) n).
Proof.
  intros i n m L Hstep Hnm HL k Hk.
  assert (Hlen : (length (xs i)+n <= length (xs (S i)))%nat).
  { rewrite Hstep,length_app,repeated_return_length; nia. }
  rewrite (nested_future_symbol (S i) k ltac:(lia)).
  unfold stage_future. destruct (lt_dec k (length (xs i))) as [Hsmall|Hlarge].
  - rewrite prepend_word_before by exact Hsmall. apply word_prefix_nth; [apply nested|exact Hsmall].
  - rewrite prepend_word_after by lia. rewrite Hstep,app_nth2 by lia.
    assert (Hd : (k-length (xs i) < n)%nat) by lia.
    assert (Hperiodic : periodic_future n (k-length (xs i))%nat = true).
    { exact (periodic_initial_all_a n (k-length (xs i))%nat ltac:(lia)). }
    rewrite Hperiodic. destruct L as [|L]; [lia|].
    cbn [repeated_return_word]; rewrite app_nth1 by (rewrite return_word_length; lia).
    unfold return_word; rewrite app_nth1 by (rewrite repeat_length; lia).
    apply nth_repeat.
Qed.

Theorem nested_stage_fiber_error : forall i n m L,
  xs (S i)=xs i++repeated_return_word m L -> (n <= m)%nat -> (0 < L)%nat ->
  opnorm (sub2 (fiber_product (length (xs i)) (nested_future xs)) (stage_fiber (xs i) n)) <=
    opnorm (stage_fiber (xs i) n)*(1/600)^n.
Proof.
  intros i n m L Hstep Hnm HL; apply symbolic_relative_absolute_bound.
  apply (nested_future_extra_a_agreement i n m L Hstep Hnm HL).
Qed.
End NestedPrefixes.

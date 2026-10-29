From Stdlib Require Import Reals Psatz Lia Arith List FunctionalExtensionality.
From HallRay Require Import SymbolicCoding SymbolicCocycle PeriodicReturns.
Import ListNotations.

Fixpoint prepend_word (xs : list bool) (w : future) : future :=
  match xs with
  | [] => w
  | b::ys => fun k => match k with O => b | S j => prepend_word ys w j end
  end.

Lemma prepend_word_before : forall xs w k,
  (k < length xs)%nat -> prepend_word xs w k = nth k xs true.
Proof.
  induction xs as [|b xs IH]; intros w [|k] Hk; simpl in *; try lia; try reflexivity. apply IH; lia.
Qed.
Lemma prepend_word_after : forall xs w k,
  (length xs <= k)%nat -> prepend_word xs w k = w (k-length xs)%nat.
Proof.
  induction xs as [|b xs IH]; intros w [|k] Hk; simpl in *; try lia; try reflexivity.
  apply IH; lia.
Qed.
Lemma prepend_word_append : forall xs ys w,
  prepend_word (xs++ys) w = prepend_word xs (prepend_word ys w).
Proof.
  induction xs as [|b xs IH]; intros ys w; simpl; [reflexivity|].
  apply functional_extensionality; intros [|k]; [reflexivity|exact (f_equal (fun f => f k) (IH ys w))].
Qed.
Lemma prepend_word_shift : forall xs w,
  shift_by (length xs) (prepend_word xs w) = w.
Proof.
  intros xs w; apply functional_extensionality; intro k; unfold shift_by.
  rewrite prepend_word_after by lia; f_equal; lia.
Qed.

Lemma prepend_same_prefix : forall xs w v N,
  same_prefix N w v -> same_prefix (length xs+N) (prepend_word xs w) (prepend_word xs v).
Proof.
  intros xs w v N Hprefix k Hk.
  destruct (lt_dec k (length xs)) as [Hsmall|Hlarge].
  - rewrite !prepend_word_before by exact Hsmall; reflexivity.
  - rewrite !prepend_word_after by lia; apply Hprefix; lia.
Qed.
Lemma prepend_common_initial : forall xs w v,
  same_prefix (length xs) (prepend_word xs w) (prepend_word xs v).
Proof.
  intros xs w v k Hk; rewrite !prepend_word_before by exact Hk; reflexivity.
Qed.

Definition return_word n := repeat true n++[false].
Fixpoint repeated_return_word n L :=
  match L with O => [] | S k => return_word n++repeated_return_word n k end.
Lemma return_word_length : forall n, length (return_word n) = S n.
Proof. intro n; unfold return_word; rewrite length_app,repeat_length; simpl; lia. Qed.
Lemma repeated_return_length : forall n L,
  length (repeated_return_word n L) = (L*S n)%nat.
Proof.
  intros n L; induction L as [|L IH]; simpl; [reflexivity|].
  rewrite length_app,return_word_length,IH; lia.
Qed.
Lemma return_word_symbol : forall n k,
  (k < S n)%nat -> nth k (return_word n) true = periodic_future n k.
Proof.
  intros n k Hk; unfold return_word,periodic_future; rewrite Nat.mod_small by exact Hk.
  destruct (lt_dec k n) as [Hsmall|Hlarge].
  - rewrite app_nth1 by (rewrite repeat_length; lia).
    rewrite nth_repeat_lt by exact Hsmall.
    assert (Hneq : Nat.eqb k n = false) by (apply Nat.eqb_neq; lia).
    rewrite Hneq; reflexivity.
  - assert (Heq : k=n) by lia; subst k.
    rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length,Nat.sub_diag,Nat.eqb_refl; reflexivity.
Qed.
Lemma prepend_return_periodic : forall n,
  prepend_word (return_word n) (periodic_future n) = periodic_future n.
Proof.
  intro n; apply functional_extensionality; intro k.
  destruct (lt_dec k (S n)) as [Hsmall|Hlarge].
  - rewrite prepend_word_before by (rewrite return_word_length; exact Hsmall).
    apply return_word_symbol; exact Hsmall.
  - rewrite prepend_word_after by (rewrite return_word_length; lia).
    rewrite return_word_length.
    replace k with ((k-S n)+S n)%nat at 2 by lia.
    rewrite periodic_future_period; reflexivity.
Qed.
Lemma prepend_repeated_periodic : forall n L,
  prepend_word (repeated_return_word n L) (periodic_future n) = periodic_future n.
Proof.
  intros n L; induction L as [|L IH]; [reflexivity|].
  cbn [repeated_return_word]; rewrite prepend_word_append,IH,prepend_return_periodic; reflexivity.
Qed.

Lemma periodic_futures_common_a : forall n m N,
  (N <= n)%nat -> (N <= m)%nat -> same_prefix N (periodic_future n) (periodic_future m).
Proof.
  intros n m N Hn Hm k Hk.
  pose proof (periodic_initial_all_a n k ltac:(lia)) as H1.
  pose proof (periodic_initial_all_a m k ltac:(lia)) as H2.
  rewrite H1,H2; reflexivity.
Qed.
Lemma prepend_growing_periodic_common : forall xs n m,
  (n <= m)%nat -> same_prefix (length xs+n)
    (prepend_word xs (periodic_future n)) (prepend_word xs (periodic_future m)).
Proof.
  intros xs n m Hnm; apply prepend_same_prefix,periodic_futures_common_a; lia.
Qed.

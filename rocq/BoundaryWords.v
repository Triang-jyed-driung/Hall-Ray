From Stdlib Require Import Reals Psatz Lia Arith List ZArith.
From HallRay Require Import SymbolicCoding SymbolicCocycle PeriodicReturns WordPrefixes
  TwoSidedCoding LatticeReturns PeriodicWords.
Import ListNotations.

Lemma repeated_return_snoc : forall n L,
  repeated_return_word n (S L)=repeated_return_word n L++return_word n.
Proof.
  intros n L; induction L as [|L IH].
  - cbn [repeated_return_word]; rewrite app_nil_r; reflexivity.
  - change (return_word n++repeated_return_word n (S L)=
      (return_word n++repeated_return_word n L)++return_word n).
    rewrite IH,app_assoc; reflexivity.
Qed.

Lemma repeated_return_suffix : forall n L k,
  (0 < L)%nat -> (k < S n)%nat ->
  nth (length (repeated_return_word n L)-S k) (repeated_return_word n L) true =
    if Nat.eqb k 0 then false else true.
Proof.
  intros n [|L] k HL Hk; [lia|]. rewrite repeated_return_snoc.
  rewrite length_app,return_word_length.
  replace (length (repeated_return_word n L)+S n-S k)%nat with
    (length (repeated_return_word n L)+(n-k))%nat by lia.
  rewrite app_nth2 by lia.
  replace (length (repeated_return_word n L)+(n-k)-length (repeated_return_word n L))%nat
    with (n-k)%nat by lia.
  unfold return_word; destruct k as [|k].
  - rewrite Nat.sub_0_r,app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length,Nat.sub_diag; reflexivity.
  - rewrite app_nth1 by (rewrite repeat_length; lia); apply nth_repeat.
Qed.

Lemma periodic_word_short_past : forall n k,
  (k < S n)%nat -> periodic_word n (-1-Z.of_nat k)%Z =
    if Nat.eqb k 0 then false else true.
Proof.
  intros n k Hk; unfold periodic_word.
  assert (Hmod : ((-1-Z.of_nat k) mod Z.of_nat (S n))%Z=Z.of_nat (n-k)).
  { symmetry; apply Z.mod_unique with (q:=(-1)%Z); [left; lia|lia]. }
  rewrite Hmod. destruct k as [|k].
  - rewrite Nat.sub_0_r,Z.eqb_refl; reflexivity.
  - assert (Hneq : Z.eqb (Z.of_nat (n-S k)) (Z.of_nat n)=false)
      by (apply Z.eqb_neq; lia).
    rewrite Hneq; reflexivity.
Qed.

Lemma splice_nonnegative_symbol : forall p f k,
  splice_word p f (Z.of_nat k)=f k.
Proof.
  intros p f k; unfold splice_word; destruct (Z_le_gt_dec 0 (Z.of_nat k)); [rewrite Nat2Z.id; reflexivity|lia].
Qed.

Lemma shifted_window_future : forall z w r N B,
  (forall t, (t < B+N)%nat -> z (Z.of_nat r+Z.of_nat t)%Z=w (Z.of_nat t)) ->
  forall j, (j < B)%nat -> forall k, (k<N)%nat ->
  orbit_shift (r+j) z (Z.of_nat k)=orbit_shift j w (Z.of_nat k).
Proof.
  intros z w r N B Hwin j Hj k Hk; rewrite !orbit_shift_by_matches; unfold bi_shift_by.
  replace (Z.of_nat k+Z.of_nat (r+j))%Z with (Z.of_nat r+Z.of_nat (j+k))%Z by lia.
  replace (Z.of_nat k+Z.of_nat j)%Z with (Z.of_nat (j+k)) by lia.
  apply Hwin; lia.
Qed.

Lemma shifted_window_past : forall z w r N B,
  (forall t, (t < B)%nat -> z (Z.of_nat r+Z.of_nat t)%Z=w (Z.of_nat t)) ->
  (forall k, (k<N)%nat -> z (Z.of_nat r-1-Z.of_nat k)%Z=w (-1-Z.of_nat k)%Z) ->
  forall j, (j < B)%nat -> forall k, (k<N)%nat ->
  orbit_shift (r+j) z (-1-Z.of_nat k)%Z=orbit_shift j w (-1-Z.of_nat k)%Z.
Proof.
  intros z w r N B Hforward Hpast j Hj k Hk; rewrite !orbit_shift_by_matches; unfold bi_shift_by.
  destruct (le_dec (S k) j) as [Hpos|Hneg].
  - replace (-1-Z.of_nat k+Z.of_nat (r+j))%Z with (Z.of_nat r+Z.of_nat (j-S k))%Z by lia.
    replace (-1-Z.of_nat k+Z.of_nat j)%Z with (Z.of_nat (j-S k)) by lia.
    apply Hforward; lia.
  - replace (-1-Z.of_nat k+Z.of_nat (r+j))%Z with (Z.of_nat r-1-Z.of_nat (k-j))%Z by lia.
    replace (-1-Z.of_nat k+Z.of_nat j)%Z with (-1-Z.of_nat (k-j))%Z by lia.
    apply Hpast; lia.
Qed.

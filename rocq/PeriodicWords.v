From Stdlib Require Import Reals Psatz Lia Arith ZArith FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra SymbolicCoding SymbolicCocycle
  DefectLimit PeriodicReturns TwoSidedCoding LatticeReturns.
Open Scope R_scope.

Definition periodic_word (n : nat) : biword := fun k =>
  if Z.eqb (k mod Z.of_nat (S n)) (Z.of_nat n) then false else true.

Lemma natural_integer_eqb : forall a b,
  Z.eqb (Z.of_nat a) (Z.of_nat b) = Nat.eqb a b.
Proof.
  intros a b. destruct (Nat.eqb a b) eqn:H.
  - apply Nat.eqb_eq in H; subst; apply Z.eqb_refl.
  - apply Z.eqb_neq; apply Nat.eqb_neq in H; lia.
Qed.

Theorem periodic_word_future : forall n k,
  future_of (periodic_word n) k = periodic_future n k.
Proof.
  intros n k. unfold future_of, periodic_word, periodic_future.
  rewrite <- Nat2Z.inj_mod, natural_integer_eqb; reflexivity.
Qed.

Theorem periodic_word_period : forall n k,
  periodic_word n (k+Z.of_nat (S n))%Z = periodic_word n k.
Proof.
  intros n k; unfold periodic_word.
  replace (k+Z.of_nat (S n))%Z with (k+1*Z.of_nat (S n))%Z by ring.
  rewrite Z.mod_add by lia; reflexivity.
Qed.

Theorem periodic_word_return_shift : forall n,
  orbit_shift (S n) (periodic_word n) = periodic_word n.
Proof.
  intro n. apply functional_extensionality; intro k.
  rewrite orbit_shift_by_matches. apply periodic_word_period.
Qed.

Theorem periodic_word_return_product : forall n,
  orbit_product (S n) (periodic_word n) = periodic_return n.
Proof.
  intro n. rewrite orbit_product_matches_future.
  apply fiber_product_extensional; apply periodic_word_future.
Qed.

Lemma orbit_shift_add : forall n m z,
  orbit_shift (n+m) z = orbit_shift m (orbit_shift n z).
Proof.
  intros n m z; apply functional_extensionality; intro k.
  rewrite !orbit_shift_by_matches. unfold bi_shift_by. rewrite orbit_shift_by_matches.
  unfold bi_shift_by; f_equal; lia.
Qed.

Lemma orbit_time_add : forall n m z,
  orbit_time (n+m) z = orbit_time n z+orbit_time m (orbit_shift n z).
Proof.
  induction n; intros m z; [simpl; ring|].
  cbn [Nat.add orbit_time orbit_shift]. rewrite IHn; ring.
Qed.

Lemma orbit_product_add : forall n m z,
  orbit_product (n+m) z = mul2 (orbit_product n z) (orbit_product m (orbit_shift n z)).
Proof.
  induction n; intros m z; [simpl; rewrite mul2_id_left; reflexivity|].
  cbn [Nat.add orbit_product orbit_shift]. rewrite IHn, mul2_assoc; reflexivity.
Qed.

Section CyclicWord.
Variable z : biword.
Variable p : nat.
Hypothesis cyclic : orbit_shift p z = z.

Theorem cyclic_word_shifts : forall k, orbit_shift (k*p) z = z.
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite Nat.mul_succ_l, orbit_shift_add, IH; exact cyclic.
Qed.

Theorem cyclic_word_times : forall k,
  orbit_time (k*p) z = INR k*orbit_time p z.
Proof.
  induction k as [|k IH]; [simpl; ring|].
  rewrite Nat.mul_succ_l, orbit_time_add, cyclic_word_shifts, IH, S_INR; ring.
Qed.

Theorem cyclic_word_products : forall k,
  orbit_product (k*p) z = matrix_power (orbit_product p z) k.
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite Nat.mul_succ_l, orbit_product_add, cyclic_word_shifts, IH,
    matrix_power_successor_right; reflexivity.
Qed.

Theorem cyclic_word_position : forall k j,
  orbit_shift (k*p+j) z = orbit_shift j z /\
  orbit_time (k*p+j) z = INR k*orbit_time p z+orbit_time j z /\
  orbit_product (k*p+j) z =
    mul2 (matrix_power (orbit_product p z) k) (orbit_product j z).
Proof.
  intros k j. rewrite orbit_shift_add, orbit_time_add, orbit_product_add,
    cyclic_word_shifts, cyclic_word_times, cyclic_word_products. auto.
Qed.
End CyclicWord.

Definition periodic_word_time n := orbit_time (S n) (periodic_word n).

Theorem periodic_word_time_positive : forall n, 0 < periodic_word_time n.
Proof.
  intro n. pose proof (orbit_time_lower_bound (S n) (periodic_word n)).
  unfold periodic_word_time. rewrite S_INR in H. pose proof (pos_INR n); lra.
Qed.

Theorem periodic_word_iterates : forall n k j,
  orbit_shift (k*(S n)+j) (periodic_word n) = orbit_shift j (periodic_word n) /\
  orbit_time (k*(S n)+j) (periodic_word n) =
    INR k*periodic_word_time n+orbit_time j (periodic_word n) /\
  orbit_product (k*(S n)+j) (periodic_word n) =
    mul2 (matrix_power (periodic_return n) k) (orbit_product j (periodic_word n)).
Proof.
  intros n k j.
  pose proof (cyclic_word_position (periodic_word n) (S n)
    (periodic_word_return_shift n) k j) as H.
  rewrite periodic_word_return_product in H; exact H.
Qed.

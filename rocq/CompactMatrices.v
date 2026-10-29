From Stdlib Require Import Reals Psatz Lia Arith ClassicalChoice.
From HallRay Require Import MatrixAlgebra ReturnIdentity FiberProducts EuclideanNorm MatrixLimits
  LatticeBasis SymbolicCoding PeriodicReturns LimitingConvergence SystoleContinuity Matrix3Limits.
Open Scope R_scope.

Lemma cofinal_composition : forall ns ms,
  indices_tend_to_infinity ns -> indices_tend_to_infinity ms ->
  indices_tend_to_infinity (fun i => ns (ms i)).
Proof.
  intros ns ms Hn Hm N. destruct (Hn N) as [I HI]; destruct (Hm I) as [J HJ].
  exists J; intros i Hi; apply HI,HJ; exact Hi.
Qed.
Lemma scalar_cv_subsequence : forall u l ns,
  Un_cv u l -> indices_tend_to_infinity ns -> Un_cv (fun i => u (ns i)) l.
Proof.
  intros u l ns Hu Hns eps He. destruct (Hu eps He) as [N HN].
  destruct (Hns N) as [I HI]. exists I; intros i Hi; apply HN,HI; exact Hi.
Qed.
Lemma matrix_cv_subsequence : forall U L ns,
  matrix_cv U L -> indices_tend_to_infinity ns -> matrix_cv (fun i => U (ns i)) L.
Proof.
  intros U L ns HU Hns eps He. destruct (HU eps He) as [N HN].
  destruct (Hns N) as [I HI]. exists I; intros i Hi; apply HN,HI; exact Hi.
Qed.
Lemma matrix3_cv_subsequence : forall U L ns,
  matrix3_cv U L -> indices_tend_to_infinity ns -> matrix3_cv (fun i => U (ns i)) L.
Proof.
  intros U L ns HU Hns eps He. destruct (HU eps He) as [N HN].
  destruct (Hns N) as [I HI]. exists I; intros i Hi; apply HN,HI; exact Hi.
Qed.
Lemma point_cv_subsequence : forall U L ns,
  point_converges U L -> indices_tend_to_infinity ns -> point_converges (fun i => U (ns i)) L.
Proof.
  intros U L ns [H1 H2] Hns; split.
  - exact (scalar_cv_subsequence _ _ ns H1 Hns).
  - exact (scalar_cv_subsequence _ _ ns H2 Hns).
Qed.

Theorem bounded_real_subsequence : forall u M,
  (forall n, Rabs (u n) <= M) ->
  exists ns l, indices_tend_to_infinity ns /\ Un_cv (fun i => u (ns i)) l.
Proof.
  intros u M Hb.
  destruct (Bolzano_Weierstrass u (fun x => -M <= x <= M) (compact_P3 (-M) M)
    ltac:(intro n; specialize (Hb n); pose proof (Rle_abs (u n));
      pose proof (Rle_abs (-u n)); rewrite Rabs_Ropp in *; lra)) as [l Hl].
  assert (Hchoice : forall i, exists n, (i <= n)%nat /\ Rabs (u n-l) < (1/2)^i).
  { intro i. apply (Hl (fun x => Rabs (x-l) < (1/2)^i) i).
    exists (mkposreal ((1/2)^i) ltac:(apply pow_lt; lra)). intros x Hx; exact Hx. }
  destruct (@choice nat nat (fun i n => (i <= n)%nat /\ Rabs (u n-l) < (1/2)^i) Hchoice)
    as [ns Hns].
  exists ns,l; split.
  - intros N. exists N; intros i Hi; specialize (Hns i); lia.
  - intros eps He.
    destruct (pow_lt_1_zero (1/2) ltac:(rewrite Rabs_right; lra) eps He) as [N HN].
    exists N; intros i Hi. specialize (HN i Hi); specialize (Hns i).
    rewrite Rabs_right in HN by (apply Rle_ge, pow_le; lra). unfold Rdist; lra.
Qed.

Theorem finite_coordinates_subsequence : forall d (U : nat -> nat -> R) M,
  (forall n j, (j < d)%nat -> Rabs (U n j) <= M) ->
  exists ns L, indices_tend_to_infinity ns /\
    forall j, (j < d)%nat -> Un_cv (fun i => U (ns i) j) (L j).
Proof.
  induction d as [|d IH]; intros U M Hb.
  - exists (fun n => n), (fun _ => 0). split.
    + intros N; exists N; auto.
    + intros j Hj; lia.
  - destruct (IH U M ltac:(intros; apply Hb; lia)) as [ns [L [Hns HL]]].
    destruct (bounded_real_subsequence (fun i => U (ns i) d) M ltac:(intro i; apply Hb; lia))
      as [ms [l [Hms Hlast]]].
    exists (fun i => ns (ms i)), (fun j => if Nat.eq_dec j d then l else L j).
    split; [apply cofinal_composition; assumption|]. intros j Hj.
    destruct (Nat.eq_dec j d) as [Hsame|Hdiff].
    + subst j; exact Hlast.
    + exact (scalar_cv_subsequence (fun i => U (ns i) j) (L j) ms (HL j ltac:(lia)) Hms).
Qed.

Definition matrix2_coordinate (A : mat2) j :=
  match j with O => a11 A | S O => a12 A | S (S O) => a21 A | _ => a22 A end.

Theorem bounded_matrix2_subsequence : forall U M,
  (forall n, opnorm (U n) <= M) ->
  exists ns L, indices_tend_to_infinity ns /\ matrix_cv (fun i => U (ns i)) L.
Proof.
  intros U M Hb.
  destruct (finite_coordinates_subsequence 4 (fun n j => matrix2_coordinate (U n) j) M
    ltac:(intros n j Hj; pose proof (opnorm_entries (U n)); specialize (Hb n);
      destruct j as [|[|[|[|j]]]]; simpl; try lia; lra)) as [ns [L [Hns HL]]].
  exists ns, (Mat2 (L 0%nat) (L 1%nat) (L 2%nat) (L 3%nat)); split; [exact Hns|].
  apply coordinates_matrix_cv. repeat split.
  - exact (HL 0%nat ltac:(lia)).
  - exact (HL 1%nat ltac:(lia)).
  - exact (HL 2%nat ltac:(lia)).
  - exact (HL 3%nat ltac:(lia)).
Qed.

Definition matrix3_coordinate (A : mat3) j :=
  match j with
  | O => b11 A | S O => b12 A | S (S O) => b13 A
  | S (S (S O)) => b21 A | S (S (S (S O))) => b22 A
  | S (S (S (S (S O)))) => b23 A | S (S (S (S (S (S O))))) => b31 A
  | S (S (S (S (S (S (S O)))))) => b32 A | _ => b33 A end.

Theorem bounded_matrix3_subsequence : forall U M,
  (forall n, entries_bounded3 (U n) M) ->
  exists ns L, indices_tend_to_infinity ns /\ matrix3_cv (fun i => U (ns i)) L.
Proof.
  intros U M Hb.
  destruct (finite_coordinates_subsequence 9 (fun n j => matrix3_coordinate (U n) j) M
    ltac:(intros n j Hj; specialize (Hb n); unfold entries_bounded3 in Hb;
      destruct j as [|[|[|[|[|[|[|[|[|j]]]]]]]]]; simpl; try lia; tauto))
    as [ns [L [Hns HL]]].
  exists ns, (Mat3 (L 0%nat) (L 1%nat) (L 2%nat) (L 3%nat) (L 4%nat)
    (L 5%nat) (L 6%nat) (L 7%nat) (L 8%nat)); split; [exact Hns|].
  apply coordinates_matrix3_cv. repeat split.
  - exact (HL 0%nat ltac:(lia)).
  - exact (HL 1%nat ltac:(lia)).
  - exact (HL 2%nat ltac:(lia)).
  - exact (HL 3%nat ltac:(lia)).
  - exact (HL 4%nat ltac:(lia)).
  - exact (HL 5%nat ltac:(lia)).
  - exact (HL 6%nat ltac:(lia)).
  - exact (HL 7%nat ltac:(lia)).
  - exact (HL 8%nat ltac:(lia)).
Qed.

Theorem matrix3_cv_determinant : forall U L,
  matrix3_cv U L -> Un_cv (fun i => det3 (U i)) (det3 L).
Proof.
  intros U L HU. apply matrix3_cv_coordinates in HU.
  destruct HU as (H11&H12&H13&H21&H22&H23&H31&H32&H33).
  unfold det3; scalar_cv_algebra.
Qed.
Theorem unimodular3_limit : forall U L,
  matrix3_cv U L -> (forall n, det3 (U n) = 1) -> det3 L = 1.
Proof.
  intros U L HU Hd. apply (UL_sequence (fun n => det3 (U n)) (det3 L) 1).
  - apply matrix3_cv_determinant; exact HU.
  - intros eps He. exists 0%nat; intros n Hn. unfold Rdist; rewrite Hd.
    replace (1-1) with 0 by ring; rewrite Rabs_R0; exact He.
Qed.

Theorem bounded_unimodular3_subsequence : forall U M,
  (forall n, det3 (U n) = 1) -> (forall n, entries_bounded3 (U n) M) ->
  exists ns L, indices_tend_to_infinity ns /\ det3 L = 1 /\ matrix3_cv (fun i => U (ns i)) L.
Proof.
  intros U M Hd Hb. destruct (bounded_matrix3_subsequence U M Hb) as [ns [L [Hns HL]]].
  exists ns,L; split; [exact Hns|]. split; [apply (unimodular3_limit _ _ HL); exact (fun i => Hd (ns i))|exact HL].
Qed.

Lemma matrix_cv_constant : forall A, matrix_cv (fun _ => A) A.
Proof.
  intro A. apply coordinates_matrix_cv. repeat split; apply real_constant_cv.
Qed.
Lemma matrix_cv_transpose : forall U L,
  matrix_cv U L -> matrix_cv (fun i => transpose2 (U i)) (transpose2 L).
Proof.
  intros U L HU. apply matrix_cv_coordinates in HU.
  destruct HU as (H11&H12&H21&H22). apply coordinates_matrix_cv.
  repeat split; assumption.
Qed.

Theorem orthogonal2_limit : forall U L,
  matrix_cv U L -> (forall n, orthogonal2 (U n)) -> orthogonal2 L.
Proof.
  intros U L HU Ho.
  pose proof (matrix_cv_product (fun n => transpose2 (U n)) U (transpose2 L) L
    (matrix_cv_transpose U L HU) HU) as Hproduct.
  assert (Hconstant : matrix_cv (fun n => mul2 (transpose2 (U n)) (U n)) id2).
  { intros eps He. destruct (matrix_cv_constant id2 eps He) as [N HN].
    exists N; intros n Hn. rewrite Ho. exact (HN n Hn). }
  exact (matrix_cv_unique _ _ _ Hproduct Hconstant).
Qed.

Theorem special_orthogonal_subsequence : forall U,
  (forall n, det2 (U n) = 1) -> (forall n, orthogonal2 (U n)) ->
  exists ns L, indices_tend_to_infinity ns /\ det2 L = 1 /\ orthogonal2 L /\ matrix_cv (fun i => U (ns i)) L.
Proof.
  intros U Hd Ho.
  destruct (bounded_matrix2_subsequence U 1
    ltac:(intro n; rewrite orthogonal_opnorm by apply Ho; lra)) as [ns [L [Hns HL]]].
  exists ns,L; split; [exact Hns|]. split.
  - apply (unimodular_limit _ _ HL); exact (fun i => Hd (ns i)).
  - split; [apply (orthogonal2_limit _ _ HL); exact (fun i => Ho (ns i))|exact HL].
Qed.

Lemma scalar_limit_closed_interval : forall u l a b,
  Un_cv u l -> (forall n, a <= u n <= b) -> a <= l <= b.
Proof.
  intros u l a b Hu Hb. split.
  - destruct (Rle_dec a l) as [Hyes|Hno]; auto.
    destruct (Hu ((a-l)/2) ltac:(lra)) as [N HN].
    specialize (HN N ltac:(lia)); specialize (Hb N).
    unfold Rdist in HN; apply Rabs_def2 in HN; lra.
  - destruct (Rle_dec l b) as [Hyes|Hno]; auto.
    destruct (Hu ((l-b)/2) ltac:(lra)) as [N HN].
    specialize (HN N ltac:(lia)); specialize (Hb N).
    unfold Rdist in HN; apply Rabs_def2 in HN; lra.
Qed.

Theorem bounded_matrix_real_subsequence : forall U v M C,
  (forall n, opnorm (U n) <= M) -> (forall n, Rabs (v n) <= C) ->
  exists ns L l, indices_tend_to_infinity ns /\
    matrix_cv (fun i => U (ns i)) L /\ Un_cv (fun i => v (ns i)) l.
Proof.
  intros U v M C HU Hv.
  destruct (bounded_matrix2_subsequence U M HU) as [ns [L [Hns HL]]].
  destruct (bounded_real_subsequence (fun i => v (ns i)) C (fun i => Hv (ns i)))
    as [ms [l [Hms Hl]]].
  exists (fun i => ns (ms i)), L, l; split; [apply cofinal_composition; assumption|].
  split; [exact (matrix_cv_subsequence _ _ ms HL Hms)|exact Hl].
Qed.

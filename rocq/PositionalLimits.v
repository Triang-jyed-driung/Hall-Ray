From Stdlib Require Import Reals Psatz Lia Arith FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra ReturnIdentity FiberProducts EuclideanNorm MatrixLimits
  SymbolicCoding SymbolicCocycle DefectLimit PeriodicReturns EllipticConjugacy
  TwoSidedCoding LatticeReturns PeriodicWords LimitingWords LimitingFibers LimitingConvergence
  Matrix3Limits CompactMatrices PositionalSubsequences LimitingRepresentatives
  PaperTarget SystoleCurves.
Open Scope R_scope.

Definition periodic_lifted_representative n j E t :=
  mul3 (diagonal_flow t) (orbit_frame (orbit_shift j (periodic_word n))
    (mul2 E (orbit_product j (periodic_word n)))).

Definition positional_limit_model F P t L : Prop :=
  (exists j, L = beginning_representative F j t) \/
  (exists r, L = ending_representative (mul2 F P) r t) \/
  (exists S, det2 S = 1 /\ orthogonal2 S /\ L = bulk_representative F S t).

Theorem periodic_positions_have_model_limits : forall ns js E F ts t S,
  indices_tend_to_infinity ns -> (forall i, (js i <= ns i)%nat) ->
  matrix_cv E F -> Un_cv ts t ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  exists ks L, indices_tend_to_infinity ks /\
    matrix3_cv (fun i => periodic_lifted_representative (ns (ks i)) (js (ks i))
      (E (ks i)) (ts (ks i))) L /\
    positional_limit_model F (phase_limit_original S) t L.
Proof.
  intros ns js E F ts t S Hns Hle HE Ht HS.
  pose proof (periodic_returns_matrix_limit ns S Hns HS) as HP.
  destruct (periodic_positions_subsequence ns js) as [ks [Hks [Hbegin|[Hend|Hbulk]]]].
  - destruct Hbegin as [j Hj].
    exists ks, (beginning_representative F j t); split; [exact Hks|]. split.
    + assert (Hsame : (fun i => periodic_lifted_representative (ns (ks i)) (js (ks i))
        (E (ks i)) (ts (ks i))) =
        (fun i => mul3 (diagonal_flow (ts (ks i)))
          (orbit_frame (orbit_shift j (periodic_word (ns (ks i))))
            (mul2 (E (ks i)) (orbit_product j (periodic_word (ns (ks i)))))))).
      { apply functional_extensionality; intro i. unfold periodic_lifted_representative; rewrite Hj; reflexivity. }
      rewrite Hsame. apply beginning_representative_limit.
      * apply cofinal_composition; assumption.
      * exact (matrix_cv_subsequence E F ks HE Hks).
      * exact (scalar_cv_subsequence ts t ks Ht Hks).
    + left; exists j; reflexivity.
  - destruct Hend as [r Hr].
    assert (Hposition : forall i, js (ks i) = (ns (ks i)-r)%nat).
    { intro i. specialize (Hle (ks i)); specialize (Hr i); lia. }
    exists ks, (ending_representative (mul2 F (phase_limit_original S)) r t).
    split; [exact Hks|]. split.
    + assert (Hsame : (fun i => periodic_lifted_representative (ns (ks i)) (js (ks i))
        (E (ks i)) (ts (ks i))) =
        (fun i => mul3 (diagonal_flow (ts (ks i)))
          (orbit_frame (orbit_shift (ns (ks i)-r) (periodic_word (ns (ks i))))
            (mul2 (mul2 (E (ks i)) (periodic_return (ns (ks i))))
              (adj2 (orbit_product (Nat.succ r) (orbit_shift (ns (ks i)-r) (periodic_word (ns (ks i)))))))))).
      { apply functional_extensionality; intro i. unfold periodic_lifted_representative.
        rewrite (periodic_prefix_from_suffix (ns (ks i)) (js (ks i)) r ltac:(specialize (Hle (ks i)); specialize (Hr i); lia)).
        rewrite Hposition, mul2_assoc; reflexivity. }
      rewrite Hsame. apply ending_representative_limit.
      * apply cofinal_composition; assumption.
      * apply matrix_cv_product.
        -- exact (matrix_cv_subsequence E F ks HE Hks).
        -- exact (matrix_cv_subsequence _ _ ks HP Hks).
      * exact (scalar_cv_subsequence ts t ks Ht Hks).
    + right; left; exists r; reflexivity.
  - destruct Hbulk as [Hjs Hremaining].
    destruct (special_orthogonal_subsequence (fun i => matrix_power constant_rotation (js (ks i)))
      ltac:(intro i; apply matrix_power_unimodular; exact (proj1 constant_rotation_special_orthogonal))
      ltac:(intro i; apply orthogonal_power; exact (proj2 constant_rotation_special_orthogonal)))
      as [ms [R [Hms [HRdet [HRorth HRcv]]]]].
    exists (fun i => ks (ms i)), (bulk_representative F R t).
    split; [apply cofinal_composition; assumption|]. split.
    + apply bulk_representative_limit.
      * intro i; apply Hle.
      * exact (cofinal_composition (fun i => js (ks i)) ms Hjs Hms).
      * exact (cofinal_composition (fun i => (ns (ks i)-js (ks i))%nat) ms Hremaining Hms).
      * exact HRcv.
      * exact (matrix_cv_subsequence E F (fun i => ks (ms i)) HE (cofinal_composition ks ms Hks Hms)).
      * exact (scalar_cv_subsequence ts t (fun i => ks (ms i)) Ht (cofinal_composition ks ms Hks Hms)).
    + right; right; exists R; auto.
Qed.

Lemma positional_limit_model_unimodular : forall F P t L,
  det2 F = 1 -> det2 P = 1 -> positional_limit_model F P t L -> det3 L = 1.
Proof.
  intros F P t L HF HP [[j Hj]|[[r Hr]|[S [HS [Horth Hbulk]]]]]; subst L.
  - apply beginning_representative_unimodular; exact HF.
  - apply ending_representative_unimodular; rewrite det2_mul, HF, HP; ring.
  - apply bulk_representative_unimodular; assumption.
Qed.

Theorem periodic_position_heights_have_model_limits : forall nm ns js E F ts t S,
  indices_tend_to_infinity ns -> (forall i, (js i <= ns i)%nat) ->
  matrix_cv E F -> det2 F = 1 -> Un_cv ts t ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  exists ks L, indices_tend_to_infinity ks /\
    positional_limit_model F (phase_limit_original S) t L /\ det3 L = 1 /\
    Un_cv (fun i => cusp_height nm (periodic_lifted_representative (ns (ks i)) (js (ks i))
      (E (ks i)) (ts (ks i)))) (cusp_height nm L).
Proof.
  intros nm ns js E F ts t S Hns Hle HE HF Ht HS.
  destruct (periodic_positions_have_model_limits ns js E F ts t S Hns Hle HE Ht HS)
    as [ks [L [Hks [HL Hmodel]]]].
  assert (HP : det2 (phase_limit_original S) = 1).
  { apply (unimodular_limit (fun i => periodic_return (ns i)) _
      (periodic_returns_matrix_limit ns S Hns HS)); intro i; apply periodic_return_unimodular. }
  assert (Hdet := positional_limit_model_unimodular F (phase_limit_original S) t L HF HP Hmodel).
  exists ks,L; split; [exact Hks|]. split; [exact Hmodel|]. split; [exact Hdet|].
  apply cusp_height_sequence_limit; assumption.
Qed.

Theorem bounded_periodic_positions_compact : forall nm ns js E ts S M C,
  indices_tend_to_infinity ns -> (forall i, (js i <= ns i)%nat) ->
  (forall i, det2 (E i) = 1) -> (forall i, opnorm (E i) <= M) ->
  (forall i, Rabs (ts i) <= C) ->
  matrix_cv (fun i => matrix_power constant_rotation (ns i)) S ->
  exists ks F t L, indices_tend_to_infinity ks /\ det2 F = 1 /\ det3 L = 1 /\
    matrix_cv (fun i => E (ks i)) F /\ Un_cv (fun i => ts (ks i)) t /\
    positional_limit_model F (phase_limit_original S) t L /\
    Un_cv (fun i => cusp_height nm (periodic_lifted_representative (ns (ks i)) (js (ks i))
      (E (ks i)) (ts (ks i)))) (cusp_height nm L).
Proof.
  intros nm ns js E ts S M C Hns Hle HE HM HC HS.
  destruct (bounded_matrix_real_subsequence E ts M C HM HC)
    as [ms [F [t [Hms [HF Ht]]]]].
  assert (HFdet : det2 F = 1) by (apply (unimodular_limit _ _ HF); exact (fun i => HE (ms i))).
  destruct (periodic_position_heights_have_model_limits nm
    (fun i => ns (ms i)) (fun i => js (ms i)) (fun i => E (ms i)) F
    (fun i => ts (ms i)) t S
    (cofinal_composition ns ms Hns Hms) (fun i => Hle (ms i)) HF HFdet Ht
    (matrix_cv_subsequence _ _ ms HS Hms))
    as [rs [L [Hrs [Hmodel [HL Hheight]]]]].
  exists (fun i => ms (rs i)), F,t,L. split; [apply cofinal_composition; assumption|].
  split; [exact HFdet|]. split; [exact HL|]. split.
  - exact (matrix_cv_subsequence _ _ rs HF Hrs).
  - split; [exact (scalar_cv_subsequence _ _ rs Ht Hrs)|]. split; assumption.
Qed.

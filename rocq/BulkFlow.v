From Stdlib Require Import Reals Psatz Lia FunctionalExtensionality.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices FiberProducts
  EuclideanNorm MatrixLimits SymbolicCoding SymbolicCocycle DefectLimit PeriodicReturns
  EllipticConjugacy EllipticContinuity TwoSidedCoding LatticeReturns LatticeBasis LatticeOrbit
  LimitingWords LimitingRepresentatives LimitingFamilies LatticeSystole SystoleCurves.
Open Scope R_scope.

Lemma constant_word_shift : forall j, orbit_shift j constant_word = constant_word.
Proof.
  intro j; apply functional_extensionality; intro k.
  rewrite orbit_shift_by_matches; reflexivity.
Qed.
Lemma constant_word_products : forall j,
  orbit_product j constant_word = matrix_power constant_return j.
Proof.
  intro j. rewrite orbit_product_matches_future, <- constant_future_product.
  apply fiber_product_extensional; reflexivity.
Qed.

Definition constant_fiber_rotation R := mul2 (mul2 constant_basis R) (adj2 constant_basis).

Lemma constant_fiber_rotation_product : forall R j,
  mul2 (constant_fiber_rotation R) (matrix_power constant_return j) =
    constant_fiber_rotation (mul2 R (matrix_power constant_rotation j)).
Proof.
  intros R j; unfold constant_fiber_rotation. rewrite constant_power_reconstruction.
  apply conjugated_circle_product, constant_basis_unimodular.
Qed.

Theorem bulk_forward_flow_cover : forall X A E R t,
  in_elliptic_circle A E -> det2 R = 1 -> orthogonal2 R -> 0 <= t ->
  exists L, limiting_representative X A L /\
    same_lattice (mul3 (diagonal_flow t) (bulk_representative (mul2 X E) R 0)) L.
Proof.
  intros X A E R t HE HRd HRo Ht.
  unfold bulk_representative. rewrite diagonal_flow_zero,mul3_id_left.
  destruct (complete_lattice_orbit_cover constant_word
    (mul2 (mul2 X E) (constant_fiber_rotation R)) t Ht) as [j [r [Hr Hsame]]].
  rewrite constant_word_shift in Hr,Hsame. rewrite constant_word_products in Hsame.
  rewrite (mul2_assoc (mul2 X E) (constant_fiber_rotation R) (matrix_power constant_return j)),
    constant_fiber_rotation_product in Hsame.
  exists (bulk_representative (mul2 X E) (mul2 R (matrix_power constant_rotation j)) r).
  split; [|exact Hsame]. apply limiting_bulk; try assumption.
  - rewrite det2_mul,HRd,matrix_power_unimodular; [ring|exact (proj1 constant_rotation_special_orthogonal)].
  - apply orthogonal_product; [exact HRo|apply orthogonal_power; exact (proj2 constant_rotation_special_orthogonal)].
  - lra.
Qed.

Theorem limiting_peak_bounds_bulk_flow : forall nm X A HX HA Hell E R t,
  in_elliptic_circle A E -> det2 R = 1 -> orthogonal2 R -> 0 <= t ->
  cusp_height nm (mul3 (diagonal_flow t) (bulk_representative (mul2 X E) R 0)) <=
    limiting_peak nm X A HX HA Hell.
Proof.
  intros nm X A HX HA Hell E R t HE HRd HRo Ht.
  destruct (bulk_forward_flow_cover X A E R t HE HRd HRo Ht) as [L [HL Hsame]].
  eapply Rle_trans; [|apply limiting_peak_upper; exact HL].
  unfold cusp_height. apply Req_le. f_equal. apply systole_same_lattice.
  - rewrite mul3_determinant,diagonal_flow_unimodular.
    rewrite bulk_representative_unimodular; [ring|rewrite det2_mul,HX,(elliptic_circle_unimodular A E HA Hell HE); ring|exact HRd].
  - apply (limiting_representatives_unimodular X A L HX HA Hell HL).
  - exact Hsame.
Qed.

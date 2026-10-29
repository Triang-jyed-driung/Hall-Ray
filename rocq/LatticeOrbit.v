From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra ReturnIdentity IntegralMatrices LatticeBasis
  LatticeReturns.
Open Scope R_scope.

(* The exact return equations descend to equality of concrete lattice sets.
   No quotient-space topology is needed for these identities. *)
Theorem orbit_lattice_return : forall z E n r,
  same_lattice
    (mul3 (diagonal_flow (orbit_time n z+r)) (orbit_frame z E))
    (mul3 (diagonal_flow r) (orbit_frame (orbit_shift n z) (mul2 E (orbit_product n z)))).
Proof.
  intros z E n r.
  pose proof (unimodular_marking_preserves_lattice
    (mul3 (diagonal_flow (orbit_time n z+r)) (orbit_frame z E)) (orbit_markings n z)
    (orbit_markings_integral n z) (orbit_markings_unimodular n z)) as Hmark.
  rewrite mul3_assoc, orbit_segment_identity in Hmark.
  apply same_lattice_symmetric; exact Hmark.
Qed.

Theorem complete_lattice_orbit_cover : forall z E t,
  0 <= t -> exists n r,
    0 <= r < orbit_roof_time (orbit_shift n z) /\
    same_lattice (mul3 (diagonal_flow t) (orbit_frame z E))
      (mul3 (diagonal_flow r) (orbit_frame (orbit_shift n z) (mul2 E (orbit_product n z)))).
Proof.
  intros z E t Ht. destruct (orbit_forward_segment_cover z t Ht) as [n [r [Hr Htime]]].
  exists n, r. split; [exact Hr|]. rewrite Htime; apply orbit_lattice_return.
Qed.

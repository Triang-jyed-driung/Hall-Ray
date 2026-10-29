From Stdlib Require Import Reals Psatz.
From HallRay Require Import MatrixAlgebra FiberProducts EuclideanNorm DefectPhases.
Open Scope R_scope.

Lemma rotation_alignment_coordinates : forall x y a b nu nv,
  0 < nu -> 0 < nv -> nu*nu = x*x+y*y -> nv*nv = a*a+b*b ->
  exists R, det2 R = 1 /\ orthogonal2 R /\
    action R (x,y) = evscale (nu/nv) (a,b).
Proof.
  intros x y a b nu nv Hnu Hnv Hu Hv.
  set (D := nu*nv).
  assert (HD : D <> 0) by (unfold D; nra).
  assert (Henergy : (x*a+y*b)^2+(x*b-y*a)^2 = D^2).
  { replace ((x*a+y*b)^2+(x*b-y*a)^2) with ((x*x+y*y)*(a*a+b*b)) by ring.
    rewrite <- Hu, <- Hv. unfold D; ring. }
  set (c := (x*a+y*b)/D). set (s := (x*b-y*a)/D).
  assert (Hcircle : c*c+s*s = 1).
  { unfold c,s. replace (((x*a+y*b)/D)*((x*a+y*b)/D)+((x*b-y*a)/D)*((x*b-y*a)/D)) with
      (((x*a+y*b)^2+(x*b-y*a)^2)/(D*D)) by (field; exact HD).
    rewrite Henergy; field; exact HD. }
  exists (circle_matrix c s).
  destruct (circle_matrix_special_orthogonal c s Hcircle) as [Hd Ho].
  split; [exact Hd|]. split; [exact Ho|].
  unfold action,circle_matrix,evscale; simpl. unfold c,s,D.
  pose proof (f_equal (fun z => z*a) Hu) as Ha.
  pose proof (f_equal (fun z => z*b) Hu) as Hb.
  f_equal; apply (Rmult_eq_reg_r (nu*nv)); [|nra| |nra].
  - field_simplify; nra.
  - field_simplify; nra.
Qed.

Theorem rotation_aligns_vectors : forall u v,
  0 < enorm u -> 0 < enorm v -> exists R,
    det2 R = 1 /\ orthogonal2 R /\
    action R u = evscale (enorm u/enorm v) v.
Proof.
  intros [x y] [a b] Hu Hv.
  apply rotation_alignment_coordinates; try assumption; apply enorm_squared.
Qed.

Lemma enorm_positive_nonzero : forall v,
  v <> (0,0) -> 0 < enorm v.
Proof.
  intros v Hv. pose proof (enorm_nonnegative v).
  destruct (Req_dec (enorm v) 0) as [Hz|Hz]; [pose proof (enorm_definite v Hz); contradiction|lra].
Qed.

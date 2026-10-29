From Stdlib Require Import Reals Psatz.
Open Scope R_scope.

(* Elementary interval rules. Certificates generated with these rules are
   ordinary Rocq proofs: the generator is not part of the trusted base. *)
Lemma box_add : forall x y a b c d lo hi,
  a <= x <= b -> c <= y <= d -> lo <= a+c -> b+d <= hi ->
  lo <= x+y <= hi.
Proof. intros; lra. Qed.
Lemma box_subtract : forall x y a b c d lo hi,
  a <= x <= b -> c <= y <= d -> lo <= a-d -> b-c <= hi ->
  lo <= x-y <= hi.
Proof. intros; lra. Qed.

Lemma box_endpoint_lower : forall x a b t lo,
  a <= x <= b -> lo <= a*t -> lo <= b*t -> lo <= x*t.
Proof.
  intros x a b t lo Hx Ha Hb. destruct (Rle_dec 0 t) as [Ht|Ht].
  - pose proof (Rmult_le_pos (x-a) t ltac:(lra) Ht). nra.
  - pose proof (Rmult_le_pos (b-x) (-t) ltac:(lra) ltac:(lra)). nra.
Qed.
Lemma box_endpoint_upper : forall x a b t hi,
  a <= x <= b -> a*t <= hi -> b*t <= hi -> x*t <= hi.
Proof.
  intros x a b t hi Hx Ha Hb. destruct (Rle_dec 0 t) as [Ht|Ht].
  - pose proof (Rmult_le_pos (b-x) t ltac:(lra) Ht). nra.
  - pose proof (Rmult_le_pos (x-a) (-t) ltac:(lra) ltac:(lra)). nra.
Qed.

Lemma box_multiply : forall x y a b c d lo hi,
  a <= x <= b -> c <= y <= d ->
  lo <= a*c -> lo <= a*d -> lo <= b*c -> lo <= b*d ->
  a*c <= hi -> a*d <= hi -> b*c <= hi -> b*d <= hi ->
  lo <= x*y <= hi.
Proof.
  intros x y a b c d lo hi Hx Hy Hac Had Hbc Hbd Hac' Had' Hbc' Hbd'.
  assert (Hc : lo <= x*c) by (eapply box_endpoint_lower; eassumption).
  assert (Hd : lo <= x*d) by (eapply box_endpoint_lower; eassumption).
  assert (Hc' : x*c <= hi) by (eapply box_endpoint_upper; eassumption).
  assert (Hd' : x*d <= hi) by (eapply box_endpoint_upper; eassumption).
  split; rewrite Rmult_comm.
  - apply (box_endpoint_lower y c d x lo Hy); nra.
  - apply (box_endpoint_upper y c d x hi Hy); nra.
Qed.

Lemma box_inverse : forall x a b lo hi,
  0 < a -> a <= x <= b -> 0 <= lo -> 0 <= hi ->
  lo*b <= 1 -> 1 <= hi*a -> lo <= /x <= hi.
Proof.
  intros x a b lo hi Ha Hx Hl Hh Hlb Hha.
  assert (Hxpos : 0 < x) by lra.
  assert (Hinv : /x*x = 1) by (field; lra).
  pose proof (Rmult_le_pos (b-x) lo ltac:(lra) Hl).
  pose proof (Rmult_le_pos (x-a) hi ltac:(lra) Hh).
  split; apply (Rmult_le_reg_r x); try lra; nra.
Qed.

Lemma box_sqrt : forall x a b lo hi,
  0 <= a -> a <= x <= b -> 0 <= lo -> 0 <= hi ->
  lo*lo <= a -> b <= hi*hi -> lo <= sqrt x <= hi.
Proof.
  intros x a b lo hi Ha Hx Hl Hh Hls Hhs.
  pose proof (sqrt_pos x).
  pose proof (Rsqr_sqrt x ltac:(lra)). unfold Rsqr in *. split; nra.
Qed.

Lemma box_square : forall x a b lo hi,
  a <= x <= b ->
  lo <= a*a -> lo <= a*b -> lo <= b*a -> lo <= b*b ->
  a*a <= hi -> a*b <= hi -> b*a <= hi -> b*b <= hi ->
  lo <= x^2 <= hi.
Proof.
  intros x a b lo hi Hx Haa Hab Hba Hbb Haa' Hab' Hba' Hbb'.
  replace (x^2) with (x*x) by ring.
  eapply box_multiply; eassumption.
Qed.

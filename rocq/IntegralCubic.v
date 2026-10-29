From Stdlib Require Import Reals Psatz Lia ZArith Znumtheory QArith Qreals Qcanon.
Open Scope R_scope.

(* An elementary substitute for the Galois argument in Section 4.
   A rational root of a monic integral cubic is integral; a repeated root
   of a cubic is rational unless all three roots coincide. *)

Lemma reduced_monic_cubic_root_integral : forall q T S,
  Z.gcd (Qnum q) (QDen q) = 1%Z ->
  (Q2R q)^3-IZR T*(Q2R q)^2+IZR S*(Q2R q)-1 = 0 ->
  exists m : Z, Q2R q = IZR m.
Proof.
  intros [p d] T S Hred Hroot.
  set (den := Z.pos d).
  assert (Hden : (0 < den)%Z) by (unfold den; lia).
  assert (HdenR : IZR den <> 0) by (apply not_0_IZR; lia).
  change (Z.gcd p den = 1)%Z in Hred.
  change ((IZR p/IZR den)^3-IZR T*(IZR p/IZR den)^2+IZR S*(IZR p/IZR den)-1 = 0) in Hroot.
  assert (Hpoly : (p*p*p-T*p*p*den+S*p*den*den-den*den*den = 0)%Z).
  { apply eq_IZR.
    repeat first [rewrite minus_IZR|rewrite plus_IZR|rewrite mult_IZR]. simpl.
    assert (Hmul : IZR p*IZR p*IZR p-IZR T*IZR p*IZR p*IZR den+
      IZR S*IZR p*IZR den*IZR den-IZR den*IZR den*IZR den =
      ((IZR p/IZR den)^3-IZR T*(IZR p/IZR den)^2+IZR S*(IZR p/IZR den)-1)*(IZR den)^3).
    { field; exact HdenR. }
    rewrite Hroot in Hmul. nra. }
  assert (Hdiv3 : (den | p*(p*p))%Z).
  { exists (T*p*p-S*p*den+den*den)%Z. nia. }
  assert (Hgcd : Z.gcd den p = 1%Z) by (rewrite Z.gcd_comm; exact Hred).
  pose proof (Z.gauss den p (p*p) Hdiv3 Hgcd) as Hdiv2.
  pose proof (Z.gauss den p p Hdiv2 Hgcd) as Hdiv1.
  assert (Hdivunit : (den | p*1)%Z) by (replace (p*1)%Z with p by ring; exact Hdiv1).
  pose proof (Z.gauss den p 1 Hdivunit Hgcd) as Hone.
  assert (Hden1 : den = 1%Z) by (destruct (Z.divide_1_r den Hone); lia).
  exists p. change (IZR p/IZR den = IZR p). rewrite Hden1. simpl. field.
Qed.

Theorem rational_monic_cubic_root_integral : forall q T S,
  (Q2R q)^3-IZR T*(Q2R q)^2+IZR S*(Q2R q)-1 = 0 ->
  exists m : Z, Q2R q = IZR m.
Proof.
  intros q T S Hroot.
  assert (Hreal : Q2R (Qred q) = Q2R q) by (apply Qeq_eqR, Qred_correct).
  assert (Hred : Z.gcd (Qnum (Qred q)) (QDen (Qred q)) = 1%Z).
  { apply (proj1 (Qred_iff (Qred q))), Qred_involutive. }
  assert (Hroot' : (Q2R (Qred q))^3-IZR T*(Q2R (Qred q))^2+IZR S*(Q2R (Qred q))-1 = 0).
  { rewrite Hreal; exact Hroot. }
  destruct (reduced_monic_cubic_root_integral (Qred q) T S Hred Hroot') as [m Hm].
  exists m. rewrite <- Hreal. exact Hm.
Qed.

Theorem integral_cubic_double_unit_root_impossible : forall a b (T S : Z),
  1 < a -> 0 < b < 1 -> a*b*b = 1 ->
  a+2*b = IZR T -> b*b+2*a*b = IZR S -> False.
Proof.
  intros a b T S Ha Hb Hdet HT HS.
  set (Delta := (T*T-3*S)%Z).
  set (den := (2*Delta)%Z).
  set (num := (T*S-9)%Z).
  assert (HDelta : IZR Delta = (a-b)^2).
  { unfold Delta. rewrite minus_IZR, !mult_IZR. simpl.
    rewrite <- HT, <- HS. ring. }
  assert (HDeltaPos : (0 < Delta)%Z).
  { apply lt_IZR. simpl. rewrite HDelta. nra. }
  assert (Hden : (0 < den)%Z) by (unfold den; lia).
  assert (HdenR : 0 < IZR den) by (apply IZR_lt; exact Hden).
  assert (Hratio : IZR num = b*IZR den).
  { unfold num, den. rewrite !minus_IZR, !mult_IZR. simpl.
    rewrite HDelta, <- HT, <- HS. nra. }
  set (q := (num # Z.to_pos den)%Q).
  assert (Hq : Q2R q = b).
  { unfold q, Q2R; simpl.
    rewrite (Z2Pos.id den Hden).
    change (IZR num/IZR den = b).
    rewrite Hratio. field; lra. }
  assert (Hroot : (Q2R q)^3-IZR T*(Q2R q)^2+IZR S*(Q2R q)-1 = 0).
  { rewrite Hq, <- HT, <- HS. nra. }
  destruct (rational_monic_cubic_root_integral q T S Hroot) as [m Hm].
  rewrite Hq in Hm.
  assert (Hm0 : (0 < m)%Z) by (apply lt_IZR; simpl; lra).
  assert (Hm1 : (m < 1)%Z) by (apply lt_IZR; simpl; lra). lia.
Qed.

Theorem integral_characteristic_no_double_contraction : forall (T S : Z) a b,
  1 < a -> 0 < b < 1 ->
  (forall x, x^3-IZR T*x^2+IZR S*x-1 = (x-a)*(x-b)^2) -> False.
Proof.
  intros T S a b Ha Hb Hpoly.
  pose proof (Hpoly 0) as H0. pose proof (Hpoly 1) as H1.
  pose proof (Hpoly (-1)) as Hm1.
  assert (Hdet : a*b*b = 1) by nra.
  apply (integral_cubic_double_unit_root_impossible a b T S); auto; nra.
Qed.

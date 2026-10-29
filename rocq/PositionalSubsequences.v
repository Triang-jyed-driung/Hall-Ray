From Stdlib Require Import Reals Psatz Lia Arith Classical ClassicalChoice.
From HallRay Require Import PeriodicReturns CompactMatrices.

Definition arbitrarily_late (P : nat -> Prop) :=
  forall N, exists n, (N <= n)%nat /\ P n.

Lemma arbitrarily_late_subsequence : forall P,
  arbitrarily_late P -> exists ns,
    indices_tend_to_infinity ns /\ forall i, P (ns i).
Proof.
  intros P HP.
  destruct (@choice nat nat (fun i n => (i <= n)%nat /\ P n) HP) as [ns Hns].
  exists ns; split.
  - intros N; exists N; intros i Hi; specialize (Hns i); lia.
  - intro i; exact (proj2 (Hns i)).
Qed.

Lemma finite_values_pigeonhole : forall B a,
  arbitrarily_late (fun i => (a i < B)%nat) ->
  exists r, (r < B)%nat /\ arbitrarily_late (fun i => a i = r).
Proof.
  induction B as [|B IH]; intros a HP.
  - destruct (HP 0%nat) as [i [_ Hi]]; lia.
  - destruct (classic (arbitrarily_late (fun i => a i = B))) as [HB|HB].
    + exists B; split; [lia|exact HB].
    + assert (Htail : exists N, forall i, (N <= i)%nat -> a i <> B).
      { unfold arbitrarily_late in HB. apply not_all_ex_not in HB.
        destruct HB as [N HN]. exists N; intros i Hi Heq.
        apply HN; exists i; auto. }
      destruct Htail as [N HN].
      assert (HPsmall : arbitrarily_late (fun i => (a i < B)%nat)).
      { intro I. destruct (HP (Nat.max I N)) as [i [Hi Hb]].
        exists i; split; [lia|]. specialize (HN i ltac:(lia)); lia. }
      destruct (IH a HPsmall) as [r [Hr Hlate]]. exists r; split; [lia|exact Hlate].
Qed.

Theorem natural_sequence_dichotomy : forall a,
  indices_tend_to_infinity a \/
  exists r ns, indices_tend_to_infinity ns /\ forall i, a (ns i) = r.
Proof.
  intro a. destruct (classic (indices_tend_to_infinity a)) as [Hyes|Hno]; [auto|].
  right. unfold indices_tend_to_infinity in Hno. apply not_all_ex_not in Hno.
  destruct Hno as [B HB].
  assert (Hall : forall N, ~ (forall i, (N <= i)%nat -> (B <= a i)%nat)).
  { intros N HN; apply HB; exists N; exact HN. }
  assert (Hlate : arbitrarily_late (fun i => (a i < B)%nat)).
  { intro N. specialize (Hall N). apply not_all_ex_not in Hall.
    destruct Hall as [i Hi]. exists i; split.
    - apply NNPP; intro Hbad. apply Hi; intro HNi; contradiction.
    - assert (Hbad : ~ (B <= a i)%nat) by (intro H; apply Hi; auto). lia. }
  destruct (finite_values_pigeonhole B a Hlate) as [r [Hr HP]].
  destruct (arbitrarily_late_subsequence _ HP) as [ns [Hns Hvalue]].
  exists r,ns; auto.
Qed.

Theorem periodic_positions_subsequence : forall ns js,
  exists ks, indices_tend_to_infinity ks /\
    ((exists j, forall i, js (ks i) = j) \/
     (exists r, forall i, (ns (ks i)-js (ks i))%nat = r) \/
     (indices_tend_to_infinity (fun i => js (ks i)) /\
      indices_tend_to_infinity (fun i => (ns (ks i)-js (ks i))%nat))).
Proof.
  intros ns js. destruct (natural_sequence_dichotomy js) as [Hjs|[j [ks [Hks Hconst]]]].
  - destruct (natural_sequence_dichotomy (fun i => (ns i-js i)%nat))
      as [Hremaining|[r [ks [Hks Hconst]]]].
    + exists (fun i => i); split; [intros N; exists N; auto|]. right; right; auto.
    + exists ks; split; [exact Hks|]. right; left; exists r; exact Hconst.
  - exists ks; split; [exact Hks|]. left; exists j; exact Hconst.
Qed.

Lemma cofinal_identity : indices_tend_to_infinity (fun i => i).
Proof. intros N; exists N; auto. Qed.

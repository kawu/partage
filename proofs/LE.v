From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.

Lemma le_SS : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H.
  induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.

Lemma plus_le_r : forall (x y z : nat),
  x <= y -> x + z <= y + z.
Proof.
  intros x y z.
  generalize dependent y.
  generalize dependent x.
  induction z as [|z' IH].
  - intros x y. intros H.
    rewrite plus_0_r. rewrite plus_0_r. apply H.
  - intros x y. intros H.
    rewrite <- plus_Snm_nSm.
    rewrite <- plus_Snm_nSm.
    apply IH.
    apply le_SS. apply H.
Qed.

Lemma plus_le_l : forall (x y z : nat),
  x + z <= y + z -> x <= y.
Proof.
  intros x y z.
  generalize dependent y.
  generalize dependent x.
  induction z as [|z' IH].
  - intros x y. intros H.
    rewrite plus_0_r in H.
    rewrite plus_0_r in H.
    apply H.
  - intros x y. intros H.
    rewrite <- plus_Snm_nSm in H.
    rewrite <- plus_Snm_nSm in H.
    apply IH in H.
    inversion H.
    + reflexivity.
    + transitivity (S x).
      * apply le_S. reflexivity.
      * apply H1.
Qed.

Lemma combine_le : forall x1 y1 x2 y2 : nat,
  x1 <= y1 ->
  x2 <= y2 ->
    x1 + x2 <= y1 + y2.
Proof.
  intros x1 y1 x2 y2.
  intros H1 H2.
  transitivity (x1 + y2).
  - rewrite plus_comm. rewrite (plus_comm x1).
    apply plus_le_r. apply H2.
  - apply plus_le_r. apply H1.
Qed.

Lemma lebP : forall n m, reflect (n <= m) (n <=? m).
Proof.
  intros n m. apply iff_reflect. split.
  - intros H. apply leb_correct. apply H.
  - intros H. apply leb_complete. apply H.
Qed.

Lemma leb_trans : forall i j k,
  i <= j -> j <= k ->
    i <= k.
Proof.
  intros i j k.
  intros H1 H2.
  transitivity j.
  - apply H1.
  - apply H2.
Qed.

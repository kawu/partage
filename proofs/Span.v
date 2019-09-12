From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.

From LF Require Import LE.
From LF Require Import App.
From LF Require Import Grammar.


(**
  In span (list of terminals between two positions)
**)


(** The list (=>set) of terminals inside the given span *)
Fixpoint in_span (i j : term) : list term :=
  match j with
  | 0 => []
  | S j' =>
    if i <=? j'
    then in_span i j' ++ [j']
    else []
  end.

Example in_span_ex1 : in_span 1 3 = [1; 2].
Proof. reflexivity. Qed.

Example in_span_ex2 : in_span 1 1 = [].
Proof. reflexivity. Qed.


Remark not_S_i_leb_i : forall (i : term),
  (S i <=? i = false).
Proof.
  intros i.
  induction i as [|i' IH].
  - simpl. reflexivity.
  - simpl in IH. simpl. apply IH.
Qed.

Lemma in_span_ii_empty : forall (i : term),
  in_span i i = [].
Proof.
  intros i.
  unfold in_span.
  destruct i as [|i'].
  - reflexivity.
  - destruct (S i' <=? i') eqn:E.
    + rewrite not_S_i_leb_i in E. discriminate E.
    + reflexivity.
Qed.


Theorem in_span_Sj : forall i j : term,
  i <= j -> in_span i (S j) = in_span i j ++ [j].
Proof.
  intros i j H.
  simpl.
  destruct (lebP i j) as [H'|H'].
  - reflexivity.
  - apply H' in H. destruct H.
Qed.


Theorem in_span_Si : forall i j : term,
  S i <= j -> [i] ++ in_span (S i) j = in_span i j.
Proof.
  intros i j H.
  induction H.
  - simpl. destruct i as [|i'] eqn:E.
    + simpl. reflexivity.
    + rewrite not_S_i_leb_i.
      rewrite Nat.leb_refl.
      rewrite in_span_ii_empty.
      simpl. reflexivity.
  - rewrite in_span_Sj.
    Focus 2. apply H.
    rewrite in_span_Sj.
    + rewrite <- IHle. rewrite app_assoc. reflexivity.
    + transitivity (S i).
      * apply le_S. reflexivity.
      * apply H.
Qed.


Lemma in_span_split : forall i j k,
  i <= j ->
  j <= k ->
    in_span i k = in_span i j ++ in_span j k.
Proof.
  intros i j k H1 H2.
  generalize dependent j.
  generalize dependent i.
  induction k as [|k'].
  - intros i j.
    simpl.
    intros H1 H2.
    assert (H3: j = 0). { inversion H2. reflexivity. }
    assert (H4: i = 0). { rewrite H3 in H1. inversion H1. reflexivity. }
    rewrite H3. rewrite H4. rewrite in_span_ii_empty. simpl. reflexivity.
  - intros i j. intros H1 H2.
    inversion H2 as [H3|m H3 H4].
    + rewrite in_span_ii_empty. rewrite app_nil_r. reflexivity.
    + apply (leb_trans i j m) in H1 as H5.
      Focus 2. rewrite H4. apply H3.
      apply (in_span_Sj i m) in H5. rewrite H4 in H5.
      apply (in_span_Sj j k') in H3 as H6.
      rewrite H5. rewrite H6.
      rewrite app_assoc.
      apply app_suf_eq.
      apply IHk'.
      * apply H1.
      * apply H3.
Qed.


(**
  Rest (list of terminals on the left and right of the two positions)
**)


(** The list (=>set) of terminals outside of the given span *)
(** TODO: rename as [out] at some point *)
(** TODO: [term_max g] or [term_max g + 1]? *)
Definition rest {vt nt} (g : @Grammar vt nt) (i j : term) : list term :=
  in_span 0 i ++ in_span j (term_max g + 1).


From Coq Require Import Arith.Arith.
From Coq Require Import Reals.Reals.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.

From LF Require Import Utils.
From LF Require Import LE.
From LF Require Import App.
From LF Require Import Grammar.
From LF Require Import Span.
From LF Require Import Cost.

Open Scope R_scope.


(** Amortized weight of the given passive parsing configuration *)
Definition amort_weight {vt nt} (g : @Grammar vt nt) (n : vt) : weight :=
  tree_weight g n + min_arc_weight g (anchor g n) - costs g (sup g n).


Lemma amort_weight_ge_0 : forall {vt nt}
    (g : @Grammar vt nt) (v : vt),
  0 <= amort_weight g v.
Proof.
  intros vt nt g v.
  unfold amort_weight.
  apply (Rplus_le_reg_r (costs g (sup g v))).
  rewrite Rplus_0_l.
  unfold Rminus.
  rewrite (Rplus_assoc).
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  rewrite Rplus_comm.
  apply costs_sup_le.
  reflexivity.
Qed.


(** Amortized weight of the given active parsing configuration *)
Definition amort_weight' {vt nt} (g : @Grammar vt nt) (r : vt*nat) : weight :=
  let n := fst r
  in tree_weight g n + min_arc_weight g (anchor g n) - costs g (sup' g r).


Lemma amort_weight'_ge_0 : forall {vt nt}
    (g : @Grammar vt nt) (r : vt*nat),
  0 <= amort_weight' g r.
Proof.
  (* TODO: prove in terms of costs_inf_le_amort_weight'? *)
  intros vt nt g r.
  unfold amort_weight'.
  apply (Rplus_le_reg_r (costs g (sup' g r))).
  rewrite Rplus_0_l.
  unfold Rminus.
  rewrite (Rplus_assoc).
  rewrite Rplus_opp_l.
  rewrite Rplus_0_r.
  rewrite Rplus_comm.
  apply costs_sup'_le.
  - reflexivity.
  - reflexivity.
Qed.


Lemma costs_inf_le_amort_weight : forall {vt nt}
  (g : @Grammar vt nt) (v : vt),
    costs g (inf g v) <= amort_weight g v.
Proof.
  intros vt nt g v.
  unfold amort_weight.

  apply (Rplus_le_reg_r (costs g (sup g v))).
  unfold Rminus.
  rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r.
  rewrite <- costs_app.
  rewrite inf_plus_sup.
  unfold costs. simpl. rewrite Rplus_0_l.
  unfold cost. rewrite Rplus_comm.
  apply Rplus_le_compat.
  - apply min_tree_weight_le. reflexivity.
  - apply Rle_refl.
Qed.


Lemma costs_inf_le_amort_weight' : forall {vt nt}
  (g : @Grammar vt nt) (r : vt*nat),
    costs g (inf' g r) <= amort_weight' g r.
Proof.
  intros vt nt g r.
  unfold amort_weight'.

  apply (Rplus_le_reg_r (costs g (sup' g r))).
  unfold Rminus.
  rewrite Rplus_assoc. rewrite Rplus_opp_l. rewrite Rplus_0_r.
  rewrite <- costs_app.
  rewrite inf_plus_sup'.
  unfold costs. simpl. rewrite Rplus_0_l.
  unfold cost. rewrite Rplus_comm.
  apply Rplus_le_compat.
  - apply min_tree_weight_le. reflexivity.
  - apply Rle_refl.
Qed.


Lemma shift_amort_weight : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
  shift g r' = Some (v, r) ->
    amort_weight' g r = amort_weight' g r' + costs g (inf g v).
Proof.
  intros vt nt g r r' v H.
  unfold amort_weight'.
  apply shift_preserves_head in H as H'.
  rewrite H'.
  apply shift_cost_sup in H as H''.
  rewrite (minus_le_plus
          (tree_weight g (fst r) + min_arc_weight g (anchor g (fst r)))
          (costs g (sup' g r'))).
  rewrite H''. rewrite plus_minus. reflexivity.
(*
  - rewrite H''. rewrite plus_minus. reflexivity.
  - destruct (sup' g r') eqn:E.
    + unfold costs. simpl.
      rewrite <- (Rplus_0_l 0).
      apply Rplus_le_compat.
      * apply tree_weight_ge_0.
      * apply min_arc_weight_ge_0.
    + apply sup'_destr in E as [E1 E2].
      rewrite E2. unfold costs.
      simpl. unfold cost. rewrite Rplus_0_l.
      rewrite <- Rplus_comm.
      apply Rplus_le_compat.
        * apply min_tree_weight_le.
          rewrite E1. rewrite H'. reflexivity.
        * rewrite E1. rewrite H'. apply Rle_refl.
*)
Qed.


Lemma shift_amort_weight' : forall {vt nt}
    (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
  shift g r = Some (v, r') ->
    amort_weight g v + costs g (inf' g r) = amort_weight' g r'.
Proof.
  intros vt nt g r r' v H.
  unfold amort_weight. unfold amort_weight'.
  apply shift_preserves_tree_weight in H as H1.
  rewrite <- H1.
  apply shift_preserves_anchor in H as H2.
  rewrite <- H2.
  apply shift_cost_sup' in H as H3.
  rewrite (minus_le_plus _ (costs g (sup g v))).
  rewrite H3. rewrite plus_minus. reflexivity.
(*
  - rewrite H3. rewrite plus_minus. reflexivity.
  - destruct (sup g v) eqn:E.
    + unfold costs. simpl. rewrite <- (Rplus_0_l 0).
      apply Rplus_le_compat.
      * apply tree_weight_ge_0.
      * apply min_arc_weight_ge_0.
    + apply sup_destr in E as [E1 E2].
      rewrite E2. unfold costs.
      simpl. unfold cost. rewrite Rplus_0_l.
      rewrite <- Rplus_comm.
      apply Rplus_le_compat.
        * apply min_tree_weight_le.
          rewrite E1. reflexivity.
        * rewrite E1. apply Rle_refl.
*)
Qed.


Lemma amort_weight_complete : forall {vt nt}
  (g : @Grammar vt nt) (r : vt*nat),
    shift g r = None ->
      amort_weight g (fst r) = amort_weight' g r.
Proof.
  intros vt nt g r.
  intros H.
  unfold amort_weight.
  unfold amort_weight'.
  apply shift_sup_passive in H.
  rewrite H. reflexivity.
Qed.


Lemma amort_le_omega : forall {vt nt}
  (g : @Grammar vt nt) v u,
    amort_weight g v <= omega g v u.
Proof.
  intros vt nt g v u.
  unfold amort_weight.
  unfold omega.
  unfold Rminus.
  rewrite (Rplus_comm _ (tree_weight _ _)).
  rewrite Rplus_assoc.
  apply Rplus_le_compat_l.
  rewrite <- Rplus_0_r.
  apply Rplus_le_compat.
  - apply min_arc_weight_le.
  - apply (Rplus_le_reg_r (costs g (sup g v))).
    rewrite Rplus_opp_l. rewrite Rplus_0_l.
    apply costs_ge_0.
Qed.


Close Scope R_scope.

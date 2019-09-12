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


Open Scope R_scope.


(** The minimal cost of scanning the given terminal *)
Definition cost {vt nt} (g : @Grammar vt nt) (t : term) : weight :=
  min_arc_weight g t + min_tree_weight g t.


(** The minimal cost of scanning the given list of terminals *)
Definition costs {vt nt}
    (g : @Grammar vt nt) (ts : list term) : weight :=
  fold_left Rplus (map (cost g) ts) 0.


Lemma costs_nil :  forall {vt nt}
  (g : @Grammar vt nt),
    costs g [] = 0.
Proof.
  intros vt nt g.
  unfold costs. simpl. reflexivity.
Qed.


Lemma costs_ge_0 :  forall {vt nt}
  (g : @Grammar vt nt) (ts : list term),
    0 <= costs g ts.
Proof.
  intros vt nt g ts.
  unfold costs.
  induction ts as [|x ts' IH].
  - simpl. apply Rle_refl.
  - simpl. rewrite Rplus_0_l.
    rewrite fold_left_plus.
    rewrite <- (Rplus_0_l 0).
    apply Rplus_le_compat.
    + rewrite Rplus_0_l. apply IH.
    + unfold cost. rewrite <- (Rplus_0_l 0).
      apply Rplus_le_compat.
      * apply min_arc_weight_ge_0.
      * apply min_tree_weight_ge_0.
Qed.


Lemma costs_app : forall {vt nt}
    (g : @Grammar vt nt) (ts ts' : list term),
  costs g (ts ++ ts') = costs g ts + costs g ts'.
Proof.
  intros vt nt g ts ts'.
  generalize dependent ts'.
  induction ts as [|tsh tst IH].
  - intros ts'. simpl. rewrite costs_nil.
    rewrite Rplus_0_l. reflexivity.
  - intros ts'. rewrite <- app_comm_cons.
    unfold costs. simpl.
    unfold costs in IH.
    rewrite fold_left_plus. rewrite Rplus_0_l.
    rewrite (fold_left_plus (cost g tsh)).
    rewrite IH. rewrite Rplus_assoc.
    rewrite (Rplus_comm _ (cost _ _)).
    rewrite <- Rplus_assoc. reflexivity.
Qed.


Lemma shift_cost_sup : forall {vt nt}
  (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
    shift g r' = Some (v, r) ->
      costs g (sup' g r') = costs g (inf g v) + costs g (sup' g r).
Proof.
  intros vt nt g r r' v H.
  destruct (shift g r') as [(v', r'')|] eqn:E.
  - rewrite shift_sup with (r0 := r) (v0 := v).
    + rewrite <- costs_app. apply f_equal. reflexivity.
    + rewrite <- H. apply E.
  - discriminate H.
Qed.


Lemma shift_cost_sup' : forall {vt nt}
  (g : @Grammar vt nt) (r r' : vt*nat) (v : vt),
    shift g r' = Some (v, r) ->
      costs g (sup g v) = costs g (inf' g r') + costs g (sup' g r).
Proof.
  intros vt nt g r r' v H.
  destruct (shift g r') as [(v', r'')|] eqn:E.
  - injection H as H1 H2.
    rewrite H1 in E. rewrite H2 in E.
    apply (shift_sup' g r r' v) in E as E'.
    rewrite E'.
    rewrite costs_app. reflexivity.
  - discriminate H.
Qed.


Lemma cost_one : forall {vt nt} (g : @Grammar vt nt) (i : term),
  costs g [i] = cost g i.
Proof.
  intros vt nt g i.
  unfold costs.
  simpl.
  rewrite Rplus_0_l.
  reflexivity.
Qed.


(* TODO: prove based on cost_rest_plus_in_r *)
Lemma cost_rest_Sj : forall {vt nt} (g : @Grammar vt nt) (i j : term),
  (* j <= term_max g -> *)
  Nat.le j (term_max g) ->
    costs g (rest g i j) = costs g (rest g i (S j)) + cost g j.
Proof.
  intros vt nt g i j H2.
  unfold rest.
  rewrite costs_app.
  rewrite costs_app.
  (* rewrite <- plus_assoc. *)
  rewrite Rplus_assoc.
  apply f_equal2. { reflexivity. }
  (* apply (f_equal2_plus). { reflexivity. } *)
  (* simpl. *)
  rewrite <- in_span_Si.
  - rewrite costs_app. rewrite <- cost_one.
    rewrite Rplus_comm. reflexivity.
  - rewrite plus_comm. simpl.
    apply le_n_S. apply H2.
Qed.


Lemma cost_rest_plus_in_r : forall {vt nt}
  (g : @Grammar vt nt) (i j k : term),
    Nat.le j k ->
    Nat.le k (term_max g + 1) ->
      costs g (rest g i j) = costs g (rest g i k) + costs g (in_span j k).
Proof.
  intros vt nt g i j k H1 H2.
  unfold rest.
  rewrite costs_app. rewrite costs_app.
  rewrite Rplus_assoc.
  apply f_equal2. { reflexivity. }
  rewrite (in_span_split j k).
  - rewrite costs_app. rewrite Rplus_comm. reflexivity.
  - apply H1.
  - apply H2.
Qed.


Lemma cost_rest_plus_in_l : forall {vt nt}
  (g : @Grammar vt nt) (i j k : term),
    Nat.le i j ->
      costs g (rest g j k) = costs g (in_span i j) + costs g (rest g i k).
Proof.
  intros vt nt g i j k H1.
  unfold rest.
  rewrite costs_app.
  rewrite costs_app.
  rewrite <- Rplus_assoc.
  apply (f_equal2).
  Focus 2. reflexivity.
  rewrite Rplus_comm.
  rewrite (in_span_split 0 i j).
  - rewrite costs_app. reflexivity.
  - apply le_0_n.
  - apply H1.
Qed.


Lemma inf_cost_vs_omega : forall {vt nt} (g : @Grammar vt nt) (v w : vt),
  root g v = true ->
    costs g (inf g v) <= omega g v w.
Proof.
  intros vt nt g v w.
  intros RH.
  unfold omega.
  apply inf_root_anchor in RH as H.
  rewrite H.
  unfold costs. simpl. rewrite Rplus_0_l.
  unfold cost.
  apply (Rplus_le_compat).
  - apply min_arc_weight_le.
  - apply min_tree_weight_le. reflexivity.
Qed.


Lemma inf_cost_vs_omega' :
  forall {vt nt} (g : @Grammar vt nt) (r : vt*nat) (w : vt),
    shift g r = None ->
    root g (fst r) = true ->
      costs g (inf' g r) <= omega g (fst r) w.
Proof.
  intros vt nt g r w H.
  apply no_shift_inf in H as H'.
  rewrite H'.
  intros R.
  apply inf_cost_vs_omega.
  apply R.
Qed.


(** Span costs when ignoring the gap *)
Lemma costs_ignore_gap : forall {vt nt} i j k l (g : @Grammar vt nt),
  Nat.le i j ->
  Nat.le j k ->
  Nat.le k l ->
    costs g (in_span i j) + costs g (in_span k l) <= costs g (in_span i l).
Proof.
  intros vt nt i j k l g.
  intros Le_i_j Le_j_k Le_k_l.
  apply (Rle_trans _
    (costs g (in_span i j) + costs g (in_span j k) + costs g (in_span k l))).
  - apply Rplus_le_compat_r.
    rewrite <- (Rplus_0_r (_ _ (in_span i j))).
    rewrite Rplus_assoc.
    apply Rplus_le_compat_l.
    rewrite Rplus_0_l.
    apply costs_ge_0.
  - rewrite <- ?costs_app.
    rewrite <- in_span_split.
    Focus 2. apply Le_i_j.
    Focus 2. apply Le_j_k.
    rewrite <- in_span_split.
    + apply Rle_refl.
    + transitivity j.
      * apply Le_i_j.
      * apply Le_j_k.
    + apply Le_k_l.
Qed.


(** Rest cost of a gap *)
Lemma costs_rest_gap : forall {vt nt} i j k l (g : @Grammar vt nt),
  Nat.le 0 i ->
  Nat.le i j ->
  Nat.le j k ->
  Nat.le k l ->
  Nat.le l (term_max g + 1) ->
    costs g (rest g j k) =
      costs g (rest g i l) + costs g (in_span i j) + costs g (in_span k l).
Proof.
  intros vt nt i j k l g.
  intros Le_0_i Le_i_j Le_j_k Le_k_l Le_l_max.
  unfold rest.
  rewrite ?costs_app.
  rewrite ?(Rplus_shift_left (costs g (in_span i j))).
  rewrite Rplus_assoc.

  (* get rid of [costs g (in_span 0 j] *)
  assert (H: costs g (in_span 0%nat j) =
    costs g (in_span 0%nat i) + costs g (in_span i j)).
    { rewrite <- costs_app.
      rewrite <- in_span_split.
      - reflexivity.
      - apply Le_0_i.
      - apply Le_i_j.
    }
  rewrite <- H.
  apply Rplus_eq_compat_l.

  (* get rid of the rest *)
  rewrite Rplus_comm.
  rewrite <- costs_app.
  rewrite <- in_span_split.
  - reflexivity.
  - apply Le_k_l.
  - apply Le_l_max.
Qed.


Lemma costs_sup_le : forall {vt nt}
  (g : @Grammar vt nt) (v : vt) t,
    anchor g v = t ->
      costs g (sup g v) <= min_arc_weight g t + tree_weight g v.
Proof.
  intros vt nt g v t.
  intros A.
  destruct sup eqn:E.
  - unfold costs. simpl.
    rewrite <- (Rplus_0_l 0).
    apply Rplus_le_compat.
    + apply min_arc_weight_ge_0.
    + apply tree_weight_ge_0.
  - apply sup_destr in E as [H Lempty].
    rewrite Lempty. rewrite cost_one.
    unfold cost.
    rewrite A in H. rewrite H.
    apply Rplus_le_compat.
    + apply Rle_refl.
    + apply min_tree_weight_le.
      apply A.
Qed.


Lemma costs_sup'_le : forall {vt nt}
  (g : @Grammar vt nt) r v t,
    fst r = v ->
    anchor g v = t ->
      costs g (sup' g r) <= min_arc_weight g t + tree_weight g v.
Proof.
  intros vt nt g r v t.
  intros F A.
  destruct sup' eqn:E.
  - unfold costs. simpl.
    rewrite <- (Rplus_0_l 0).
    apply Rplus_le_compat.
    + apply min_arc_weight_ge_0.
    + apply tree_weight_ge_0.
  - apply sup'_destr in E as [H Lempty].
    rewrite Lempty. rewrite cost_one.
    unfold cost.
    rewrite F in H.
    rewrite A in H. rewrite H.
    apply Rplus_le_compat.
    + apply Rle_refl.
    + apply min_tree_weight_le.
      apply A.
Qed.


Close Scope R_scope.
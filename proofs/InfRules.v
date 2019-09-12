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
From LF Require Import Amort.

Open Scope R_scope.


(** Parsing configuration *)
Inductive spot {vt} : Type :=
  | Node (v : vt)
  | Rule (r : vt*nat).


(** Value of the heuristic for the given passive item *)
Definition heuristic {vt nt}
  (g : @Grammar vt nt) (v : vt) (i j : term) : weight :=
    amort_weight g v + costs g (rest g i j).


(** Value of the heuristic for the given active item *)
Definition heuristic' {vt nt}
  (g : @Grammar vt nt) (r : vt*nat) (i j : term) : weight :=
    amort_weight' g r + costs g (rest g i j).


Lemma heuristic'_ge_0 : forall {vt nt} r i j (g : @Grammar vt nt),
  0 <= heuristic' g r i j.
Proof.
  intros vt nt r i j g.
  unfold heuristic'.
  rewrite <- (Rplus_0_l 0).
  apply Rplus_le_compat.
  - apply amort_weight'_ge_0.
  - apply costs_ge_0.
Qed.


(** Inferior terminals for the given spot **)
Definition heuristic_s {vt nt}
  (g : @Grammar vt nt) (s : spot) (i j : term) : weight :=
    match s with
    | Node v => heuristic g v i j
    | Rule r => heuristic' g r i j
    end.


(** Active item's total weight: the inside weight +
    the heuristic estimation
**)
Definition total {vt nt}
  (g : @Grammar vt nt) (v : vt) (i j : term)
  (w : weight)  (* inside weight *)
  (w' : weight) (* gap weight estimate *)
  : weight :=
    w + w' + heuristic g v i j.


(** Active item's total weight: the inside weight +
    the heuristic estimation
**)
Definition total' {vt nt}
  (g : @Grammar vt nt) (r : vt*nat) (i j : term)
  (w : weight)  (* inside weight *)
  (w' : weight) (* gap weight estimate *)
  : weight :=
    w + w' + heuristic' g r i j.


(** Inferior terminals for the given spot **)
Definition inf_s {vt nt} (g : @Grammar vt nt) (s : spot) : list term :=
  match s with
  | Node v => inf g v
  | Rule r => inf' g r
  end.


(** Combine two optional values *)
Definition oplus {A : Type} (x y : option A) : option A :=
  match x with
  | None => y
  | Some v => x
  end.


(** Inference rules for chart items.

We thread the previous max total weight through the inference rules
in order to be able to easily check the monotonicity of the system.

*)
Inductive item {vt nt}
   : @Grammar vt nt
    (* the underlying grammar *)
  -> @spot vt
    (* parsing configuration (spot) *)
  -> term -> term
    (* starting position, ending position *)
  -> option term -> option term
    (* optional gap *)
  -> weight
    (* inside weight *)
  -> weight
    (* gap weight estimate *)
  -> weight
    (* previous max total weight (or 0 if none) *)
  -> Prop :=
  | axiom (g : @Grammar vt nt) (r : vt*nat) (i : term)
      (I: In r (rules g))
      (L: Nat.le i (term_max g)) :
        item g (Rule r) i i None None 0 0 0
  | scan (g : @Grammar vt nt)
      (r r' : vt*nat) (i j : term) p q (v : vt) (w w' _t : weight)
      (P: item g (Rule r) i j p q w w' _t)
      (L: Nat.le j (term_max g))
      (Sh: shift g r = Some (v, r'))
      (Lb: label g v = Terminal (Some j)) :
        item g (Rule r') i (S j) p q w w'
          (total' g r i j w w')
  | scan_empty (g : @Grammar vt nt)
      (r r' : vt*nat) (i j : term) p q (v : vt) (w w' _t : weight)
      (P: item g (Rule r) i j p q w w' _t)
      (L: Nat.le j (term_max g))
      (Sh: shift g r = Some (v, r'))
      (Lb: label g v = Terminal None) :
        item g (Rule r') i j p q w w'
          (total' g r i j w w')
  | deact (g : @Grammar vt nt)
      (r : vt*nat) (v : vt) (i j : term) p q (w w' _t : weight)
      (P: item g (Rule r) i j p q w w' _t)
      (Sh: shift g r = None) :
        item g (Node (fst r)) i j p q w w'
          (total' g r i j w w')
  | pseudo_subst (g : @Grammar vt nt)
      (l l' : vt*nat) (v : vt) (i j k : term) p1 q1 p2 q2
      (w1 w2 w1' w2' _t1 _t2 : weight)
      (LP: item g (Rule l) i j p1 q1 w1 w1' _t1)
      (RP: item g (Node v) j k p2 q2 w2 w2' _t2)
      (Sh: shift g l = Some (v, l')) :
        item g (Rule l') i k (oplus p1 p2) (oplus q1 q2) (w1 + w2) (w1' + w2')
          (Rmax (total' g l i j w1 w1') (total g v j k w2 w2'))
  | subst (g : @Grammar vt nt)
      (l l' : vt*nat) (v v' : vt) (i j k : term) p1 q1
      (w1 w2 w1' w2' _t1 _t2 : weight)
      (LP: item g (Rule l) i j p1 q1 w1 w1' _t1)
      (RP: item g (Node v) j k None None w2 w2' _t2)
      (Rv: root g v = true)
      (Rs: sister g v = false)
      (Le: leaf g v' = true)
      (Lb: label g v = label g v')
      (Sh: shift g l = Some (v', l')) :
        (* NOTE: [w2' = 0]! *)
        item g (Rule l') i k p1 q1 (w1 + w2 + omega g v (fst l)) (w1' + w2')
          (Rmax (total' g l i j w1 w1') (total g v j k w2 w2'))
  | sister_adjoin (g : @Grammar vt nt)
      (l : vt*nat) (v : vt) (i j k : term) p1 q1
      (w1 w2 w1' w2' _t1 _t2 : weight)
      (LP: item g (Rule l) i j p1 q1 w1 w1' _t1)
      (RP: item g (Node v) j k None None w2 w2' _t2)
      (Rs: sister g v = true)
      (Lb: label g v = label g (fst l)) :
        (* NOTE: [w2' = 0]! *)
        item g (Rule l) i k p1 q1 (w1 + w2 + omega g v (fst l)) (w1' + w2')
          (Rmax (total' g l i j w1 w1') (total g v j k w2 w2'))
  | foot_adjoin (g : @Grammar vt nt)
      (l l' : vt*nat) (v v' : vt) (i j k : term) p2 q2
      (w1 w2 w1' w2' _t1 _t2 : weight)
      (LP: item g (Rule l) i j None None w1 w1' _t1)
      (RP: item g (Node v) j k p2 q2 w2 w2' _t2)
      (Sh: shift g l = Some (v', l'))
      (Fv: foot g v' = true)
      (Lb: label g v = label g v') :
        (* NOTE: [w1' = 0]! *)
        item g (Rule l') i k (Some j) (Some k) w1 (w1' + w2 + w2' + amort_weight g v)
          (Rmax (total' g l i j w1 w1') (total g v j k w2 w2'))
  | root_adjoin (g : @Grammar vt nt)
      (v u : vt) (i j k l : term) p2 q2
      (w1 w2 w1' w2' _t1 _t2 : weight)
      (LP: item g (Node v) i l (Some j) (Some k) w1 w1' _t1)
      (RP: item g (Node u) j k p2 q2 w2 w2' _t2)
      (Rv: root g v = true)
      (Lb: label g v = label g u) :
        (* NOTE: [w2' = 0]! *)
        item g (Node u) i l p2 q2 (w1 + w2 + omega g v u) (w1' + w2')
          (Rmax (total g v i l w1 w1') (total g u j k w2 w2')).


Theorem item_i_le_j : forall {vt nt} s i j p q w w' t (g : @Grammar vt nt)
  (H: @item vt nt g s i j p q w w' t),
    Nat.le i j.
Proof.
  intros vt nt s i j p q w w' t g.
  intros eta.
  induction eta
    as [ g r i I L
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r v i j p q w w' _t P IHP Sh
       | g l l' v i j k p1 q1 p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Rs Le Lb Sh
       | g l v i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rs Lb
       | g l l' v v' i j k p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh Fv Lb
       | g v u i j k l p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Lb
       ].
  - reflexivity.
  - apply le_S. apply IHP.
  - apply IHP.
  - apply IHP.
  - transitivity j. { apply IHL. } { apply IHP. }
  - transitivity j. { apply IHL. } { apply IHP. }
  - transitivity j. { apply IHL. } { apply IHP. }
  - transitivity j. { apply IHL. } { apply IHP. }
  - apply IHL.
Qed.


Theorem item_j_le_term_max : forall {vt nt} s i j p q w w' t (g : @Grammar vt nt)
  (H: @item vt nt g s i j p q w w' t),
    Nat.le j (term_max g + 1).
Proof.
  intros vt nt s i j p q w w' t g.
  intros eta.
  induction eta
    as [ g r i I L
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r v i j p q w w' _t P IHP Sh
       | g l l' v i j k p1 q1 p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Rs Le Lb Sh
       | g l v i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rs Lb
       | g l l' v v' i j k p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh Fv Lb
       | g v u i j k l p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Lb
       ];
  try (apply IHP);
  try (apply IHL).
  - rewrite Nat.add_1_r. apply le_S. apply L.
  - rewrite Nat.add_1_r. apply le_n_S. apply L.
Qed.


Theorem item_i_le_p : forall {vt nt} s i j x q w w' t (g : @Grammar vt nt)
  (H: @item vt nt g s i j (Some x) q w w' t),
    Nat.le i x.
Proof.
  intros vt nt s i j x q w w' t g.
  intros eta.
  (* Need to remember that [p] is [Some x] *)
  remember (Some x) as p.
  (* Generalizing [x] is crucial here! *)
  generalize dependent x.
  induction eta
    as [ g r i I L
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r v i j p q w w' _t P IHP Sh
       | g l l' v i j k p1 q1 p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Rs Le Lb Sh
       | g l v i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rs Lb
       | g l l' v v' i j k p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh Fv Lb
       | g v u i j k l p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Lb
       ];
  try (apply IHP);
  try (apply IHL).
  - intros x E. discriminate E.
  - intros x E. destruct p1.
    + simpl in E. apply IHL in E. apply E.
    + simpl in E. apply IHP in E.
      apply item_i_le_j in LP as E'.
      transitivity j.
      * apply E'.
      * apply E.
  - intros x E. injection E as E. rewrite <- E.
    apply item_i_le_j in LP. apply LP.
  - intros x E. apply IHP in E as Le_j_x.
    assert (T: Some j = Some j). { reflexivity. }
    apply IHL in T as Le_i_j.
    transitivity j.
    + apply Le_i_j.
    + apply Le_j_x.
Qed.


Theorem item_some_p_iff_some_q : forall {vt nt} s i j p q w w' t (g : @Grammar vt nt)
  (H: @item vt nt g s i j p q w w' t),
    p = None <-> q = None.
Proof.
  assert (NoneEq: forall {A : Type}, @None A = @None A).
    { intros A. reflexivity. }
  intros vt nt s i j p q w w' t g.
  intros eta.
  induction eta
    as [ g r i I L
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r v i j p q w w' _t P IHP Sh
       | g l l' v i j k p1 q1 p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Rs Le Lb Sh
       | g l v i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rs Lb
       | g l l' v v' i j k p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh Fv Lb
       | g v u i j k l p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Lb
       ];
  try reflexivity;
  try (apply IHP);
  try (apply IHL).
  - destruct p1. destruct q1.
    + split. { intros H. discriminate H. } { intros H. discriminate H. }
    + exfalso. destruct IHL as [_ H]. apply H in NoneEq. discriminate.
    + destruct IHL as [H _]. apply H in NoneEq as H'.
      rewrite H'. simpl. apply IHP.
  - split. { intros H. discriminate. } { intros H. discriminate H. }
Qed.


Theorem item_p_le_q : forall {vt nt} s i j x y w w' t (g : @Grammar vt nt)
  (H: @item vt nt g s i j (Some x) (Some y) w w' t),
    Nat.le x y.
Proof.
  assert (NoneEq: forall {A : Type}, @None A = @None A).
    { intros A. reflexivity. }
  intros vt nt s i j x y w w' t g.
  intros eta.
  (* Need to remember that [p] is [Some x] *)
  remember (Some x) as p.
  remember (Some y) as q.
  (* Generalizing [x] is crucial here! *)
  generalize dependent y.
  generalize dependent x.
  induction eta
    as [ g r i I L
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r v i j p q w w' _t P IHP Sh
       | g l l' v i j k p1 q1 p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Rs Le Lb Sh
       | g l v i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rs Lb
       | g l l' v v' i j k p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh Fv Lb
       | g v u i j k l p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Lb
       ];
  try (apply IHL);
  try (apply IHP).
  - intros x E y F. discriminate E.
  - intros x E y F.
    destruct p1 eqn:Eq_p1.
    + simpl in E.
      destruct q1 eqn:Eq_q1.
      * simpl in F.
        apply IHL. apply E. apply F.
      * exfalso. apply item_some_p_iff_some_q in LP.
        destruct LP as [_ Abs].
        apply Abs in NoneEq. discriminate NoneEq.
    + simpl in E.
      destruct q1 eqn:Eq_q1.
      * exfalso. apply item_some_p_iff_some_q in LP.
        destruct LP as [Abs _].
        apply Abs in NoneEq. discriminate NoneEq.
      * apply IHP. apply E. apply F.
  - intros x E y F. injection E as E. injection F as F.
    rewrite <- E. rewrite <- F.
    apply item_i_le_j in RP. apply RP.
Qed.


Theorem item_q_le_j : forall {vt nt} s i j p x w w' t (g : @Grammar vt nt)
  (H: @item vt nt g s i j p (Some x) w w' t),
    Nat.le x j.
Proof.
  intros vt nt s i j p x w w' t g.
  intros eta.
  (* Need to remember that [p] is [Some x] *)
  remember (Some x) as q.
  (* Generalizing [x] is crucial here! *)
  generalize dependent x.
  induction eta
    as [ g r i I L
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r v i j p q w w' _t P IHP Sh
       | g l l' v i j k p1 q1 p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Rs Le Lb Sh
       | g l v i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rs Lb
       | g l l' v v' i j k p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh Fv Lb
       | g v u i j k l p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Lb
       ];
  try (apply IHL);
  try (apply IHP).
  - intros x E. discriminate E.
  - intros x E. apply IHP in E. apply le_S. apply E.
  - intros x E. destruct q1.
    + simpl in E. apply IHL in E.
      apply item_i_le_j in RP as E'.
      transitivity j.
      * apply E.
      * apply E'.
    + simpl in E. apply IHP in E.
      apply E.
  - intros x E. apply IHL in E.
    apply item_i_le_j in RP as E'.
      transitivity j.
      * apply E.
      * apply E'.
  - intros x E. apply IHL in E.
    apply item_i_le_j in RP as E'.
      transitivity j.
      * apply E.
      * apply E'.
  - intros x E. injection E as E. rewrite <- E.
    reflexivity.
  - intros x E. apply IHP in E as Le_x_k.
    assert (T: Some k = Some k). { reflexivity. }
    apply IHL in T as Le_k_l.
    transitivity k.
    + apply Le_x_k.
    + apply Le_k_l.
Qed.


Theorem weights_ge_0 : forall {vt nt} s i j p q w w' t
  (g : @Grammar vt nt) (H: @item vt nt g s i j p q w w' t),
    0 <= w /\ 0 <= w'.
Proof.
  intros vt nt s i j p q w w' t g.
  intros eta.

  induction eta
    as [ g r i I L
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r v i j p q w w' _t P IHP Sh
       | g l l' v i j k p1 q1 p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Rs Le Lb Sh
       | g l v i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rs Lb
       | g l l' v v' i j k p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh Fv Lb
       | g v u i j k l p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Lb
       ];
  try (apply IHP).

  - split. apply Rle_refl. apply Rle_refl.

  - destruct IHL as [L1 L2].
    destruct IHP as [P1 P2].
    split.
    + rewrite <- (Rplus_0_l 0).
      apply Rplus_le_compat.
      * apply L1.
      * apply P1.
    + rewrite <- (Rplus_0_l 0).
      apply Rplus_le_compat.
      * apply L2.
      * apply P2.

  - destruct IHL as [L1 L2].
    destruct IHP as [P1 P2].
    split.
    + rewrite <- (Rplus_0_l 0). rewrite <- (Rplus_0_r (0 + 0)).
      apply Rplus_le_compat.
        { apply Rplus_le_compat.
          - apply L1.
          - apply P1. }
        { apply omega_ge_0. }
    + rewrite <- (Rplus_0_l 0).
      apply Rplus_le_compat.
      * apply L2.
      * apply P2.

  - destruct IHL as [L1 L2].
    destruct IHP as [P1 P2].
    split.
    + rewrite <- (Rplus_0_l 0). rewrite <- (Rplus_0_r (0 + 0)).
      apply Rplus_le_compat.
        { apply Rplus_le_compat.
          - apply L1.
          - apply P1. }
        { apply omega_ge_0. }
    + rewrite <- (Rplus_0_l 0).
      apply Rplus_le_compat.
      * apply L2.
      * apply P2.

  - destruct IHL as [L1 L2].
    destruct IHP as [P1 P2].
    split.
    + apply L1.
    + rewrite <- 2?(Rplus_0_l 0). rewrite ?Rplus_assoc.
      apply Rplus_le_compat. { apply L2. }
      apply Rplus_le_compat. { apply P1. }
      apply Rplus_le_compat. { apply P2. }
      apply amort_weight_ge_0.

  - destruct IHL as [L1 L2].
    destruct IHP as [P1 P2].
    split.
    + rewrite <- (Rplus_0_l 0). rewrite <- (Rplus_0_r (0 + 0)).
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat. { apply L1. }
      apply Rplus_le_compat. { apply P1. }
      apply omega_ge_0.
    + rewrite <- (Rplus_0_l 0).
      apply Rplus_le_compat.
      * apply L2.
      * apply P2.

Qed.


Theorem in_vs_inside : forall {vt nt} s i j p q w w' t
  (g : @Grammar vt nt) (H: @item vt nt g s i j p q w w' t),
    costs g (in_span i j) <= w + w' + costs g (inf_s g s).
Proof.
  intros vt nt s i j p q w w' t g.
  intros eta.

  induction eta
    as [ g r i I L
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r1 r2 i j p q v w w' _t P IHP L Sh Lb
       | g r v i j p q w w' _t P IHP Sh
       | g l l' v i j k p1 q1 p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh
       | g l l' v v' i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Rs Le Lb Sh
       | g l v i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rs Lb
       | g l l' v v' i j k p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Sh Fv Lb
       | g v u i j k l p2 q2 w1 w2 w1' w2' _t1 _t2 LP IHL RP IHP Rv Lb
       ].

  - simpl. rewrite in_span_ii_empty.
    rewrite costs_nil. rewrite Rplus_0_l. rewrite Rplus_0_l.
    apply costs_ge_0.

  - rewrite in_span_Sj.
    Focus 2. apply (item_i_le_j (Rule r1) i j p q w w' _t g). apply P.
    simpl. rewrite (shift_term_inf g r1 r2 v j).
    + rewrite costs_app. rewrite costs_app.
      rewrite <- Rplus_assoc.
      apply (Rplus_le_compat_r (costs g [j])).
      apply IHP.
    + apply Sh.
    + apply Lb.

  - (* EM *)
    apply shift_empty_inf in Sh as InfEq.
    + simpl. simpl in IHP. rewrite InfEq. apply IHP.
    + apply Lb.

  - simpl. simpl in IHP.
    apply shift_inf_passive in Sh as H.
    rewrite <- H.
    apply IHP.

  - (* PS *)
    rewrite (in_span_split i j k).
    Focus 2. apply item_i_le_j in LP. apply LP.
    Focus 2. apply item_i_le_j in RP. apply RP.
    rewrite costs_app.
    apply shift_inf in Sh as E.
    simpl.
    rewrite <- E. rewrite costs_app.
    (* reorder the weights *)
    rewrite (Rplus_assoc w1 w2).
    rewrite <- (Rplus_assoc w2).
    rewrite (Rplus_reord4 w2 w1').
    rewrite <- (Rplus_assoc w1).
    (* one final reordering *)
    rewrite Rplus_reord2.
    apply Rplus_le_compat.
    + apply IHL.
    + apply IHP.

  - (* SU *)
    rewrite <- Rplus_assoc.
    rewrite ?(Rplus_shift_left w1').
    rewrite 3?(Rplus_shift_left (costs _ _)).
    rewrite (Rplus_shift_left w2').

    rewrite (in_span_split i j k).
    Focus 2. apply item_i_le_j in LP. apply LP.
    Focus 2. apply item_i_le_j in RP. apply RP.
    rewrite costs_app.
    rewrite 2?Rplus_assoc.
    apply Rplus_le_compat.

    + apply root_non_term in Rv as Rv'.
      destruct Rv' as [x Rv'].
      apply (shift_non_term_leaf_inf _ _ _ _ x) in Sh as [Sh1 Sh2].
      * simpl. rewrite Sh2. apply IHL.
      * apply Le.
      * rewrite Lb in Rv'. apply Rv'.

    + apply (Rle_trans _ (w2 + w2' + costs g (inf g v))).
      * apply IHP.
      * rewrite Rplus_assoc.
        apply Rplus_le_compat_l. apply Rplus_le_compat_l.
        apply (inf_cost_vs_omega g v (fst l)).
        apply Rv.

  - (* SA *)
    apply sister_is_root in Rs as Rv.

    rewrite <- Rplus_assoc.
    rewrite ?(Rplus_shift_left w1').
    rewrite 3?(Rplus_shift_left (costs _ _)).
    rewrite (Rplus_shift_left w2').
    rewrite 2?Rplus_assoc.

    rewrite (in_span_split i j k).
    Focus 2. apply item_i_le_j in LP. apply LP.
    Focus 2. apply item_i_le_j in RP. apply RP.
    rewrite costs_app.
    (* rewrite Rplus_reord1. *)
    apply Rplus_le_compat.
    + apply root_non_term in Rv as Rv'.
      destruct Rv' as [x Rv'].
      apply IHL.
    + apply (Rle_trans _ (w2 + w2' + costs g (inf g v))).
      * apply IHP.
      * rewrite Rplus_assoc.
        apply Rplus_le_compat_l. apply Rplus_le_compat_l.
        apply (inf_cost_vs_omega g v (fst l)).
        apply Rv.

  - (* FA *)

    rewrite (in_span_split i j k).
    Focus 2. apply item_i_le_j in LP. apply LP.
    Focus 2. apply item_i_le_j in RP. apply RP.
    rewrite costs_app.

    rewrite <- ?Rplus_assoc.
    rewrite 3?(Rplus_shift_left (costs _ _)).
    rewrite 2?Rplus_assoc.

    apply Rplus_le_compat.
    + simpl. simpl in IHL.
      apply foot_is_non_term_leaf in Fv as [v'Leaf [x LbNT]].
      apply (shift_non_term_leaf_inf _ _ _ v' x) in Sh as [_ InfEq].
      Focus 2. apply v'Leaf.
      Focus 2. apply LbNT.
      rewrite InfEq. apply IHL.

    + rewrite <- Rplus_assoc.
      apply (Rle_trans _ ( w2 + w2' + costs g (inf_s g (Node v)))).
      * apply IHP.
      * apply Rplus_le_compat_l.
        simpl.
        apply costs_inf_le_amort_weight.

  - (* RA *)

    rewrite <- ?Rplus_assoc.
    rewrite ?(Rplus_shift_left w1').
    rewrite 1?(Rplus_shift_left (omega _ _ _)).
    rewrite 2?Rplus_assoc.

    (* split the span *)
    rewrite (in_span_split i j l).
    Focus 2. apply (item_i_le_p) in LP. apply LP.
    Focus 2. apply (item_i_le_j) in RP.
      apply item_q_le_j in LP.
      transitivity k. apply RP. apply LP.
    rewrite (in_span_split j k l).
    Focus 2. apply item_i_le_j in RP. apply RP.
    Focus 2. apply item_q_le_j in LP. apply LP.
    rewrite ?costs_app.

    (* align [in_span j k] *)
    rewrite (Rplus_comm (costs g (in_span j k))).
    rewrite <- Rplus_assoc.
    apply Rplus_le_compat.
    Focus 2. rewrite <- Rplus_assoc. apply IHP.

    (* we still have to deal with [in_span i j] and [in_span j k] *)
    apply (Rle_trans _ (costs g (in_span i l))).
      { apply costs_ignore_gap.
        - apply item_i_le_p in LP. apply LP.
        - apply item_i_le_j in RP. apply RP.
        - apply item_q_le_j in LP. apply LP.
      }
    apply (Rle_trans _ (w1 + w1' + costs g (inf_s g (Node v)))).
      { apply IHL. }
    apply Rplus_le_compat_l.

    (* relation between [inf_s] and [omega] *)
    move Rv after IHP.
    apply (inf_cost_vs_omega _ _ u) in Rv as Ineq.
    simpl. apply Ineq.

Qed.


Theorem in_vs_inside_root : forall {vt nt} v v' i j p q w w' t
  (g : @Grammar vt nt) (H: @item vt nt g (Node v) i j p q w w' t),
    root g v = true ->
      costs g (in_span i j) <= w + w' + omega g v v'.
Proof.
  intros vt nt v v' i j p q w w' t g I R.
  apply (Rle_trans _ (w + w' + costs g (inf g v))).
  - assert (H: inf_s g (Node v) = inf g v).
      { simpl. reflexivity. }
    rewrite <- H. apply (in_vs_inside _ _ _ p q _ w' t). apply I.
  - apply Rplus_le_compat_l.
    apply (inf_root_anchor) in R as A.
    rewrite A.
    unfold costs. simpl.
    rewrite Rplus_0_l.
    unfold omega.
    unfold cost.
    apply Rplus_le_compat.
    + apply min_arc_weight_le.
    + apply min_tree_weight_le. reflexivity.
Qed.


Theorem monotonic : forall {vt nt} s i j p q w w' t
  (g : @Grammar vt nt) (H: @item vt nt g s i j p q w w' t),
    t <= w + w' + heuristic_s g s i j.
Proof.
  intros vt nt s i j p q w w' t g.
  intros eta.

  destruct eta
    as [ g r i I L
       | g r1 r2 i j p q v w w' _t P L Sh Lb
       | g r1 r2 i j p q v w w' _t P L Sh Lb
       | g r v i j p q w w' _t P Sh
       | g l l' v i j k p1 q1 p2 q2 w1 w2 w1' w2' _t1 _t2 LP RP Sh
       | g l l' v v' i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP RP Rv Rs Le Lb Sh
       | g l v i j k p1 q1 w1 w2 w1' w2' _t1 _t2 LP RP Rs Lb
       | g l l' v v' i j k p2 q2 w1 w2 w1' w2' _t1 _t2 LP RP Sh Fv Lb
       | g v u i j k l p2 q2 w1 w2 w1' w2' _t1 _t2 LP RP Rv Lb
       ].

  - (* AX *)
    (* simpl. rewrite Rplus_0_l.
    unfold heuristic'. *)
    rewrite Rplus_0_l. rewrite Rplus_0_l.
    simpl.
    unfold heuristic'.
    rewrite <- (Rplus_0_l 0).
    apply Rplus_le_compat.
    + apply amort_weight'_ge_0.
    + apply costs_ge_0.

  - (* SC *)
    unfold total'.
    apply Rplus_le_compat_l.
    simpl. unfold heuristic'.
    apply shift_amort_weight in Sh as Sh'. rewrite Sh'.
    rewrite Rplus_assoc.
    apply Rplus_le_compat_l.
    apply (cost_rest_Sj g i) in L.
    rewrite L.
    apply term_inf in Lb. rewrite Lb.
    rewrite <- Rplus_comm.
    rewrite cost_one.
    apply Rplus_le_compat_l.
    apply Rle_refl.

  - (* EM *)
    unfold total'.
    apply Rplus_le_compat_l.
    simpl. unfold heuristic'.
    apply Rplus_le_compat_r.
    rewrite <- (Rplus_0_r (_ _ r1)).
    apply shift_amort_weight in Sh as Sh'. rewrite Sh'.
    apply Rplus_le_compat.
    + apply Rle_refl.
    + apply costs_ge_0.

  - (* DE *)
    simpl. unfold total'.
    apply Rplus_le_compat_l.
    unfold heuristic. unfold heuristic'.
    unfold amort_weight. unfold amort_weight'.
    apply shift_sup_passive in Sh as H.
    rewrite <- H.
    apply Rle_refl.

  - (* PS *)
    apply Rmax_Rle'. split.

    + simpl. unfold total'.
      rewrite Rplus_reord2. rewrite (Rplus_assoc (w1 + _)).
      apply Rplus_le_compat_l.
      unfold heuristic'.
      apply shift_amort_weight in Sh as Sh'. rewrite Sh'.
      rewrite (Rplus_assoc (amort_weight' _ _)). rewrite (Rplus_comm (w2 + w2')).
      rewrite Rplus_assoc.
      apply Rplus_le_compat_l.
      rewrite (cost_rest_plus_in_r g i j k).
      * rewrite <- (Rplus_comm (costs g (rest g i k))).
        rewrite Rplus_assoc.
        apply Rplus_le_compat_l.
        rewrite Rplus_comm.
        assert (H: inf_s g (Node v) = inf g v).
          { simpl. reflexivity. }
        rewrite <- H.
        apply (in_vs_inside (Node v) j k p2 q2 w2 w2' _t2).
        apply RP.
      * apply item_i_le_j in RP. apply RP.
      * apply item_j_le_term_max in RP. apply RP.

    + unfold total. simpl.
      rewrite Rplus_reord2.
      rewrite (Rplus_comm (w1 + _)).
      rewrite (Rplus_assoc (w2 + _)).
      apply Rplus_le_compat_l.
      unfold heuristic. unfold heuristic'.
      rewrite (cost_rest_plus_in_l g i j k).
        Focus 2. apply item_i_le_j in LP. apply LP.
      rewrite <- Rplus_assoc. rewrite <- Rplus_assoc.
      apply Rplus_le_compat_r.
      apply shift_amort_weight' in Sh as Sh'.
      rewrite <- Sh'.
      rewrite Rplus_assoc. rewrite Rplus_reord3.
      apply Rplus_le_compat_l. rewrite Rplus_comm.
      assert (H: inf_s g (Rule l) = inf' g l). { simpl. reflexivity. }
      rewrite <- H.
      apply (in_vs_inside _ _ _ p1 q1 _ _ _t1). apply LP.


  - (* SU *)
    apply root_non_term in Rv as H.
    destruct H as [y RNonTerm].
    apply (shift_non_term_leaf_inf _ _ _ _ y) in Sh as H.
    destruct H as [InfVEmpty InfLEq].
    Focus 2. apply Le.
    Focus 2. rewrite RNonTerm in Lb. rewrite Lb. reflexivity.

    apply Rmax_Rle'. split.

    + unfold total'.
      rewrite (Rplus_shift_left (w1' + _)).
      rewrite <- Rplus_assoc.
      rewrite (Rplus_shift_left w1').
      rewrite ?(Rplus_assoc (w1 + _)).
      apply Rplus_le_compat_l.

      simpl. unfold heuristic'.
      apply shift_amort_weight in Sh as Sh'. rewrite Sh'.

      (* [costs g (inf g v)] is 0 because v is a non-terminal leaf *)
      rewrite InfVEmpty. rewrite costs_nil.
      rewrite Rplus_0_r.

      (* get rid of [amort_weight' g l] on both sides *)
      rewrite <- Rplus_assoc.
      rewrite ?(Rplus_shift_left (amort_weight' _ _)).
      rewrite (Rplus_comm w2).
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l.

      rewrite (cost_rest_plus_in_r g i j k).
      * rewrite Rplus_comm. rewrite <- ?Rplus_assoc.
        apply Rplus_le_compat_r.
        apply (in_vs_inside_root _ _ _ _ None None _ _ _t2).
        Focus 2. apply Rv.
        apply RP.
      * apply item_i_le_j in RP. apply RP.
      * apply item_j_le_term_max in RP. apply RP.

    + unfold total.

      rewrite <- Rplus_assoc.
      rewrite (Rplus_comm w1).
      rewrite ?(Rplus_shift_left w2').
      rewrite ?Rplus_assoc.

      apply Rplus_le_compat_l.
      apply Rplus_le_compat_l.

      simpl. unfold heuristic. unfold heuristic'.

      rewrite (cost_rest_plus_in_l g i j k).
        Focus 2. apply item_i_le_j in LP. apply LP.

      rewrite <- ?Rplus_assoc.
      apply Rplus_le_compat_r.

      apply (Rplus_le_reg_r (costs g (inf' g l))).
      rewrite (Rplus_shift_left w1').
      rewrite Rplus_reord1. rewrite Rplus_reord4.

      apply Rplus_le_compat.
      * assert (H: inf_s g (Rule l) = inf' g l).
          { simpl. reflexivity. }
        rewrite <- H.
        apply (in_vs_inside _ _ _ p1 q1 _ _ _t1). apply LP.
      * apply Rplus_le_compat.
        { unfold amort_weight. unfold omega.
          rewrite (Rplus_comm (arc_weight _ _ _)).
          apply sup_root in Rv as Rnil.
          (* Focus 2. apply L1. *)
          rewrite Rnil.
          (* assert (C0: costs g [] = 0).
            { unfold costs. simpl. reflexivity. } *)
          rewrite costs_nil. rewrite Rminus_0_r.
          apply Rplus_le_compat_l.
          apply min_arc_weight_le. }
        { apply shift_amort_weight' in Sh as E.
          rewrite <- (Rplus_0_l (costs g (inf' g l))).
          rewrite <- E.
          apply Rplus_le_compat.
          - apply amort_weight_ge_0.
          - apply Rle_refl. }

  - (* SA *)
    apply sister_is_root in Rs as Rv.
    apply root_non_term in Rv as H.
    destruct H as [y RNonTerm].

    apply Rmax_Rle'. split.

    + unfold total'.

      rewrite <- Rplus_assoc.
      rewrite ?(Rplus_shift_left w1').
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l. apply Rplus_le_compat_l.
      simpl. unfold heuristic'.

      (* get rid of [amort_weight' g l] on both sides *)
      rewrite <- ?Rplus_assoc.
      rewrite ?(Rplus_shift_left (amort_weight' _ _)).
      rewrite (Rplus_comm w2).
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l.

      rewrite (cost_rest_plus_in_r g i j k).
      * rewrite Rplus_comm. rewrite <- ?Rplus_assoc.
        apply Rplus_le_compat_r.
        rewrite (Rplus_shift_left w2').
        apply (in_vs_inside_root _ _ _ _ None None _ _ _t2).
        Focus 2. apply Rv.
        apply RP.
      * apply item_i_le_j in RP. apply RP.
      * apply item_j_le_term_max in RP. apply RP.

    + unfold total.

      rewrite (Rplus_comm w1).
      rewrite <- Rplus_assoc.
      rewrite ?(Rplus_shift_left w2').
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l. apply Rplus_le_compat_l.

      simpl. unfold heuristic. unfold heuristic'.

      rewrite (cost_rest_plus_in_l g i j k).
        Focus 2. apply item_i_le_j in LP. apply LP.

      rewrite <- ?Rplus_assoc.
      apply Rplus_le_compat_r.

      apply (Rplus_le_reg_r (costs g (inf' g l))).
      rewrite ?(Rplus_shift_left w1').
      rewrite Rplus_reord1. rewrite Rplus_reord4.

      apply Rplus_le_compat.
      * assert (H: inf_s g (Rule l) = inf' g l).
          { simpl. reflexivity. }
        rewrite <- H.
        apply (in_vs_inside _ _ _ p1 q1 _ _ _t1). apply LP.
      * apply Rplus_le_compat.
        { unfold amort_weight. unfold omega.
          rewrite (Rplus_comm (arc_weight _ _ _)).
          apply sup_root in Rv as Rnil.
          rewrite Rnil.
          rewrite costs_nil. rewrite Rminus_0_r.
          apply Rplus_le_compat_l.
          apply min_arc_weight_le. }
        { apply costs_inf_le_amort_weight'. }

  - (* FA *)
    apply foot_is_non_term_leaf in Fv as [v'Leaf [x EqNT]].

    apply Rmax_Rle'. split.

    + unfold total'. simpl.
      rewrite <- ?Rplus_assoc.
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l.
      apply Rplus_le_compat_l.
      rewrite <- ?Rplus_assoc.

      unfold heuristic'.
      rewrite (cost_rest_plus_in_r g i j k).
      Focus 2. apply item_i_le_j in RP. apply RP.
      Focus 2. apply item_j_le_term_max in RP. apply RP.

      rewrite (Rplus_comm (costs _ _)).
      rewrite <- ?Rplus_assoc.
      apply Rplus_le_compat_r.

      rewrite (Rplus_comm _ (costs _ _)).
      apply Rplus_le_compat.
      * apply (Rle_trans _ (w2 + w2' + costs g (inf_s g (Node v)))).
        { apply (in_vs_inside _ _ _ p2 q2 _ _ _t2).
          apply RP. }
        { apply Rplus_le_compat_l. simpl. apply costs_inf_le_amort_weight. }
      * unfold amort_weight'.
        move Sh after Lb.

        apply (shift_non_term_leaf_sup _ _ _ _ x) in Sh as Sup.
        Focus 2. apply v'Leaf.
        Focus 2. apply EqNT.
        rewrite Sup.

        apply (shift_preserves_head) in Sh as Head.
        rewrite Head.
        apply Rle_refl.

    + unfold total. simpl.

      rewrite <- ?Rplus_assoc.
      rewrite ?(Rplus_shift_left w2). rewrite (Rplus_comm w1).
      rewrite ?(Rplus_shift_left w2').
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l. apply Rplus_le_compat_l.

      unfold heuristic. unfold heuristic'.

      (* get rid of [costs g (rest g j k)] *)
      rewrite (cost_rest_plus_in_l g i j k).
      Focus 2. apply item_i_le_j in LP. apply LP.
      rewrite <- ?Rplus_assoc.
      apply Rplus_le_compat_r.

      (* get rid of [amort_weght g v] *)
      rewrite ?(Rplus_shift_left (amort_weight _ _)).
      rewrite (Rplus_comm w1).
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l.

      apply (Rle_trans _ (w1 + w1' + costs g (inf_s g (Rule l)))).
      * apply (in_vs_inside _ _ _ None None _ _ _t1). apply LP.
      * rewrite ?Rplus_assoc.
        apply Rplus_le_compat_l.
        apply Rplus_le_compat_l.
        simpl.
        move Sh after Lb.
        apply (shift_non_term_leaf_inf _ _ _ _ x) in Sh as [_ Inf].
        Focus 2. apply v'Leaf.
        Focus 2. apply EqNT.
        rewrite <- Inf.
        apply costs_inf_le_amort_weight'.

  - (* RA *)

    apply Rmax_Rle'. split.

    + unfold total. simpl.

      (* get rid of [w1 + w1'] *)
      rewrite <- Rplus_assoc.
      rewrite ?(Rplus_shift_left w1').
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l. apply Rplus_le_compat_l.

      unfold heuristic.

      (* get rid of [rest g i l] *)
      rewrite <- ?Rplus_assoc.
      apply Rplus_le_compat_r.

      (* match [amort_weight g v] and [omega g v u] *)
      rewrite (Rplus_comm w2).
      rewrite ?Rplus_assoc.
      rewrite <- (Rplus_0_r (amort_weight g v)).
      apply Rplus_le_compat.
        { apply amort_le_omega. }

      (* all elements on the right are positive *)
      apply weights_ge_0 in RP as [Ineq Ineq'].
      rewrite <- (Rplus_0_r 0). rewrite <- (Rplus_0_r (0 + 0)).
      rewrite Rplus_assoc.
      apply Rplus_le_compat. { apply Ineq. }
      apply Rplus_le_compat. { apply Ineq'. }
      apply amort_weight_ge_0.

    + unfold total. simpl.

      (* get rid of [w2 + w2'] *)
      rewrite (Rplus_comm w1).
      rewrite <- Rplus_assoc.
      rewrite ?(Rplus_shift_left w2').
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l.
      apply Rplus_le_compat_l.

      unfold heuristic.

      (* get rid of [amort_weight g u] *)
      rewrite <- ?Rplus_assoc.
      rewrite ?(Rplus_shift_left (amort_weight _ _)).
      rewrite (Rplus_comm w1).
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l.

      (* split the cost of the [rest] *)
      rewrite (costs_rest_gap i _ _ l).
      Focus 2. apply le_0_n.
      Focus 2. apply item_i_le_p in LP. apply LP.
      Focus 2. apply item_i_le_j in RP. apply RP.
      Focus 2. apply item_q_le_j in LP. apply LP.
      Focus 2. apply item_j_le_term_max in LP. apply LP.

      (* get rid of [rest g i l] *)
      rewrite <- ?Rplus_assoc.
      rewrite ?(Rplus_shift_left (_ _ (rest _ _ _))).
      rewrite (Rplus_comm w1).
      rewrite ?Rplus_assoc.
      apply Rplus_le_compat_l.

      (* join the in-spans *)
      apply (Rle_trans _ (costs g (in_span i l))).
        { apply costs_ignore_gap.
          - apply item_i_le_p in LP. apply LP.
          - apply item_i_le_j in RP. apply RP.
          - apply item_q_le_j in LP. apply LP.
        }
      apply (Rle_trans _ (w1 + w1' + costs g (inf_s g (Node v)))).
        { apply (in_vs_inside _ _ _ (Some j) (Some k) _ _ _t1).
          apply LP. }

      (* get rid of [w1 + w1'] *)
      rewrite <- Rplus_assoc.
      rewrite ?(Rplus_shift_left w1').
      apply Rplus_le_compat_l.

      (* match costs with omega *)
      apply inf_cost_vs_omega. apply Rv.

Qed.


Close Scope R_scope.

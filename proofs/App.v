From Coq Require Import Lists.List.
Import ListNotations.

Lemma app_suf_eq : forall {A : Type} (xs : list A) ys zs,
  xs = ys -> xs ++ zs = ys ++ zs.
Proof.
  intros A xs ys zs.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma app_pref_eq : forall {A : Type} (l l' pref : list A),
  pref ++ l = pref ++ l' -> l = l'.
Proof.
  intros A l l' pref.
  induction pref as [|h t].
  - simpl. intros H. apply H.
  - intros H. rewrite <- app_comm_cons in H. rewrite <- app_comm_cons in H.
    injection H as H. apply IHt in H. apply H.
Qed.

Lemma app_pref_eq' : forall {A : Type} (l l' pref : list A),
  l = l' -> pref ++ l = pref ++ l'.
Proof.
  intros A l l' pref.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Lemma app_pref_eq_r' : forall {A : Type} (l l' pref : list A),
  l = l' -> l ++ pref = l' ++ pref.
Proof.
  intros A l l' pref.
  intros H.
  rewrite H.
  reflexivity.
Qed.
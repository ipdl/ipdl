From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop.

(* The following file proves correspondences between ssreflect's notion of permutation and the Coq standard library's notion. *)

Require Import Sorting.Permutation.
Require Import Sorting.PermutSetoid.
From AAC_tactics
Require Import AAC.
From AAC_tactics
Require Instances.

Lemma list_contents_count_mem {A : eqType} (xs : seq A) x :
  count_mem x xs = let (f) := list_contents eq (fun x y => eq_comparable x y) xs  in f x.
  move: x; induction xs.
  done.
  simpl.
  intro.
  destruct (eqVneq a x); subst.
  simpl.
  destruct (eq_comparable x x).
  rewrite IHxs.
  done.
  move/eqP: n => n; rewrite eq_refl in n; done.
  destruct (eq_comparable a x).
  subst.
  rewrite eq_refl //= in i.
  rewrite IHxs //=.
Qed.

Lemma perm_eq_permutation {A : eqType} (xs ys : seq A) :
  perm_eq xs ys <-> permutation eq (fun x y => eq_comparable x y) xs ys.
  rewrite /permutation.
  rewrite /Multiset.meq /Multiset.multiplicity //=.
  split.
  intros.
  rewrite -list_contents_count_mem.
  rewrite -list_contents_count_mem.
  move/permP: H => h.
  done.
  intros.
  apply/allP => x Hx //=.
  rewrite !list_contents_count_mem; apply/eqP; done.
Qed.

Lemma perm_eq_Perm {A : eqType} (xs ys : seq A) :
  reflect (Permutation xs ys) (perm_eq xs ys).
  apply/(iffP idP).
  move/perm_eq_permutation.
  move/permutation_Permutation.
  elim => l; elim => h1 h2.
  suff : l = ys.
  intro; subst; done.
  clear h1; induction h2.
  done.
  subst; done.
  intro h; induction h.
  done.
  rewrite perm_cons //=.
  have -> : [:: y, x & l] = [:: y; x] ++ l by done.
  have -> : [:: x, y & l] = [:: x; y] ++ l by done.
  apply perm_cat.
  have -> : [:: y; x] = [:: y] ++ [:: x] by done.
  have -> : [:: x; y] = [:: x] ++ [:: y] by done.
  rewrite perm_catC perm_refl //=.
  apply perm_refl.
  eapply seq.perm_trans.
  apply IHh1.
  done.
Qed.

Lemma perm_ind {A : eqType} (P : seq A -> seq A -> Prop) :
  (P nil nil) ->
  (forall x xs ys, perm_eq xs ys -> P xs ys -> P (x :: xs) (x :: ys)) ->
  (forall x y xs, P (x :: y :: xs) (y :: x :: xs)) ->
  (forall xs ys zs, perm_eq xs ys -> P xs ys -> perm_eq ys zs -> P ys zs -> P xs zs) ->
  (forall xs ys, perm_eq xs ys -> P xs ys).
  intros.
  move/perm_eq_Perm: H3 => H3.
  induction H3; intros.
  done.
  move/perm_eq_Perm: H3 => H3.
  apply H0; done.
  done.
  move/perm_eq_Perm: H3_ => H3_.
  move/perm_eq_Perm: H3_0 => H3_0.
  apply (H2 l l' l''); done.
Qed.


Lemma Permutation_flatten {t} (x y : seq (seq t)) :
  Permutation x y ->
  Permutation (flatten x) (flatten y).
  intros.
  induction H.
  done.
  simpl in *.
  apply Permutation_app_head; done.
  simpl.
  etransitivity.
  apply Permutation_app_rot.
  apply Permutation_app_head.
  apply Permutation_app_comm.
  etransitivity.
  apply IHPermutation1.
  done.
Qed.

Lemma mkFlatten {T} (x y : seq T) : x ++ y = flatten [:: x; y].
  simpl.
  rewrite cats0 //=.
Qed.

Lemma flatten_cat_l {T} (x : seq (seq T)) y :
  y ++ flatten x = flatten (y :: x).
  done.
Qed.

Lemma flatten_cons_l {T} (x : seq (seq T)) (y : T) :
  y :: flatten x = flatten ([:: y] :: x).
  done.
Qed.

Lemma flatten_cat_in_r {T} (x y z : seq T)  :
  flatten [:: x; y ++ z] = flatten [:: x; y; z].
  simpl.
  rewrite catA !cats0 //=.
Qed.

Lemma flatten_cat_in_l {T} (x y : seq T) z:
  flatten ((x ++ y) :: z) = flatten [:: x, y & z].
  simpl.
  rewrite catA //=.
Qed.

Definition mkFlattenE t := (catA, @mkFlatten t, @flatten_cat_in_l t, cats0).
Ltac cat_perm_tac :=
  rewrite !mkFlattenE; apply Permutation_flatten.



From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple fintype.
From mathcomp Require Import choice path bigop.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Base Ipdl.Exp Lib.TupleLems Lib.setoid_bigop.
Require Import Lib.Crush Core Lems Lib.Set Pars Big Lib.OrdLems Lib.SeqOps.
Require Import Lib.Perm.
Require Import Sorting.Permutation.

Section Typ.
  Context {chan : Type -> Type}.

Definition tst (i o : chan (4.-tuple bool)) :=
  x <- new (7.-tuple bool) ;;
  pars [::
          Out x (Ret [tuple of nseq _ false]);
          Out o (a <-- Read i;; _ <-- Read x;; Ret a) ].

Definition tst2 (i o : chan (4.-tuple bool)) := 
  tst i o ||| tst o i.

Definition tags {t} {n} (v : n.-tuple (chan t)) : seq (@tagged chan) :=
  map tag v.

Lemma newvec_t_ord {n} {t} (o : seq (@tagged chan)) (f : n.-tuple (chan t) -> ipdl) :
  (forall cs, ipdl_t (tags cs ++ o) (f cs)) ->
  ipdl_t o (x <- newvec n @ t ;; f x).
  intros.
  apply newvec_t; intros.
  apply H.
Qed.

Definition ipdl_tE := (flatten_map1, cats0).

Lemma map_tag_enum {t} {n}  (v : n.-tuple (chan t)) :
  map (fun i => tag (v ## i)) (enum 'I_n) = tags v.
  rewrite map_comp.
  rewrite /tags.
  congr (_ _ _).
  rewrite map_tnth_enum //=.
Qed.

Lemma Outvec_t {n} {t} (v : n.-tuple (chan t)) k :
  ipdl_t (tags v) (Outvec v k).
  rewrite /tags.
  eapply Bigpar_t; intros.
  apply out_t.
  rewrite flatten_map1 //=.
  rewrite map_tag_enum.
  reflexivity.
Qed.


(* some other lemmas *)

Lemma map_mkChan_enum_map {t} {n} {A} (v : n.-tuple A) (f : A -> chan t) :
  map (fun i => tag (f (v ## i))) (enum 'I_n) = map tag ([tuple of map f v]).
  rewrite map_comp /comp //=.
  congr (_ _ _).
  rewrite map_comp /comp //=.
  congr (_ _ _).
  apply map_tnth_enum.
Qed.

Lemma map_tnth_enum_map {n} {a} {b} (f : a -> b) (v : n.-tuple a) :
  map (fun i => f (v ## i)) (enum 'I_n) = map f v.
  rewrite map_comp.
  congr (_ _ _).
  apply map_tnth_enum.
Qed.


Lemma flatten_map_cons {A B} (f : A -> B) (g : A -> seq B) xs :
  Permutation (flatten (map (fun a => f a :: g a) xs))
   ((map f xs) ++ (flatten (map g xs))).         
  induction xs; rewrite //=.
  rewrite IHxs //=.
  setoid_rewrite (cons_catE (f a)) at 1.
  setoid_rewrite (cons_catE (f a)) at 3.
  rewrite !mkFlattenE.
  apply Permutation_flatten.
  apply perm_skip.
  rewrite perm_swap.
  apply perm_skip.
  done.
Qed.

Lemma flatten_map_nil {A B} (xs : seq A):
  flatten (map (fun i => (nil : seq B)) xs) = nil.
  induction xs; rewrite //=.
Qed.


Lemma map_tuple_cons {n} {a b} (f : a -> b) (v : n.-tuple a) x :
  map_tuple f [tuple of x :: v] = [tuple of (f x) :: map_tuple f v].
  apply eq_tuple; done.
Qed.


Lemma enum0 : enum 'I_0 = nil.
  apply size0nil.
  rewrite size_enum_ord; done.
Qed.

Lemma tags0 t (v : 0.-tuple (chan t)) : tags v = nil.
  rewrite /tags.
  rewrite (tuple0 v) //.
Qed.

Lemma tags_cons_tuple {n} {a} (t : n.-tuple (chan a)) x :
  tags [tuple of x :: t] = (tag x) :: tags t.
  done.
Qed.

Lemma cons_mkcat {a} (x : a) t :
  x :: t = [:: x] ++ t.
  done.
Qed.

End Typ.

Ltac type_tac :=
  (progress set_tac) + (progress rewrite ?ipdl_tE //=) + done + (repeat lazymatch goal with
    | [ H : ipdl_t _ ?r |- ipdl_t _ ?r ] => eapply H
    | [ |- ipdl_t  _ (Out _ _) ] => eapply out_t; intros
    | [ |- ipdl_t  _ (Par _ _) ] => eapply par_t; intros
    | [ |- ipdl_t  _ (pars (_ :: _)) ] => eapply par_t; intros
    | [ |- ipdl_t  _ (pars [::]) ] => eapply zero_t; intros
    | [ |- ipdl_t  _ Zero] => eapply zero_t
    | [ |- ipdl_t  _ (New _ _)] => eapply new_t; intros
    | [ |- ipdl_t  _ (\||_(i < _) _)] => eapply Bigpar_t; intros; rewrite ?flatten_map1
    | [ |- ipdl_t  _ (x <- newvec _ @ _ ;; _)] => eapply newvec_t_ord; intros
    | [ |- ipdl_t  _ (Outvec _ _)] => apply Outvec_t
               end).

#[global]
Hint Resolve Permutation_app_comm : perm.
#[global]
Hint Resolve Permutation_app_tail : perm.
#[global]
Hint Resolve Permutation_app_head : perm.
#[global]
Hint Resolve Permutation_app : perm.
#[global]
Hint Resolve Permutation_add_inside : perm.
#[global]
Hint Resolve Permutation_cons_append : perm.
#[global]
Hint Resolve Permutation_app_rot : perm.
#[global]
Hint Resolve Permutation_app_swap_app : perm.
#[global]
Hint Resolve Permutation_app_middle : perm.
#[global]
Hint Resolve Permutation_cons_app : perm.
#[global]
Hint Resolve Permutation_elt : perm.
#[global]
Hint Resolve Permutation_middle : perm.
#[global]
Hint Resolve Permutation_refl : perm.
#[global]
Hint Constructors Permutation : perm.

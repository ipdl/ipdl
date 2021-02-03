
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple fintype.
From mathcomp Require Import choice path bigop.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Base Ipdl.Exp Lib.TupleLems Lib.setoid_bigop.
Require Import Lib.Crush Core Lems Lib.Set Pars Big Lib.OrdLems.

Inductive rset_t : rset -> set Chan -> set Chan -> Prop :=
| zero_t (i o : set Chan) :
    i = empty ->
    o = empty ->
    rset_t Zero i o
| out_t {t} (c : chan t) r (i o : set Chan) :
    wfRxn r ->
    i = rxn_inputs r ->
    o = singleton (mkChan c) -> 
    rset_t (Out c r) i o
| par_t r1 r2 i1 i2 o1 o2 (i' o' : set Chan) :
  rset_t r1 i1 o1 ->
  rset_t r2 i2 o2 ->
  disjoint o1 o2 ->
  i' = minus (union i1 i2) (union o1 o2) ->
  o' = union o1 o2 -> 
  rset_t (Par r1 r2) i' o'
| new_t {t} (X : seq (chan t)) k i o :
    (forall (c : chan t),
        (~ In X c -> rset_t (k c) i (union o (singleton (mkChan c))))) -> 
    rset_t (New t k) i o.

Lemma mkFresh1 {t} (c : chan t) : exists d, c <> d.
    destruct (mkFresh _ [:: c]).
    exists x.
    repeat set_tac.
Qed.

Lemma mkChan_neq_t {t1 t2} (c : chan t1) (c' : chan t2) :
  t1 <> t2 ->
  mkChan c <> mkChan c'.
  intros.
  unfold mkChan.
  crush.
Qed.

Lemma mkChan_eq_t {t} (c1 c2 : chan t) :
  c1 <> c2 ->
  mkChan c1 <> mkChan c2.
  intros.
  unfold mkChan.
  crush.
Qed.

Lemma mkChan_neq_neq {t} (c1 c2 : chan t) :
  mkChan c1 <> mkChan c2 ->
  c1 <> c2.
  intros.
  crush.
Qed.

Definition Union {A B} (f : A -> set B) : set B :=
  fun j => exists x, f x j.

Definition CondUnion {A B} (f : A -> set B) (p : A -> Prop) : set B :=
  fun j => exists x, p x /\ f x j.

Lemma disjoint_union {A B} (f : A -> set B) (s : set B) :
  (forall x, disjoint s (f x)) ->
  disjoint s (Union f).
  firstorder.
Qed.

Lemma Not_union {A B} (f : A -> set B) x :
  (forall y, ~ (f y) x) ->
  ~ Union f x.
  intros; intro.
  elim H0; intros.
  specialize (H x0); done.
Qed.

Ltac type_tac :=
  (progress set_tac) + done + (repeat lazymatch goal with
    | [ H : rset_t ?r _ _ |- rset_t ?r _ _ ] => eapply H
    | [ H : Union _ _ |- _ ] => destruct H
    | [ H : CondUnion _ _ _ |- _ ] => destruct H; destruct H
    | [ |- ~ Union _ _ ] => apply Not_union; intros
    | [ |- rset_t _ _ _ ] => econstructor; intros
    | [ H : existT _ ?ttt _ = existT _ ?ttt _ |- _ ] => 
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst 
    | [ H : forall z : chan _, ?c <> z -> _ |- _ ] =>
      let x := fresh "x" in
      let Hx := fresh "Hx" in
      destruct (mkFresh1 c) as [x Hx]; specialize (H x Hx)
    | [ |- (@mkChan ?x _) <> (@mkChan ?x _) ] => by apply mkChan_eq_t; congruence
    | [ |- (@mkChan ?x _) <> (@mkChan ?y _) ] => by apply mkChan_neq_t; congruence
    | [ H : mkChan ?a <> mkChan ?b |- ?a <> ?b ] => by apply mkChan_neq_neq; congruence
    | [ H : mkChan ?b <> mkChan ?a |- ?a <> ?b ] => by apply mkChan_neq_neq; congruence
    | [ |- wfRxn _ ] => eexists; repeat econstructor
               end).

Notation "x ::: I --> O" := (rset_t x I O) (at level 30).


Lemma Bigpar_t {n} (f : 'I_n -> rset) I O :
  (forall i, f i ::: (I i) --> (O i)) ->
  (forall i j, i <> j -> disjoint (O i) (O j)) ->
  (\||_(i < n) f i) ::: (minus (Union I) (Union O)) --> (Union O).
  move: f I O; induction n; intros.
  rewrite big_ord0.
  apply zero_t.
  type_tac.
  inversion H2.
  destruct x; done.
  type_tac.
  inversion H1.
  destruct x; done.

  rewrite big_ord_recl.
  eapply par_t.
  apply H.
  apply IHn.
  intros; apply H.
  intros.
  apply H0.
  intro h; inversion h.
  have //=: i = j.
  apply/eqP; rewrite eqE //=; apply/eqP; done.
  apply disjoint_union; intros.
  apply H0; done.
  type_tac.
  destruct H2.
  destruct (ordP x); subst.
  left; subst; done.
  right.
  split.
  firstorder.
  constructor; firstorder.
  firstorder.
  firstorder.
  firstorder.
  intro.
  destruct H3.
  destruct (ordP x); subst.
  firstorder.
  firstorder.
  firstorder.
  intro; destruct H3.
  destruct (ordP x); subst.
  done.
  firstorder.
  type_tac.
  inversion H1.
  destruct (ordP x); subst.
  left; done.
  right; firstorder.
  firstorder.
  firstorder.
Qed.

Lemma Bigpar_t_simple {n} (f : 'I_n -> rset) I O :
  (forall i, f i ::: (I i) --> (O i)) ->
  (forall i j, i <> j -> disjoint (O i) (O j)) ->
  (forall i j, disjoint (I i) (O j)) ->
  (\||_(i < n) f i) ::: ((Union I)) --> (Union O).
  intros.
  have -> : Union I = minus (Union I) (Union O).
  repeat set_tac.
  firstorder.
  apply Bigpar_t; done.
Qed.
  
Lemma newvec_t {n} {t} (X : seq (chan t)) (f : n.-tuple (chan t) -> rset) I O :
  (forall t, (forall j, ~ In X ((tnth t j))) -> (forall i j, i <> j -> tnth t i <> tnth t j) -> (f t) ::: I --> union O (Union (fun x => singleton (mkChan (tnth t x))))) ->
  (x <- newvec n @ t ;; f x) ::: I --> O.
  move: t X f I O.
  induction n.
  intros.
  have -> : O = union O (Union (fun x : 'I_0 => singleton (mkChan (tnth ([tuple] : 0.-tuple (chan t)) x)))).
    repeat set_tac.
    destruct H1.
    case x; done.
  apply H.
  case; done.
  case; done.
  intros.
  rewrite newvecS.
  apply (new_t X).
  intros.
  intros.
  apply (IHn _ (c :: X)).
  intros.
  have -> : union (union O (singleton (mkChan c)))
                  (Union (fun x : 'I_n => singleton (mkChan (tnth t0 x))))
            =
            union O (Union (fun x : 'I_(n.+1) => singleton (mkChan (tnth [tuple of c :: t0] x)))).
    repeat set_tac.
    right.
    exists ord0.
    rewrite tnth0 //=.
    right.
    destruct H4.
    exists (lift ord0 x).
    rewrite tnthS //=.
    left; left; done.
    destruct H4.
    destruct (ordP x); subst.
    rewrite tnth0 in H3.
    left; right; done.
    rewrite tnthS in H3.
    right.
    exists j; done.
  apply H.
  intros.
  simpl in H1.
  destruct (ordP j); subst.
  rewrite tnth0.
  done.
  rewrite tnthS.
  specialize (H1 j); repeat set_tac.
  intros.
  destruct (ordP i); destruct (ordP j); subst.
  done.
  rewrite (tnth0) tnthS.
  specialize (H1 j); repeat set_tac.
  rewrite tnth0 tnthS.
  specialize (H1 j0); repeat set_tac.
  rewrite !tnthS //=.
  apply H2.
  intro; subst.
  done.
Qed.

Definition tup_ok {n} {t} (t : n.-tuple (chan t)) :=
  (forall i j, i <> j -> tnth t i <> tnth t j).

Definition fresh_tup {n} {t} (X : seq (chan t)) (t : n.-tuple (chan t)) :=
  ((forall j, ~ In X ((tnth t j))) /\ tup_ok t).

(* Example *)
Definition tst (i o : chan 4) :=
  x <- new 7 ;;
  pars [::
          Out x (Ret [bv nseq _ false]);
          Out o (a <-- Read i;; _ <-- Read x;; Ret a) ].

Definition tst2 (i o : chan 4) := 
  tst i o ||| tst o i.

Lemma tst_t i o : i <> o ->
                  (tst i o) :::  [:: mkChan i]  --> [:: mkChan o].
  intros.
  apply (new_t nil); intros.
  repeat type_tac.
Qed.

Lemma tst2_t i o : i <> o -> tst2 i o ::: nil --> [:: mkChan i; mkChan o].
  intros.
  have H1 := tst_t i o H.
  have H2 := tst_t o i.
  specialize (H2 ltac:(crush)).
  repeat type_tac.
Qed.

Definition tst3 :=
  i <- new 4 ;;
  o <- new 4 ;;
  tst i o ||| tst o i.


Definition setE := (@complement_union, @complement_intersection).

Lemma tst3_t : tst3 ::: nil --> nil.
  apply (new_t nil); intros.
  apply (new_t [:: c]); intros.
  eapply par_t.
  apply tst_t.
  repeat set_tac.
  eapply tst_t.
  repeat set_tac.
  repeat type_tac.
  repeat type_tac.
  repeat type_tac.
Qed.

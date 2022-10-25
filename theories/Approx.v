(* This file extends the core IPDL logic to reason about
approximate equivalences. *)



Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype ssrnum ssralg.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Big Pars Lib.Set.  
Require Import FunctionalExtensionality.


(* Because we use a shallow embedding, we only keep track of the number of reactinos in protocols. It is currently up to the user to ensure that reactions are 
efficiently computable. *)

Fixpoint size_ipdl {chan} (p : @ipdl chan) (bnd : nat) : Prop :=
  match p with
  | Zero => bnd = 0
  | Out _ _ _ => bnd = 1
  | Par q r => exists k1 k2, size_ipdl q k1 /\ size_ipdl r k2 /\ bnd = k1 + k2
  | New t k => 
      forall x, size_ipdl (k x) bnd end.

Class IPDLBnd {chan} (p : @ipdl chan) (bnd : nat) := { _ : size_ipdl p bnd}.

#[global]
Instance IPDLBndZero {chan}  : @IPDLBnd chan Zero 0.
    constructor; done.
Qed.

#[global]
Instance IPDLBndOut {chan} {t} (c : chan t) r : IPDLBnd (c ::= r) 1.
    constructor; done.
Qed.

#[global]
Instance IPDLBndPar {chan} (p : @ipdl chan) q b1 b2 `{IPDLBnd _ p b1} `{IPDLBnd _ q b2} : IPDLBnd (p ||| q) (b1 + b2).
destruct H, H0.
constructor; exists b1; exists b2; split.
done.
split; done.
Qed.

#[global]
Instance IPDLBndNew {chan} {t} (k : chan t -> ipdl) b `{forall x, IPDLBnd (k x) b} : IPDLBnd (New t k) b.
    constructor; intros.
    intro.
    destruct (H x); done.
Qed.

#[global]
 Instance IPDLBndNewvec {chan} {t} {n} (k : n.-tuple (chan t) -> ipdl) b `{forall x, IPDLBnd (k x) b} : IPDLBnd (newvec n t k) b.
induction n.
simpl in *.
apply (H [tuple]).
simpl.
apply IPDLBndNew; intro.
apply IHn; intro.
apply H.
Qed.

#[global]
 Instance IPDLBndBig {chan} n (k : 'I_n -> @ipdl chan) b `{forall x, IPDLBnd (k x) b} : IPDLBnd (\||_(i < n) k i) (n * b).
induction n.
simpl.
rewrite big_ord0 mul0n; apply _.
rewrite big_ord_recl.
eapply IPDLBndPar.
done.
apply IHn.
done.
Qed.



(* Pairs (k, l), as in fig 14 *)
Definition err := (nat * nat)%type.
Definition err0 : err := (0, 0).

Definition err1 : err := (1, 0).

(* The error accumluated by transitivity *)
Definition add_err (e1 e2 : err) : err
      := (fst e1 + fst e2, maxn (snd e1) (snd e2)).

Notation "e1 +e e2" := (add_err e1 e2) (at level 50) : ipdl_scope.

(* The error accumulated by parallel composition *)
Definition comp_err (e : err) (bnd : nat) : err :=
  (fst e, snd e + bnd).

Lemma add_err0 e : add_err e err0 = e.
  rewrite /err0 /add_err addn0 maxn0; case e; done.
Qed.

Definition comp_err_comp (e : err) b1 b2 :
  comp_err (comp_err e b1) b2 = comp_err e (b1 + b2).
  rewrite /comp_err //= addnA //=.
Qed.

(* The below abstract type models our use of IPDL axioms for approximate equivalence. *)
Axiom AEqProt_base : forall chan, (nat -> @ipdl chan) -> (nat -> @ipdl chan) -> Prop.

Reserved Notation "p =a_( l , e ) q" (at level 40, format "p  =a_( l , e )  q").
Inductive AEqProt {chan} (lambda : nat) : err -> @ipdl chan -> @ipdl chan -> Prop :=
| AEq_base p q : AEqProt_base chan p q -> AEqProt lambda err1 (p lambda) (q lambda)
| AEq_zero : forall p1 p2 : ipdl, p1 =p p2 -> p1 =a_(lambda, err0) p2

| AEq_tr : forall (e1 e2 e3 : err) (p1 p2 p3 : ipdl),
            p1 =a_(lambda, e1) p2 -> p2 =a_(lambda, e2) p3 -> e3 = add_err e1 e2 -> p1 =a_(lambda, e3) p3
| AEq_sym e p q : p =a_(lambda, e) q -> q =a_(lambda, e) p
| AEq_comp : forall (e : err) (p1 p2 q : ipdl) bnd,
            p1 =a_(lambda, e) p2 -> size_ipdl q bnd -> (p1 ||| q) =a_(lambda, comp_err e bnd) (p2 ||| q)
| AEq_new t f1 f2 e :
    (forall c, (f1 c) =a_(lambda, e) (f2 c)) ->
    (x <- new t ;; f1 x) =a_(lambda, e) (x <- new t ;; f2 x)
where "p =a_( l , e ) q" := (AEqProt l e p q) : ipdl_scope.

Lemma AEq_newvec {chan} {n} {l} t (k1 k2 : n.-tuple (chan t) -> @ipdl chan) e :
  (forall v, k1 v =a_(l, e) k2 v) ->
  newvec n t k1 =a_(l, e) (newvec n t k2).
  intros.
  induction n.
  simpl.
  apply H.
  simpl.
  apply AEq_new => c.
  apply IHn.
  intros; apply H.
Qed.

Require Import RelationClasses.

#[global]
Instance refl_aeq {chan} {l} : Reflexive (@AEqProt chan l err0).
   intro.
   apply AEq_zero; done.
Qed.

#[global]
Instance sym_aeq {chan}  {l} e : Symmetric (@AEqProt chan l e).
   intros x y.
   move/AEq_sym; done.
Qed.

Require Import Setoid Relation_Definitions Morphisms.
Close Scope bool_scope.

(* This allows me to rewrite using exact equalities *)
#[global]
Instance proper_aeqprot {chan} {l} : Proper (eq ==> EqProt ==> EqProt ==> Basics.flip Basics.impl) (@AEqProt chan l).
    repeat intro. 
    eapply AEq_tr.
    apply AEq_zero; apply H0.
    eapply AEq_tr.
    apply H2.
    symmetry; apply AEq_zero; apply H1.
    done.
    subst.
    rewrite /add_err //= !addn0 !add0n.
    rewrite maxn0 max0n.
    case y; done.
Qed.

(* The below class is used to automate manipulations involving approximate equivalences. *)
Class RewritesWith {chan} {l} (x : @ipdl chan) y e (h : x =a_(l, e) y) (p : @ipdl chan) q e' := rewr_witness : (p =a_(l, e') q).

Lemma rewrite_RewritesWith {chan} {l} {x y} {e e'} (h : x =a_(l, e) y) p q `{RewritesWith chan l _ _ e h p q e'} : p =a_(l, e') q.
    apply rewr_witness.
Qed.

#[global]
Instance RewritesWith_id {chan} {l} (x : @ipdl chan) y e (h : x =a_(l, e) y) : RewritesWith x y e h x y e.
    apply h.
Qed.

#[global]
Instance RewritesWith_comp_l {chan} {l} (x : @ipdl chan) y e (h : x =a_(l, e) y) (p : ipdl) bnd `{IPDLBnd _ p bnd} : RewritesWith x y e h (x ||| p) (y ||| p) (comp_err e bnd).
    apply AEq_comp.
    apply h.
    destruct H; done.
Qed.

#[global]
Instance RewritesWith_comp_r {chan} {l} (x : @ipdl chan) y e (h : x =a_(l, e) y) p bnd `{IPDLBnd _ p bnd} : RewritesWith x y e h (p ||| x) (p ||| y) (comp_err e bnd).
    rewrite /RewritesWith.
    rewrite EqCompComm.
    rewrite (EqCompComm p).
    apply AEq_comp.
    apply h.
    destruct H; done.
Qed.

#[global]
Instance RewritesWith_pars_head {chan} {l} (x : @ipdl chan) y e (h : x =a_(l, e) y) ps bnd `{IPDLBnd _ (pars ps) bnd} :
  RewritesWith x y e h (pars (x :: ps)) (pars (y :: ps)) (comp_err e bnd).
   rewrite /RewritesWith.
   rewrite !pars_cons.
   apply RewritesWith_comp_l.
   done.
   done.
Qed.

#[global]
Instance RewritesWith_pars_cons {chan} {l} (x : @ipdl chan) y e (h : x =a_(l, e) y) ps qs p e' `{RewritesWith chan l x y e h (pars ps) (pars qs) e'} bnd `{IPDLBnd _ p bnd} :
   RewritesWith x y e h (pars (p :: ps)) (pars (p :: qs)) (comp_err e' bnd).
   rewrite /RewritesWith.
   rewrite !pars_cons.
   apply RewritesWith_comp_r.
   apply H.
   done.
Qed.

Ltac arewrite h :=
   eapply AEq_tr; [ eapply (rewrite_RewritesWith h); apply _ | | ].


Ltac arewrite_inv h :=
   eapply AEq_tr; [ eapply (rewrite_RewritesWith (AEq_sym _ _ _ _ h)); apply _ | | ].


Lemma exact_tr {chan} {l} (p : @ipdl chan) p' q e : p' =p p -> p =a_(l, e) q -> p' =a_(l, e) q.
  intros.
  rewrite H.
  done.
Qed.


Ltac atrans := eapply AEq_tr.
Ltac etrans := eapply exact_tr.

Lemma AEq_comp_r {chan} {l} (e : err) (p1 : @ipdl chan) p2 q bnd `{IPDLBnd _ q bnd} :
  p1 =a_(l, e) p2 -> (q ||| p1) =a_(l, comp_err e bnd) (q ||| p2).
  intros.
  arewrite H0.
  reflexivity.
  rewrite /add_err /err0 //= addn0 maxn0 //=.
Qed.

Lemma AEq_err_eq {chan} {l} e1 e2 (p1 p2 : @ipdl chan) :
  e1 = e2 ->
  p1 =a_(l, e1) p2 ->
  p1 =a_(l, e2) p2.
  intro; subst; done.
Qed.

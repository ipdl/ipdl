From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple fintype.
From mathcomp Require Import choice path bigop.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Base Ipdl.Exp Lib.TupleLems Lib.setoid_bigop.
Require Import Lib.Crush Lib.Set.

Inductive rset : Type :=
  | Zero : rset
  | Out {t} (c : chan t) : rxn t -> rset
  | Par : rset -> rset -> rset 
  | New t : (chan t -> rset) -> rset.

Fixpoint chans (r : rset) : set Chan :=
  match r with
    | Zero => empty
    | Out _ c r => add (rxn_inputs r) (mkChan c)
    | Par r1 r2 => union (chans r1) (chans r2)
    | New t k =>
      fun x => forall c, mkChan c <> x -> chans (k c) x
                                      end.

Fixpoint inputs (r : rset) : set Chan :=
  match r with
    | Zero => empty
    | Out _ _ r => rxn_inputs r
    | Par r1 r2 => union (inputs r1) (inputs r2)                             
    | New t k =>
      fun x => forall c, mkChan c <> x -> inputs (k c) x end.

Fixpoint outputs (r : rset) : set Chan :=
  match r with
    | Zero => empty
    | Out _ c _ => singleton (mkChan c)                
    | Par r1 r2 => union (outputs r1) (outputs r2)
    | New t k =>
      fun x => forall c, mkChan c <> x -> outputs (k c) x end.

Coercion chans : rset >-> set.

Notation "x ||| y" := (Par x y) (at level 41, right associativity) : ipdl_scope.

Delimit Scope ipdl_scope with ipdl.

Notation "x <-- c ;; k" := (Bind c (fun x => k)) (at level 41, right associativity).

Axiom notin_mono : forall t (f : chan t -> rset) x j,
    ~ In (f x) j ->
    ~ In (New _ f) j.

Axiom not_output_mono : forall t (f : chan t -> rset) x j,
    ~ outputs (f x) j ->
    ~ outputs (New _ f) j.

Axiom mkFresh : forall t (l : list (chan t)), 
    exists (c : chan t), ~ In l c.

(* Used for some lemmas. *)
Lemma exists_chan : forall (t : type), exists (c : chan t), True.
   intros.
   move: (mkFresh t nil).
   elim.
   intros; done.
Qed.

Lemma chan_separated : forall (t : type) (c : chan t), exists c2, c <> c2.
intros.
   destruct (mkFresh t [:: c]).
   exists x.
   repeat set_tac.
Qed.

Inductive EqProt : rset -> rset -> Prop := 
  | EqRefl r : EqProt r r
  | EqSym r1 r2 : EqProt r1 r2 -> EqProt r2 r1
  | EqTr r1 r2 r3 : EqProt r1 r2 -> EqProt r2 r3 -> EqProt r1 r3
       
  | EqOut t (c : chan t) (r1 : rxn t) (r2 : rxn t) :
      EqRxn _ r1 r2 ->
      EqProt (Out c r1) (Out c r2)

  | EqPar r r1 r2 : EqProt r1 r2 -> 
    EqProt (Par r r1) (Par r r2)
                                              
  | EqNew {t} k1 k2 :
      (forall c, ~ In (New t k1) (mkChan c) -> ~ In (New t k2) (mkChan c) -> EqProt (k1 c) (k2 c)) ->
      EqProt (New t k1) (New t k2)
  | Absorb P Q :
      outputs P = empty ->
      (forall c, inputs P c -> chans Q c) ->
      EqProt (Par P Q) Q

  | ParSym r1 r2 : EqProt (Par r1 r2) (Par r2 r1)

  | ParAssoc r1 r2 r3 : EqProt (Par r1 (Par r2 r3)) (Par (Par r1 r2) r3)
                               
  | NewNew t1 t2 k :
      EqProt (New t1 (fun c => New t2 (fun c' => k c c')))
              (New t2 (fun c' => New t1 (fun c => k c c')))
  | NewComp t r k :
      EqProt (Par (New t k) r)
                 (New t (fun c => Par (k c) r))
  | NewUnused t r :
      EqProt (New t (fun _ => r))
                 r
  | Replacement {t1 t2} (c1 : chan t1) (c2 : chan t2) r k1 k2 :
      EqRxn _ (x <-- r ;; y <-- k1 x ;; Ret {{ x, y }})
              (x <-- r ;; y <-- k2 x ;; Ret {{ x, y }}) ->
      EqProt (Par (Out c1 r) (Out c2 (x <-- Read c1 ;; k1 x)))
             (Par (Out c1 r) (Out c2 (x <-- Read c1 ;; k2 x)))

  (* Derived from the Unused rule *)            
  | RUndep {t1 t2} (a : chan t1) (b : chan t2) 
           (r1 : rxn t1) (r2 : rxn t2) :
      List.Forall (fun x => In (rxn_inputs r2) x) (rxn_inputs r1) ->
      EqProt (Par (Out a r1) (Out b (Bind (Read a) (fun _ => r2))))
                      (Par (Out a r1) (Out b r2))
  | RFold {t1 t2} (a : chan t1) (r : rxn t2) k :
      EqProt (New t2 (fun c => Par (Out c r) (Out a (x <-- Read c ;; k x))))
                 (Out a (x <-- r ;; k x)).


               
  (*
     r1, r2 equivalent reactions
     ----
     Out c r1 = Out c r2
   *)
    

  (*
     substitution
  *)
  (* 
     hidden resource
  *)
               
Add Parametric Relation : (rset) (EqProt ) 
                                       reflexivity proved by (EqRefl )
                                       symmetry proved by (EqSym )
                                           transitivity proved by (EqTr ) as mod_rel.

Lemma RRemove {t1} (r : rxn t1) (P : rset) :
    (forall x : Chan, In (rxn_inputs r) x -> In P x) ->
  EqProt (New t1 (fun a => Par (Out a r) P))
             P.
  intros.
  rewrite -NewComp.
  apply Absorb.
  simpl.
  set_tac.
  destruct a as [t a].
  destruct (type_eq_dec t t1); subst.
  destruct (chan_separated _ a) as [c Hc].
  specialize (H0 c).
  have: singleton (mkChan c) (mkChan a).
  apply H0.
  intro h.
  have: a = c.
  apply Eqdep.EqdepTheory.inj_pair2; done.
  intro; congruence.
  intro h; inversion h.
  have: a = c.
  apply Eqdep.EqdepTheory.inj_pair2; done.
  congruence.

  destruct (exists_chan t1) as [x _].
  specialize (H0 x).
  have: singleton (mkChan x) (mkChan a).
  apply H0.
  intro h; inversion h; subst; done.
  intro h; inversion h; subst; done.

  simpl; intros.
  apply H.

  have: exists c0 : chan t1, mkChan c0 <> c.
  destruct c as [t c].
  destruct (type_eq_dec t t1); subst.
  destruct (chan_separated _ c) as [x Hx].
  exists x.
  intro h.
  have: c = x by apply Eqdep.EqdepTheory.inj_pair2.
  congruence.
  destruct (exists_chan t1) as [x _].
  exists x.
  intro h; inversion h; subst; done.
  elim => c0 Hc0.
  eapply H0.
  apply Hc0.
Qed.


Declare Scope ipdl_scope.
Delimit Scope ipdl_scope with ipdl.

Notation "x ||| y" := (Par x y) (at level 41, right associativity) : ipdl_scope.

Notation "x <- 'new' t ;; P" := (New t (fun x => P)) (at level 41, right associativity) : ipdl_scope.

Notation prot0 := Zero.


Infix "~=" := (EqProt) (at level 60).

(* Basic lemmas *)

Lemma EqCong (r1 r2 s1 s2 : rset ) :
  EqProt r1 s1 -> EqProt r2 s2 -> EqProt (r1 ||| r2)%ipdl (s1 ||| s2)%ipdl.
  intros.
  etransitivity.
  apply EqPar.
  apply H0.
  rewrite ParSym.
  rewrite (ParSym s1).
  apply EqPar.
  done.
Qed.

Lemma EqPar_l (r : rset) r1 r2 :
  EqProt r1 r2 -> EqProt (r1 ||| r)%ipdl (r2 ||| r)%ipdl.
  intros; eapply EqCong.
  done.
  reflexivity.
Qed.

Lemma NewComp_r t (r : rset) k :
   EqProt (Par r (New t k))  (New t (fun c => Par r (k c))).
  intros.
  rewrite ParSym NewComp.
  apply EqNew; intros.
  apply ParSym.
Qed.

Open Scope ipdl.

Lemma eq_par0 (r : rset) : EqProt r (r ||| prot0).
  rewrite ParSym.
  rewrite Absorb //=.
Qed.

Lemma eq_0par r :
    EqProt r (prot0 ||| r).
    rewrite ParSym -eq_par0 //=.
Qed.

Require Import Setoid Relation_Definitions Morphisms.
Close Scope bool_scope.

Add Parametric Morphism : (Par)
   with signature EqProt  ==> EqProt  ==> EqProt  as par_mor.
  intros; apply EqCong; done.
Qed.

Add Parametric Morphism t : (New t)
   with signature (pointwise_relation _ (EqProt)) ==> EqProt as new_rel.
  intros.
  apply EqNew.
  intros.
  rewrite /pointwise_relation in H.
  done.
Qed.

Add Parametric Morphism t (c : chan t) : (Out c) with signature
    EqRxn t ==> EqProt as out_rel.
  intros; apply EqOut; done.
Qed.

(** Setoid instance **)

Canonical rset_setoid : Setoid.setoid :=
  {| Setoid.car := rset; Setoid.eqv := EqProt |}.

Instance rset_setoid_monoidLaws : @Setoid.monoidLaws (rset_setoid) prot0 Par.
    constructor.
    apply _.
    simpl.
    rewrite /Setoid.eqv.
    rewrite //=.
    intros.
    rewrite ParAssoc; reflexivity.
    intros.
    symmetry.
    rewrite -eq_par0; reflexivity.
    intros.
    rewrite ParSym.
    rewrite -eq_par0; reflexivity.
Qed.

Instance rset_setoid_comMonoid : @Setoid.comMonoidLaws (rset_setoid) prot0 Par.
    constructor.
    apply _.
    intros; apply ParSym.
Qed.

Definition copy {t} (c : chan t) : rxn t := (x <-- Read c ;; Ret x).

Class NewLike {A} (f : (A -> rset) -> rset) :=
  {
  newUnused : forall r, f (fun _ => r) ~= r;
  newComp : forall k r, f k ||| r ~= f (fun c => k c ||| r);
  newCong : forall k1 k2, (forall x, k1 x ~= k2 x) -> f k1 ~= f k2;
                                                              }.
Instance New_NewLike t : NewLike (New t).
   constructor.
   intros; apply NewUnused.
   intros; apply NewComp.
   intros; apply EqNew.
   intros; apply H.
Qed.

Check NewComp_r.
Lemma newComp_r {A} (f : (A -> rset) -> rset) `{NewLike _ f} k r :
  r ||| f k ~= f (fun c => r ||| k c).
  rewrite ParSym.
  rewrite newComp.
  apply newCong; intros.
  apply ParSym.
Qed.


Lemma eq_EqRefl r1 r2 :
  r1 = r2 -> r1 ~= r2.
  intro; subst; done.
Qed.

Open Scope bool_scope.




(* old rules that are now lemmas *)
Lemma RTr  {t1 t2 t3} (a : chan t1) (b : chan t2) (r1 : rxn t1) (r2 : rxn t2) 
        (m : chan t3) :
      In (rxn_inputs r1)  (mkChan m) ->
      In (rxn_inputs r2)  (mkChan a) ->
      wfRxn r2 ->
      EqProt (Par (Out a r1) (Out b r2)) (Par (Out a r1) (Out b (_ <-- (Read m) ;; r2))).
  intros.
  have Hr1 : r1 =r (_ <-- Read m ;; r1) by apply EqMkRead.
  rewrite Hr1.
  have Hr2 : r2 =r (_ <-- Read a ;; r2) by apply EqMkRead.
  etransitivity.
  apply EqCong.
  done.
  apply EqOut.
  apply Hr2.

  erewrite (Replacement _ _ _ _ (fun x => _ <-- Read m ;; r2)); last first.
  simp_rxn; symmetry; simp_rxn.
  r_swap 1 2.
  rewrite EqReadSame.
  done.
  rewrite -Hr1.
  have -> : (_ <-- Read a ;; _ <-- Read m ;; r2) =r (_ <-- Read m ;; r2).
  r_swap 0 1.
  apply EqBind_r; intro.
  rewrite -Hr2 //=.
  apply EqRefl.
Qed.
  
Lemma RSubst {t1 t2} (a : chan t1) (b : chan t2) (r1 : rxn t1) (k : t1 -> rxn t2) :
      isDet _ r1 ->
      EqProt (Par (Out a r1) (Out b (Bind (Read a) k)))
              (Par (Out a r1) (Out b (Bind r1 (fun x => Bind (Read a) (fun _ => (k x)))))).
  intros.
  rewrite EqBindC.
  apply Replacement.
  induction r1.
  done.
  simp_rxn; symmetry; simp_rxn.
  done.
  symmetry; simp_rxn; rewrite EqReadSame; done.
  simp_rxn; symmetry.
  simp_rxn.
  r_swap 1 2.
  rewrite EqBindSame //=.
  apply EqBind_r; intros.
  rewrite EqBindSame //=.
  destruct H; done.
  destruct H; done.
Qed.


(* Notations *)


Notation "x ## i" := (tnth x i) (at level 40) : ipdl_scope.

Notation "c ::= r" := (Out c r) (at level 40) : ipdl_scope.

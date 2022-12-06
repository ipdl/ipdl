From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple fintype.
From mathcomp Require Import choice path bigop ssrnum ssralg.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Base Ipdl.Exp Lib.TupleLems Lib.setoid_bigop.
Require Import Lib.Set.

(* IPDL protocols. Note that the New combinator takes in a *coq function*, thus giving us a higher-order syntax. Since 'chan' is an abstract type, we are guaranteed that these coq functions can only 'pass around' channels, but not inspect them in any way.*)
Inductive ipdl {chan} : Type :=
    Zero : ipdl
| Out : forall {t : Type}, chan t -> @rxn chan t -> ipdl
| Par : ipdl -> ipdl -> ipdl
| New : forall (t : Type) , (chan t -> ipdl) -> ipdl.

Declare Scope ipdl_scope.
Delimit Scope ipdl_scope with ipdl.
Open Scope ipdl_scope.

Infix "::=" := (Out) (at level 40) : ipdl_scope.
Infix "|||" := Par (at level 41, right associativity) : ipdl_scope.

Notation "x <- 'new' t ;; k" := (New t (fun x => k)) (at level 41, right associativity).
Notation prot0 := Zero.

(* Typing for IPDL protocols. ipdl_t C P means that 
  P only outputs on the channels in C, and each channel only has one definition. We do *not* track inputs; thus, P might red from some ambient channel in the type environment.
*)
Inductive ipdl_t {chan} : seq tagged -> @ipdl chan -> Prop :=
out_t : forall (t : Type) (o : chan t) (r : rxn t),
            ipdl_t [:: tag o] (o ::= r)
| par_t : forall (o1 o2 o : seq tagged) (p1 p2 : ipdl),
            ipdl_t o1 p1 ->
            ipdl_t o2 p2 ->
            Permutation.Permutation o (o1 ++ o2) -> ipdl_t o (p1 ||| p2)
| perm_t : forall (o1 o2 : seq tagged) (p : ipdl),
            Permutation.Permutation o1 o2 -> ipdl_t o1 p -> ipdl_t o2 p
| new_t : forall (t : Type) (o : seq tagged) (f : chan t -> ipdl),
            (forall c : chan t, ipdl_t (tag c :: o) (f c)) ->
            ipdl_t o (x <- new t;; f x)
| zero_t : ipdl_t [::] prot0.


Reserved Notation "p =p q" (at level 50).

(* EqProt_base stands in for arbitrary semantic equalities 
 that are lifted into the equational system. This is necessary for introducing axioms into the system. *)
Axiom EqProt_base : forall chan, @ipdl chan -> @ipdl chan -> Prop.


(* Exact equivalence of IPDL protocols. *)
    Inductive EqProt {chan} : @ipdl chan -> @ipdl chan -> Prop :=
    | EqAxiom p q : EqProt_base chan p q -> EqProt p q
    (* necessary for soundness *)
    |  EqRefl : forall r : ipdl, r =p r
    | EqSym : forall r1 r2 : ipdl, r1 =p r2 -> r2 =p r1
    | EqTr : forall r1 r2 r3 : ipdl, r1 =p r2 -> r2 =p r3 -> r1 =p r3
    | EqCongReact : forall (t : Type) (c : chan t) (r1 r2 : rxn t),
                r1 =r r2 -> c ::= r1 =p c ::= r2
    | EqCongComp : forall r r1 r2 : ipdl, r1 =p r2 -> r ||| r1 =p r ||| r2
    | EqCongNew : forall (t : Type) (k1 k2 : chan t -> ipdl),
                (forall c : chan t, k1 c =p k2 c) ->
                x <- new t;; k1 x =p x <- new t;; k2 x
    | EqCongCompZero : forall P : ipdl, P ||| prot0 =p P
    | EqZero : forall P : ipdl, ipdl_t [::] P -> P =p prot0
    | EqCompComm : forall r1 r2 : ipdl, r1 ||| r2 =p r2 ||| r1
    | EqCompAssoc : forall r1 r2 r3 : ipdl,
                r1 ||| r2 ||| r3 =p (r1 ||| r2) ||| r3
    | EqNewExch : forall (t1 t2 : Type) (k : chan t1 -> chan t2 -> ipdl),
                c <- new t1;; c' <- new t2;; k c c' =p
                c' <- new t2;; c <- new t1;; k c c'
    | EqCompNew : forall (t : Type) (r : ipdl) (k : chan t -> ipdl),
                (x <- new t;; k x) ||| r =p c <- new t;; k c ||| r
    | EqSubsume : forall (t1 t2 t3 : Type) (c : chan t1) (d : chan t3)
                (k1 : t3 -> rxn t1) (e : chan t2) 
                (k2 : t1 -> rxn t2),
                c ::= (x <-- Read d;; k1 x) ||| e ::= (x <-- Read c;; k2 x) =p
                c ::= (x <-- Read d;; k1 x)
                ||| e ::= (_ <-- Read d;; x <-- Read c;; k2 x)
    | EqFold : forall (t1 t2 : Type) (r1 : rxn t1) 
                (c2 : chan t2) (k : t1 -> rxn t2),
                c <- new t1;; c ::= r1 ||| c2 ::= (x <-- Read c;; k x) =p
                c2 ::= (x <-- r1;; k x)
    | EqSubst : forall (t1 t2 : Type) (c : chan t1) 
                    (d : chan t2) (r : rxn t1) (k : t1 -> rxn t2),
                isDet t1 r ->
                c ::= r ||| d ::= (x <-- Read c;; k x) =p
                c ::= r ||| d ::= (x <-- r;; k x)
    | EqUnused : forall (t1 t2 : Type) (c : chan t1) 
                    (r : rxn t1) (d : chan t2) (r2 : rxn t2),
                (forall t (c : chan t), can_read c r -> reads_from c r2) ->
                c ::= r ||| d ::= (_ <-- Read c;; r2) =p
                                                            c ::= r ||| d ::= r2
    | EqDiverge : forall t (c : chan t) r,
                c ::= (x <-- Read c ;; r x) =p c ::= Read c
    | EqSplitBranch : forall t (c : chan t) (b : chan bool) (l r : chan t -> rxn t),
        c ::= (x <-- Read b ;; if x then l c else r c) =p
        (L <- new t ;; R <- new t ;; (L ::= (_ <-- Read b ;; l c) ||| R ::= (_ <-- Read b ;; r c) ||| c ::= (x <-- Read b ;; if x then Read L else Read R)))                                                           
                                                           
      where "p =p q" := (EqProt p q) : ipdl_scope.

     Add Parametric Relation {C} : (@ipdl C) (EqProt)
                                      reflexivity proved by EqRefl
                                      symmetry proved by EqSym
                                      transitivity proved by EqTr as eqprot_rel.

     Lemma EqCong {C} :
       forall r1 r2 s1 s2 : @ipdl C, r1 =p s1 -> r2 =p s2 -> r1 ||| r2 =p s1 ||| s2.
       intros.
       etransitivity.
       apply EqCongComp.
       apply H0.
       rewrite EqCompComm.
       etransitivity.
       apply EqCongComp.
       apply H.
       apply EqCompComm.
     Qed.

Require Import Setoid Relation_Definitions Morphisms.
Close Scope bool_scope.



Add Parametric Morphism {C} : (@Par C)
   with signature EqProt  ==> EqProt  ==> EqProt  as par_mor.
  intros; apply EqCong; done.
Qed.

Add Parametric Morphism {C} t : (@New C t)
   with signature (pointwise_relation _ (EqProt)) ==> EqProt as new_rel.
  intros.
  apply EqCongNew.
  intros.
  rewrite /pointwise_relation in H.
  done.
Qed.

Add Parametric Morphism {C} t (c : C t) : (@Out C _ c) with signature
    EqRxn t ==> EqProt as out_rel.
  intros; apply EqCongReact; done.
Qed.

Open Scope bool_scope.


     Lemma RRemove {chan} :
       forall (t1 : Type) (r : chan t1 -> rxn t1) (P : ipdl),
       a <- new t1;; a ::= (r a) ||| P =p P.
       intros.
       rewrite -EqCompNew.
       have h: (x <- new t1 ;; x ::= r x) =p prot0.
          apply EqZero.
          eapply new_t; intros.
          apply out_t.
       rewrite h.
       rewrite EqCompComm.
       rewrite EqCongCompZero //=.
     Qed.

     Lemma EqCongComp_l {C} : forall r r1 r2 : @ipdl C, r1 =p r2 -> r1 ||| r =p r2 ||| r.
       intros.
       eapply EqCong; done.
     Qed.

     Lemma EqCompNew_r {chan} :
       forall (t : Type) (r : ipdl) (k : chan t -> ipdl),
       r ||| x <- new t;; k x =p c <- new t;; r ||| k c.
        intros.
        rewrite EqCompComm.
        rewrite EqCompNew.
        apply EqCongNew => c.
        apply EqCompComm.
     Qed.

     Lemma Absorb {C} : forall p1 p2 : @ipdl C, ipdl_t [::] p1 -> p1 ||| p2 =p p2.
        intros.
        have h: p1 =p prot0 by apply EqZero.
        rewrite h.
        rewrite EqCompComm EqCongCompZero //=.
     Qed.

     Lemma eq_par0 {C} : forall r : @ipdl C, r =p r ||| prot0.
       intros; rewrite EqCongCompZero; done.
     Qed.

     Lemma eq_0par {C} : forall r : @ipdl C, r =p prot0 ||| r.
        intros; rewrite EqCompComm EqCongCompZero //=.
     Qed.

     Definition copy {chan} : forall {t : Type}, chan t -> @rxn chan t.
         intros.
         apply (x <-- Read X ;; Ret x).
     Defined.

     Class NewLike chan {A : Type} (f : (A -> @ipdl chan) -> ipdl) : Prop := Build_NewLike
       { newComp : forall (k : A -> ipdl) (r : ipdl),
                   f k ||| r =p f (fun c : A => k c ||| r);
         newCong : forall k1 k2 : A -> ipdl,
             (forall x : A, k1 x =p k2 x) -> f k1 =p f k2;
         new_new : forall {t} (k : A -> chan t -> ipdl),
             f (fun x => c <- new t ;; k x c) =p
             c <- new t ;; f (fun x => k x c)                                    
       }.

     #[global]
     Instance New_NewLike {C} t : NewLike C (New t).
       constructor.
       intros.
       apply EqCompNew.
       intros.
       apply EqCongNew; done.
       intros; apply EqNewExch.
     Qed.
       
     Lemma newComp_r {chan} :
       forall (A : Type) (f : (A -> ipdl) -> ipdl),
       NewLike chan f ->
       forall (k : A -> ipdl) (r : ipdl), r ||| f k =p f (fun c : A => r ||| k c).
         intros.
         rewrite EqCompComm.
         rewrite newComp.
         apply newCong.
         intros; apply EqCompComm.
     Qed.

     #[global]
     Instance newlike_mor chan A f `{NewLike chan A f} :
       Proper (pointwise_relation _ EqProt ==> EqProt) f.
        move => k1 k2 h.
        apply newCong.
        done.
     Qed.

     Lemma eq_EqRefl {chan} : forall r1 r2 : @ipdl chan, r1 = r2 -> r1 =p r2.
       intros; subst; reflexivity.
     Qed.

     Notation "xs ## i" := (tnth xs i) (at level 60) : ipdl_scope.


     (* Setoid instance *)
Canonical ipdl_setoid {C} : Setoid.setoid :=
  {| Setoid.car := @ipdl C; Setoid.eqv := EqProt |}.

     #[global]
Instance rset_setoid_monoidLaws {C} : @Setoid.monoidLaws (ipdl_setoid) prot0 (@Par C).
    constructor.
    apply _.
    simpl.
    rewrite /Setoid.eqv.
    rewrite //=.
    intros.
    rewrite EqCompAssoc; reflexivity.
    intros.
    symmetry.
    rewrite -eq_par0; reflexivity.
    intros.
    rewrite EqCompComm.
    rewrite -eq_par0; reflexivity.
Qed.

     #[global]
Instance ipdl_setoid_comMonoid {C} : @Setoid.comMonoidLaws (ipdl_setoid) prot0 (@Par C).
    constructor.
    apply _.
    intros; apply EqCompComm.
Qed.

Lemma EqSubsume_reads_from {chan} {t1 t2 t3} (c : chan t1) (d : chan t2) (e : chan t3)
      r1 r2 :
  reads_from d r1 ->
  reads_from e r2 ->
  (c ::= r1) ||| (d ::= r2) =p
                               (c ::= (_ <-- Read e ;; r1) ||| (d ::= r2)).
  intros.
  have h1 : r1 =r (_ <-- Read d ;; r1) by rewrite remove_read //=.
  have h2 : r2 =r (_ <-- Read e ;; r2) by rewrite remove_read //=.
  etransitivity.
  apply EqCongComp.
  apply EqCongReact.
  apply h2.
  etransitivity.
  rewrite EqCompComm.
  apply EqCongComp.
  apply EqCongReact.
  apply h1.
  rewrite EqSubsume.
  rewrite EqCompComm.
  rewrite -h2.
  apply EqCongComp_l.
  apply EqCongReact.
  apply EqBind_r; intro.
  rewrite -h1; done.
Qed.

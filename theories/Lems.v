(* Some extra random lemmas. *)


From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop fintype.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Base Ipdl.Exp Ipdl.Core Lib.Perm Lib.setoid_bigop Lib.OrdLems Lib.TupleLems Lib.Set Classical Big Pars.

Open Scope bool.



(* Simple permutations *)

Require Import ProofIrrelevance.

Inductive RPerm {C} : @ipdl C -> @ipdl C -> Prop :=
  | RPerm_refl r : RPerm r r
  | RPerm_sym r1 r2 : RPerm r1 r2 -> RPerm r2 r1
  | RPerm_trans r1 r2 r3 : RPerm r1 r2 -> RPerm r2 r3 -> RPerm r1 r3
  | RPerm_comp_sym r1 r2 : RPerm (Par r1 r2) (Par r2 r1)
  | RPerm_comp_assoc r1 r2 r3 : RPerm (r1 ||| (r2 ||| r3)) ((r1 ||| r2) ||| r3)
  | RPerm_cong r1 r2 r3 r4 : RPerm r1 r3 -> RPerm r2 r4 -> RPerm (r1 ||| r2) (r3 ||| r4)
  | RPerm_par0 r : RPerm r (Par r prot0).

Add Parametric Relation {C} : (@ipdl C) (RPerm)
                                       reflexivity proved by RPerm_refl
                                       symmetry proved by RPerm_sym
                                           transitivity proved by RPerm_trans as perm_rel.


Close Scope bool_scope.
Require Import Setoid Relation_Definitions.

Add Parametric Morphism {C} : (@Par C)
   with signature RPerm ==> RPerm ==> RPerm as par_perm_mor.
  intros.
  apply RPerm_cong; done.
Qed.

Open Scope bool_scope.

Notation "x =perm y" := (RPerm x y) (at level 60).

Require Import PropExtensionality.

Lemma orF p : p <-> (p \/ False).
  split.
  intro; left; done.
  elim; done.
Qed.

Lemma orT p : (p \/ True) <-> True.
  split.
  done.
  intuition.
Qed.

Lemma andF p : (p /\ False) <-> False.
  intuition.
Qed.

Lemma andT p : (p /\ True) <-> p.
  intuition.
Qed.
  
Lemma RPerm_EqProt {C} r1 r2 :
    RPerm r1 r2 -> @EqProt C r1 r2.
    elim; intros.
    reflexivity.
    symmetry; done.
    etransitivity.
    apply H0; done.
    done.
    rewrite EqCompComm //=.
    rewrite EqCompAssoc //=.
    rewrite H0 H2 //=.
    rewrite -eq_par0 //=.
  Qed.

Notation "x =perm y" := (RPerm x y) (at level 60).

Add Parametric Relation {C} : (@ipdl C) (RPerm)
                                       reflexivity proved by RPerm_refl
                                       symmetry proved by RPerm_sym
                                           transitivity proved by RPerm_trans as perm_rel_2.


Close Scope bool_scope.
Require Import Setoid Relation_Definitions.

Add Parametric Morphism {C} : (@Par C)
   with signature RPerm ==> RPerm ==> RPerm as par_perm_mor_2.
  intros.
  apply RPerm_cong; done.
Qed.

Open Scope bool_scope.


(* Typeclass for new-like *)


  
Lemma new_pars_pull {C} {A} (r : ipdl) (f : (A -> ipdl) -> ipdl) `{NewLike C _ f} (rs : A -> seq ipdl) :
  f (fun c => pars [:: r & rs c]) =p r ||| f (fun c => pars (rs c)).
  symmetry.
  rewrite newComp_r.
  apply newCong; intros.
  apply pars_cons.
Qed.



Lemma newPars {C} {A} (f : (A -> ipdl) -> ipdl) `{NewLike C _ f} k rs :
  pars [:: f k & rs] =p f (fun c => pars [:: k c & rs]).
  rewrite pars_cons.
  rewrite newComp.
  apply newCong; intros.
  rewrite pars_cons //=.
Qed.


(* Input/ output stuff *)


Lemma eqseq_map_val {T : eqType} (P : pred T) (sT : subType P) (xs ys : seq sT) :
  map val xs = map val ys -> xs = ys.
  intros.
  move: ys H; induction xs; intros.
  simpl in H.
  destruct ys.
  done.
  simpl in H.
  inversion H.
  destruct ys.
  inversion H.
  simpl in H.
  inversion H.
  have -> : a = s.
  apply/eqP; rewrite eqE //= H1 //=.
  erewrite IHxs.
  done.
  done.
Qed.

Lemma ord_enumS I :
  ord_enum I.+1 = ord0 :: map (fun j => lift ord0 j) (ord_enum I).
  apply eqseq_map_val.
  rewrite val_ord_enum.
  simpl.
  congr (_ :: _).
  rewrite -map_comp /comp.
  etransitivity; last first.
  instantiate (1 :=
                 [seq x.+1 | x <- map val (ord_enum I)]).
  rewrite -map_comp /comp.
  apply eq_map => x.
  done.
  rewrite val_ord_enum.
  have -> //= : 1 = 1 + 0 by done.
  rewrite iotaDl.
  apply eq_map.  done.
Qed.

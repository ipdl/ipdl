
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop fintype.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Base Ipdl.Exp Ipdl.Core Lib.Perm Lib.setoid_bigop Lib.OrdLems Lib.TupleLems Lib.Set Classical Big Pars.

Open Scope bool.



(* Simple permutations *)

Require Import ProofIrrelevance.

Inductive RPerm : rset -> rset -> Prop :=
  | RPerm_refl r : RPerm r r
  | RPerm_sym r1 r2 : RPerm r1 r2 -> RPerm r2 r1
  | RPerm_trans r1 r2 r3 : RPerm r1 r2 -> RPerm r2 r3 -> RPerm r1 r3
  | RPerm_comp_sym r1 r2 : RPerm (Par r1 r2) (Par r2 r1)
  | RPerm_comp_assoc r1 r2 r3 : RPerm (r1 ||| (r2 ||| r3)) ((r1 ||| r2) ||| r3)
  | RPerm_cong r1 r2 r3 r4 : RPerm r1 r3 -> RPerm r2 r4 -> RPerm (r1 ||| r2) (r3 ||| r4)
  | RPerm_par0 r : RPerm r (Par r prot0).

Add Parametric Relation : (rset) (RPerm)
                                       reflexivity proved by RPerm_refl
                                       symmetry proved by RPerm_sym
                                           transitivity proved by RPerm_trans as perm_rel.


Close Scope bool_scope.
Require Import Setoid Relation_Definitions Lib.Crush.

Add Parametric Morphism : (Par)
   with signature RPerm ==> RPerm ==> RPerm as par_perm_mor.
  intros.
  apply RPerm_cong; done.
Qed.

Open Scope bool_scope.

Notation "x =p y" := (RPerm x y) (at level 60).

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
  

Lemma noOutput_rperm r1 r2 :
  r1 =p r2 ->
  (forall x, ~ outputs r1 x <-> ~ outputs r2 x).
  elim; intros.
  done.
  rewrite H0 //=.
  rewrite H0 H2 //=.
  split; repeat set_tac.
  split; repeat set_tac.
  split; repeat set_tac.
  apply H0 in H5; auto.
  apply H2 in H3; auto.
  apply <- H0 in H5; auto.
  apply <- H2 in H3; auto.
  split; repeat set_tac.
Qed.

Require Import Lib.Crush Lib.Learn.
  
  

Lemma isInput_rperm r1 r2 :
  r1 =p r2 ->
  forall x, inputs r1 x <-> inputs r2 x.
  elim; intros.
  repeat set_tac.
  move: (H0 x).
  repeat set_tac.
  move: (H0 x) (H2 x).
  repeat set_tac.
  repeat set_tac.
  repeat set_tac; union_split.
  learn_with x.
  learn_with x.
  repeat set_tac; union_split.
  repeat set_tac.
Qed.

  Lemma RPerm_EqProt r1 r2 :
    RPerm r1 r2 -> EqProt r1 r2.
    elim; intros.
    reflexivity.
    symmetry; done.
    etransitivity.
    apply H0; done.
    done.
    rewrite ParSym //=.
    rewrite ParAssoc //=.
    rewrite H0 H2 //=.
    rewrite -eq_par0 //=.
  Qed.

Notation "x =p y" := (RPerm x y) (at level 60).

Add Parametric Relation : (rset) (RPerm)
                                       reflexivity proved by RPerm_refl
                                       symmetry proved by RPerm_sym
                                           transitivity proved by RPerm_trans as perm_rel_2.


Close Scope bool_scope.
Require Import Setoid Relation_Definitions.

Add Parametric Morphism : (Par)
   with signature RPerm ==> RPerm ==> RPerm as par_perm_mor_2.
  intros.
  apply RPerm_cong; done.
Qed.

Open Scope bool_scope.


(* Typeclass for new-like *)


  
Lemma new_pars_pull {A} (r : rset) (f : (A -> rset) -> rset) `{NewLike _ f} (rs : A -> seq rset) :
  f (fun c => pars [:: r & rs c]) =0 r ||| f (fun c => pars (rs c)).
  symmetry.
  rewrite newComp_r.
  apply newCong; intros.
  apply pars_cons.
Qed.



Lemma newPars {A} (f : (A -> rset) -> rset) `{NewLike _ f} k rs :
  pars [:: f k & rs] =0 f (fun c => pars [:: k c & rs]).
  rewrite pars_cons.
  rewrite newComp.
  apply newCong; intros.
  rewrite pars_cons //=.
Qed.

Print chans.

Lemma notin_newP {t} (r : chan t -> rset) j :
  ~ In (x <- new t ;; r x) j ->
  exists c, mkChan c <> j /\ ~ In (r c) j.
  intros.
  unfold In in *.
  simpl in *.
  apply not_all_ex_not in H.
  destruct H.
  apply imply_to_and in H.
  exists x; done.
Qed.

Lemma notin_outputs_newP {t} (r : chan t -> rset) j :
  ~ outputs (x <- new t ;; r x) j ->
  exists c, mkChan c <> j /\ ~ outputs (r c) j.
  intros.
  unfold In in *.
  simpl in *.
  apply not_all_ex_not in H.
  destruct H.
  apply imply_to_and in H.
  exists x; done.
Qed.

Lemma notin_new_irrel {t} (r : chan t -> rset) j :
  ~ In (x <- new t ;; r x) j ->
  exists v, ~ In (r v) j.
  move/notin_newP.
  set_tac.
  exists x; done.
Qed.

Lemma notin_outputs_new_irrel {t} (r : chan t -> rset) j :
  ~ outputs (x <- new t ;; r x) j ->
  exists v, ~ outputs (r v) j.
  move/notin_outputs_newP.
  set_tac.
  exists x; done.
Qed.

Lemma In_newvec {I} {t} (r : I.-tuple (chan t) -> rset) j :
  (forall v, (forall i, j <> mkChan (tnth v i)) -> In (r v) j) <->
  In (x <- newvec I @ t ;; r x) j.
  split.
  induction I.
  simpl.
  intros.
  apply (H [tuple]).
  case; done.
  simpl; intros.
  unfold In; intros.
  apply IHI; simpl; intros.
  apply H; intros.
  destruct (ordP i); subst.
  rewrite tnth0.
  crush.
  rewrite tnthS.
  crush.

  induction I; crush.
  have -> //= : v = [tuple] by apply tuple0.
  destruct (tupleP v).
  apply (IHI (fun v => r [tuple of x :: v])).
  apply H.
  intros.
  apply (H0 ord0).
  rewrite tnth0; congruence.
  intros.
  apply (H0 (lift ord0 i)).
  rewrite tnthS; done.
Qed.

Lemma outputs_newvec {I} {t} (r : I.-tuple (chan t) -> rset) j :
  (forall v, (forall i, j <> mkChan (tnth v i)) -> outputs (r v) j) <->
  outputs (x <- newvec I @ t ;; r x) j.
  split.
  induction I.
  simpl.
  intros.
  apply (H [tuple]).
  case; done.
  simpl; intros.
  unfold In; intros.
  apply IHI; simpl; intros.
  apply H; intros.
  destruct (ordP i); subst.
  rewrite tnth0.
  crush.
  rewrite tnthS.
  crush.

  induction I; crush.
  have -> //= : v = [tuple] by apply tuple0.
  destruct (tupleP v).
  apply (IHI (fun v => r [tuple of x :: v])).
  apply H.
  intros.
  apply (H0 ord0).
  rewrite tnth0; congruence.
  intros.
  apply (H0 (lift ord0 i)).
  rewrite tnthS; done.
Qed.

Lemma notin_newvec {I} {t} (r : I.-tuple (chan t) -> rset) j :
  ~ In (x <- newvec I @ t ;; r x) j ->
  exists v, (forall i, j <> mkChan (tnth v i)) /\ ~ In (r v) j.
  intros.
  rewrite <- In_newvec in H.
  set_tac.
  eexists; split.
  apply x0.
  done.
Qed.

Lemma notin_outputs_newvec {I} {t} (r : I.-tuple (chan t) -> rset) j :
  ~ outputs (x <- newvec I @ t ;; r x) j ->
  exists v, (forall i, j <> mkChan (tnth v i)) /\ ~ outputs (r v) j.
  intros.
  rewrite <- outputs_newvec in H.
  set_tac.
  eexists; split.
  apply x0.
  done.
Qed.

Lemma notin_newvec_irrel {I} {t} (r : I.-tuple (chan t) -> rset) j :
  ~ In (x <- newvec I @ t ;; r x) j ->
  exists v, ~ In (r v) j.
  intros.
  rewrite <- In_newvec in H.
  set_tac.
  eexists; apply H.
Qed.

Lemma notin_outputs_irrel {I} {t} (r : I.-tuple (chan t) -> rset) j :
  ~ outputs (x <- newvec I @ t ;; r x) j ->
  exists v, ~ outputs (r v) j.
  intros.
  rewrite <- outputs_newvec in H.
  set_tac.
  eexists; apply H.
Qed.



Lemma not_output_mono_vec {I} {t} (f : I.-tuple (chan t) -> rset) v j :
  ~ outputs (f v) j -> ~ outputs (x <- newvec I @ t ;; f x) j.
  intros; induction I.
  rewrite //=.
  have: v = [tuple] by apply tuple0.
  intro; subst; done.
  rewrite newvecS.
  destruct (tupleP v).
  eapply not_output_mono.
  eapply IHI.
  instantiate (1 := t0).
  instantiate (1 := x).
  done.
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
  apply eq_map.
  done.
Qed.


Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Typing Lib.Set CFold.  
Require Import CoinFlip.
Require Import Lib.Procrastination.

Lemma CFIdealParty_t {n} (honest : pred 'I_n) leakB ok out i send :
  Uniq [:: mkChan (tnth leakB i); mkChan ok; mkChan send; mkChan (tnth out i)] -> 
  (CFIdealParty n honest leakB ok out i send) :::
                                            (if honest i then
                                               [:: mkChan send; mkChan ok]
                                             else
                                               [:: mkChan send])
                                            -->
                                            (if honest i then
                                               [:: mkChan (tnth out i)]
                                             else
                                               [:: mkChan (tnth leakB i)]).
  intros.
  case h : (honest i).
  repeat type_tac.
  rewrite h; repeat type_tac.
  rewrite h; repeat type_tac.
  repeat type_tac.
  repeat type_tac.
  repeat type_tac.
  repeat type_tac.
  repeat type_tac.
  rewrite h; repeat type_tac.
  rewrite h; repeat type_tac.
  repeat type_tac.
  repeat type_tac.
  repeat type_tac.
  repeat type_tac.
Qed.

Lemma In_mem {A : eqType} (X : seq A) x :
  x \in X ->
  In X x .
  induction X; rewrite //=.
  firstorder.
  rewrite in_cons in H; move/orP: H; elim; intros.
  right.
  rewrite (eqP H); done.
  left; apply IHX; done.
Qed.
  

Lemma CFIdeal_t {n} (honest : pred 'I_n) outs ok leakB :
  (exists j, honest j) ->
  (forall i j, i <> j -> tnth outs i <> tnth outs j) ->
  (forall i j, i <> j -> tnth leakB i <> tnth leakB j) ->
  (forall i j, tnth outs i <> tnth leakB j) -> 
  CFIdeal _ honest leakB ok outs :::
          [:: mkChan ok] --> union (CondUnion (fun x => singleton (mkChan (tnth outs x))) honest) (CondUnion (fun x => singleton (mkChan (tnth leakB x))) ( fun x => ~~ honest x)).
  intro Hhonest.
  intros.
  apply (new_t (
             (map (fun x => (tnth outs x)) (enum 'I_n))
                            ++ (map (fun x => (tnth leakB x)) (enum 'I_n)))); intros.
  have h1: (forall j, c <> tnth outs j).
    intros.
    intro; subst.
    destruct H2; apply in_cat_iff; left.
    eapply in_map_iff; exists j; split.
    apply In_mem; rewrite mem_enum //=.
    done.
  have h2: (forall j, c <> tnth leakB j).
    intros.
    intro; subst.
    destruct H2; apply in_cat_iff; right.
    eapply in_map_iff; exists j; split.
    apply In_mem; rewrite mem_enum //=.
    done.
 


  eapply par_t.
  repeat type_tac.
  eapply par_t.
  eapply Bigpar_t.
  intros; apply CFIdealParty_t.
  repeat type_tac.
  apply mkChan_eq_t; apply H1.
  repeat type_tac.

  destruct (honest i); destruct (honest j); repeat set_tac; apply mkChan_eq_t.
  apply H; congruence.
  specialize (H1 i j); congruence.
  apply H1.
  apply H0; congruence.

  destruct (honest i); destruct (honest j); repeat set_tac; apply mkChan_eq_t.
  apply H; done.
  apply H1.
  specialize (H1 j i); congruence.
  apply H0; done.

  apply drop_t; done.
  repeat type_tac.
  done.
  done.
  repeat type_tac.

  elim => j; destruct (honest j).
  repeat type_tac.
  specialize (h1 j); done.
  repeat type_tac.
  specialize (h2 j); done.


  destruct (honest x1); repeat type_tac.
  repeat type_tac.
  exists x; rewrite H3; repeat type_tac.
  elim => j; destruct (honest j); repeat type_tac.
  elim => j; destruct (honest j); repeat type_tac.
  elim => j; destruct (honest j); repeat type_tac.
  destruct (honest x0); repeat type_tac.

  repeat type_tac.
  repeat type_tac.
  right; left.
  exists x0.
  rewrite H4; repeat type_tac.
  repeat type_tac.
  right; left.
  exists x0; rewrite (negbTE H4); repeat type_tac.

  case h : (honest x0); rewrite h in H4; repeat type_tac.
  left; left; exists x0; split; done.
  left; right; exists x0; split.
  rewrite h //=.
  done.
Qed.

Lemma cfold_t {n} {t t' : type} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t') (init : t -> t') (ys : (n.+1).-tuple (chan t')) :
  tup_disj xs ys ->
  tup_ok xs ->
  tup_ok ys ->
  (cfold xs f init ys) ::: (Union (fun x => singleton (mkChan (tnth xs x)))) -->
                           (Union (fun x => singleton (mkChan (tnth ys x)))).
  intros.
  have -> :
    Union (fun x : 'I_n.+1 => singleton (mkChan (tnth xs x))) =
    Union (fun x : 'I_n.+1 => CondUnion (fun y => singleton (mkChan (tnth xs y))) (fun y => y < x)).
    by admit.
  eapply Bigpar_t_simple.
  admit.
  intros; repeat set_tac.
  apply mkChan_eq_t.
  apply H1; congruence.
  apply mkChan_eq_t.
  apply H1; congruence.
  intros; repeat type_tac.
  elim.
  intro; case; intros.
  inversion b; subst.
  move: (H x j).
  done.
Admitted.

(* Real *)

Lemma big_FComm_t {n} (commit : n.-tuple (chan TBool)) (committed : n.-tuple (chan TUnit)) (open : n.-tuple (chan TUnit)) (opened : n.-tuple (chan TBool)) :
  (forall i j, tnth committed i <> tnth open j) ->
  (forall i j, tnth commit i <> tnth opened j) ->
  (forall i j, i <> j -> tnth commit i <> tnth commit j) ->
  (forall i j, i <> j -> tnth committed i <> tnth committed j) ->
  (forall i j, i <> j -> tnth open i <> tnth open j) ->
  (forall i j, i <> j -> tnth opened i <> tnth opened j) ->
  (\||_(i < n) FComm (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i)) ::: Union (fun x => [:: mkChan (tnth commit x); mkChan (tnth open x)]) -->
                                                                                           Union (fun x =>  [:: mkChan (tnth committed x); mkChan (tnth opened x)]). 
  intros.
  apply Bigpar_t_simple.
  intros; repeat type_tac.
  intros; repeat type_tac; apply mkChan_eq_t; firstorder.
  intros; repeat type_tac; apply mkChan_eq_t; firstorder.
  intros; repeat type_tac; apply mkChan_eq_t; firstorder.
  intros; repeat type_tac; apply mkChan_eq_t; firstorder.
Qed.

Lemma CFRealParty_honest_t {n} (committed : (n.+1).-tuple (chan TUnit)) opened commit open out :
  tup_ok committed ->
  tup_ok opened ->
  out <> commit ->
  (CFRealParty_honest _ committed opened commit open out) :::
                                                        Union (fun x => [:: mkChan (tnth committed x); mkChan (tnth opened x)]) --> [:: mkChan commit; mkChan open; mkChan out].
  intros.
  eapply newvec_t; intros.
  eapply newvec_t; intros.
  eapply par_t.
  repeat type_tac.
  eapply par_t.
  apply cfold_t.
  admit. (* tup_disj committed t *)
  done.
  done.
  eapply par_t.
  repeat type_tac.
  eapply par_t.
  apply cfold_t.
  admit. (* tup_disj opened t0 *)
  done.
  done.
  repeat type_tac.
  repeat type_tac.
  (* out <> tnth t0 x0 *)
  admit.
  (* same *)
  admit.
  done.
  done.
  repeat type_tac.
  elim.
  intros.
  inversion H6.
  done.
  done.
  repeat type_tac.
  (* t <> open *)
  admit.
  elim; intros.
  inversion H6.
  elim; intros; inversion H6.
  (* t <> open *)
  admit.
  elim ;intros; repeat type_tac.
  elim ;intros; repeat type_tac.
  done.
  done.
  repeat type_tac.
  elim ;intros; repeat type_tac.
  (* t0 <> commit *)
  admit.
  admit.

  repeat type_tac.
  right; split.
  right; split.
  right; split.
  left.
  eexists; done.
  repeat type_tac.
  (* t0 <> opened *)
  admit.
  (* out <> opened *)
  admit.
  repeat type_tac.
  intro; repeat type_tac.


Admitted.


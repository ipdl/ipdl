
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Big Pars Lib.Set.
Require Import CoinFlip CFold CFSimComp CFReal.

Lemma pars_replace r2 r1 rs :
  pars [:: r1 & rs] =0 pars [:: r2 & rs] ->
  pars [:: r1 & rs] =0 pars [:: r2 & rs].
  done.
Qed.

Lemma new_pars_replace_elim t r1 r2 rs rs' :
  (forall c, pars [:: Out c r1 & rs c] =0 pars [:: Out c r1 & rs']) ->
  (forall c, pars [:: Out c r2 & rs c] =0 pars [:: Out c r2 & rs']) ->
  (forall x, In (rxn_inputs r1) x -> In (pars rs') x) ->
  (forall x, In (rxn_inputs r2) x -> In (pars rs') x) ->
  (x <- new t ;; pars [:: Out x r1 & rs x]) =0 (x <- new t ;; pars [:: Out x r2 & rs x]).
  intros.
  etransitivity.
  apply EqNew => c _ _.
  rewrite H.
  apply EqRefl.
  symmetry.
  etransitivity.
  apply EqNew => c _ _.
  rewrite H0.
  apply EqRefl.
  rewrite new_pars_remove; rewrite //=.
  rewrite new_pars_remove; rewrite //=.
Qed.

Print SimComp_simpl7.

Lemma CFRealIdealE (k : nat) {n}
           (honest : pred 'I_(n.+2))
           (out advCommit : (n.+2).-tuple (chan k)) 
           (advOpen : (n.+2).-tuple (chan TUnit))
           (advCommitted : (n.+2).-tuple ((n.+2).-tuple (chan TUnit)))
           (advOpened : (n.+2).-tuple ((n.+2).-tuple (chan k))) :
  ~~ honest ord0 ->
  honest ord_max ->
  CFRealSimpl k honest out advCommit advOpen advCommitted advOpened =0
  SimComp_simpl7 k honest advCommit advOpen advCommitted advOpened out.
  intros.
  rewrite /CFRealSimpl.
  rewrite /SimComp_simpl7.

  setoid_rewrite (@newvec_newvec _ _ TUnit TUnit) at 1.
  rewrite newvec_newvec.
  apply EqNew_vec => open _ _.
  rewrite newvec_newvec.
  apply EqNew_vec => committed _ _.
  rewrite newvec_newvec.
  apply EqNew_vec => opened _ _.
  rotate_news.
  apply EqNew_vec => sum_commits _ _.
  apply EqNew_vec => sum_open _ _.
  apply EqNew_vec => commit _ _.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  apply EqProt_big_r; intros; apply EqOut; r_swap 0 1; done.
  swap_tac 0 3.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 3.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  rewrite bigpar_mkcond.
  swap_tac 0 1.
  rewrite bigpar_mkcond.
  rewrite -par_in_pars.
  rewrite -bigpar_par.
  apply pars_cons_cong; rewrite //=.
  apply EqProt_big_r; intros.
  rewrite /Sim_CFParty.
  destruct (honest x); simpl.
  rewrite -eq_0par.
  apply EqNew_vec => v1 _ _.
  apply EqNew_vec => v2 _ _.
  align.
  rewrite -eq_par0.
  done.
Qed.

Search Sim.

Lemma CoinFlip_main (k : nat) {n}
           (honest : pred 'I_(n.+2))
           (out advCommit : (n.+2).-tuple (chan k)) 
           (advOpen : (n.+2).-tuple (chan TUnit))
           (advCommitted : (n.+2).-tuple ((n.+2).-tuple (chan TUnit)))
           (advOpened : (n.+2).-tuple ((n.+2).-tuple (chan k))) :
  ~~ honest ord0 ->
  honest ord_max ->
  CFReal k _ honest out advCommit advOpen advCommitted advOpened =0
    leak <- new k ;; 
    ok <- new TUnit ;; 
    pars [::
            Sim k honest leak ok advCommit advOpen advCommitted advOpened;
            CFIdeal k _ honest leak ok out
                 ].
  intros.
  rewrite CFRealSimplE.
  symmetry.
  etransitivity.
  instantiate (1 := SimComp k honest advCommit advOpen advCommitted advOpened out).
  done.

  rewrite SimComp_E1.
  rewrite SimComp_simpl2E //=.
  rewrite SimComp_simpl3E //=.
  rewrite SimComp_simpl4E //=.
  rewrite SimComp_simpl5E //=.
  rewrite SimComp_simpl6E //=.
  rewrite SimComp_simpl7E //=.
  rewrite CFRealIdealE //=.
Qed.

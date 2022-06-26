
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Big Pars Lib.Set.
Require Import CoinFlip CFold CFSimComp CFReal.

Lemma pars_replace {chan : Type -> Type} (r2 : @ipdl chan) r1 rs :
  pars [:: r1 & rs] =p pars [:: r2 & rs] ->
  pars [:: r1 & rs] =p pars [:: r2 & rs].
  done.
Qed.

Lemma new_pars_replace_elim {chan : Type -> Type} t r1 r2 rs rs' :
  (forall c, @pars chan [:: Out c r1 & rs c] =p pars [:: Out c r1 & rs']) ->
  (forall c, pars [:: Out c r2 & rs c] =p pars [:: Out c r2 & rs']) ->
  (x <- new t ;; pars [:: Out x r1 & rs x]) =p (x <- new t ;; pars [:: Out x r2 & rs x]).
  intros.
  etransitivity.
  apply EqCongNew => c_.
  rewrite H.
  apply EqRefl.
  symmetry.
  etransitivity.
  apply EqCongNew => c.
  rewrite H0.
  apply EqRefl.
  rewrite new_pars_remove; rewrite //=.
  rewrite new_pars_remove; rewrite //=.
Qed.
Open Scope bool_scope.

Lemma CFRealIdealE {chan : Type -> Type} (k : nat) {n}
           (honest : pred 'I_(n.+2))
           (out advCommit : (n.+2).-tuple (chan k.-bv)) 
           (advOpen : (n.+2).-tuple (chan unit))
           (advCommitted : (n.+2).-tuple ((n.+2).-tuple (chan unit)))
           (advOpened : (n.+2).-tuple ((n.+2).-tuple (chan k.-bv))) :
  ~~ honest ord0 ->
  honest ord_max ->
  CFRealSimpl k honest out advCommit advOpen advCommitted advOpened =p
  SimComp_simpl7 k honest advCommit advOpen advCommitted advOpened out.
  intros.
  rewrite /CFRealSimpl.
  rewrite /SimComp_simpl7.

  setoid_rewrite (@newvec_newvec _ _ _ unit unit) at 1.
  rewrite newvec_newvec.
  apply EqCongNew_vec => open .
  rewrite newvec_newvec.
  apply EqCongNew_vec => committed .
  rewrite newvec_newvec.
  apply EqCongNew_vec => opened .
  rotate_news.
  apply EqCongNew_vec => sum_commits .
  apply EqCongNew_vec => sum_open .
  apply EqCongNew_vec => commit .
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  apply EqProt_big_r; intros; apply EqCongReact; r_swap 0 1; done.
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
  apply EqCongNew_vec => v1 .
  apply EqCongNew_vec => v2 .
  align.
  rewrite -eq_par0.
  done.
Qed.

Lemma CoinFlip_main {chan : Type -> Type} (k : nat) {n}
           (honest : pred 'I_(n.+2))
           (out advCommit : (n.+2).-tuple (chan k.-bv)) 
           (advOpen : (n.+2).-tuple (chan unit))
           (advCommitted : (n.+2).-tuple ((n.+2).-tuple (chan unit)))
           (advOpened : (n.+2).-tuple ((n.+2).-tuple (chan k.-bv))) :
  ~~ honest ord0 ->
  honest ord_max ->
  CFReal k _ honest out advCommit advOpen advCommitted advOpened =p
    leak <- new k.-bv ;; 
    ok <- new unit ;; 
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

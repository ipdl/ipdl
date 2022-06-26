Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Lib.OrdLems.  
Require Import CoinFlip CFold.

Lemma eq_EqRxn {chan} {t} (r1 r2 : rxn t) :
  r1 = r2 ->
  @EqRxn chan _ r1 r2.
  move => -> //=.
Qed.

Definition CFRealParty_honest_external {chan : Type -> Type} (k : nat) {n} (committed : (n.+1).-tuple (chan unit)) (opened : (n.+1).-tuple (chan k.-bv)) (commit : chan k.-bv) (open : chan unit)  :=
  committed_sum <- newvec n.+1 @ unit ;;
  opened_sum' <- newvec n.+1 @ k.-bv ;;
  pars [::
          commit ::= (Samp (Unif ));
          read_all committed committed_sum;
          Out open (copy (tnth committed_sum ord_max));
          @cfold chan _ k.-bv k.-bv opened xort id opened_sum'
       ].
          
Lemma CFRealParty_honest_externalE {chan : Type -> Type} (k : nat) {n} (committed : (n.+1).-tuple (chan unit)) (opened : (n.+1).-tuple (chan k.-bv)) (commit : chan k.-bv) (open : chan unit) (out : chan k.-bv) (opened_sum : (n.+1).-tuple (chan k.-bv)) :
  pars [::
          CFRealParty_honest k _ committed opened commit open out;
          @cfold chan _ k.-bv k.-bv opened xort id opened_sum ] =p 
  pars [::
          CFRealParty_honest_external k committed opened commit open ;
          Out out (copy (tnth opened_sum ord_max)); 
       @cfold chan _ k.-bv k.-bv opened xort id opened_sum ].
  rewrite newPars.
  rewrite newPars.
  setoid_rewrite newPars.
  apply EqCongNew_vec => committed_sum.
  apply EqCongNew_vec => opened_sum'.
  rewrite pars_pars; simpl.
  
  rewrite pars_pars; simpl.
  swap_tac 0 5.
  swap_tac 1 3.
  rewrite (pars_split 2) //=.
  rewrite cfold2_det_copy.
  rewrite -pars_cat //=.
  swap_tac 0 4.
  rewrite pars_inline_from_big //=.
  swap_tac 0 4.
  rewrite (pars_split 2) //=.
  rewrite -cfold2_det_copy.
  rewrite -pars_cat //=.
  align.
  rewrite /copy; apply EqCongReact; simp_rxn; done.
  apply _.
  apply _.
Qed.

Lemma CFRealPartyE {chan : Type -> Type} (k : nat) {n} (honest : pred 'I_(n.+1)) advCommit advOpen advCommitted advOpened i committed opened commit open out opened_sum :
  pars [::
          CFParty k _ honest advCommit advOpen advCommitted advOpened i committed opened commit open out;
          @cfold chan _ k.-bv k.-bv opened xort id opened_sum ] =p 
  pars [::
          if honest i then pars [::
                                   CFRealParty_honest_external k committed opened commit open; Out out (copy (tnth opened_sum ord_max))] else CFRealParty_corr k _ advCommit advOpen advCommitted advOpened i committed opened commit open;
       @cfold chan _ k.-bv k.-bv opened xort id opened_sum ].
  rewrite /CFParty.
  destruct (honest i).
  rewrite pars_pars.
  apply CFRealParty_honest_externalE.
  done.
Qed.

Lemma CFRealParty_compE {chan : Type -> Type} (k : nat) {n} (honest : pred 'I_(n.+1)) advCommit advOpen advCommitted advOpened committed opened commit open out opened_sum :
  pars [::
         \||_(i < n.+1) CFParty k _ honest advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i) (tnth out i) ; 
          @cfold chan _ k.-bv k.-bv opened xort id opened_sum ] =p 
  pars [::
          \||_(i < n.+1 | honest i) CFRealParty_honest_external k committed opened (tnth commit i) (tnth open i);
          \||_(i < n.+1 | honest i) Out (tnth out i) (copy (tnth opened_sum ord_max));
       \||_(i < n.+1 | ~~ honest i) CFRealParty_corr k _ advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i);
          @cfold chan _ k.-bv k.-bv opened xort id opened_sum ]. 
  etransitivity.
  apply pars_big_replace.
  intros.
  apply CFRealPartyE.
  simpl.
  symmetry.
  rewrite bigpar_mkcond.
  swap_tac 0 1.
  rewrite bigpar_mkcond.
  swap_tac 0 2.
  rewrite bigpar_mkcond.
  simpl.
  rewrite -par_in_pars.
  rewrite -bigpar_par.
  rewrite -par_in_pars.
  rewrite -bigpar_par.
  apply pars_big_replace; intros.
  rewrite !par_in_pars.
  destruct (honest i); simpl.
  rewrite pars_prot0.
  rewrite pars_pars //=.
  swap_tac 0 1; rewrite pars_prot0.
  swap_tac 0 1; rewrite pars_prot0.
  done.
Qed.
          
Lemma opened_sumE {chan : Type -> Type} (k : nat) {n} (commits : (n.+1).-tuple (chan k.-bv)) (opens : (n.+1).-tuple (chan unit)) (committed : (n.+1).-tuple (chan unit)) (opened : (n.+1).-tuple (chan k.-bv)) (opened_sum : (n.+1).-tuple (chan k.-bv))
      (opens_sum : (n.+1).-tuple (chan unit))
      (commits_sum : (n.+1).-tuple (chan k.-bv))
  :
  pars [::
          @cfold _ _ k.-bv k.-bv commits xort id commits_sum;
          read_all opens opens_sum;
          @cfold _ _ k.-bv k.-bv opened xort id opened_sum;
          \||_(i < n.+1) FComm k (tnth commits i)  (tnth committed i) (tnth opens i) (tnth opened i)]  =p

  pars [::
          @cfold _ _ k.-bv k.-bv commits xort id commits_sum;
          read_all opens opens_sum;
       \||_(i < n.+1) Out (tnth opened_sum i) (
                                            _ <-- Read (tnth opens_sum i) ;;
                                            x <-- Read (tnth commits_sum i) ;;
                                            Ret x);
          \||_(i < n.+1)
          FComm k (tnth commits i) (tnth committed i) (tnth opens i)  (tnth opened i)]. 
  swap_tac 0 3.
  rewrite big_pars2 pars_pars //=.
  swap_tac 0 3.
  symmetry.
  swap_tac 0 3.
  rewrite pars_pars //=.
  swap_tac 0 3.

  apply pars_big_hybrid2.
  intros.
  symmetry.
  rewrite /cfold_body.
  destruct (ordP k0); subst.
  swap_tac 0 1.
  swap_tac 1 2.
  rewrite pars_inline_from_big //=.
  simp_at 0.
  symmetry.
  swap_tac 0 1.
  swap_tac 1 3.
  rewrite pars_inline_from_big //=.
  rewrite {1}/cfold_body //=.
  simp_at 0.
  swap_at 0 0 1.
  swap_tac 1 5.
  rewrite pars_inline_from_big //=.
  rewrite {1}/cfold_body //=.
  apply pars_cons_cong.
  apply EqCongReact.
  simp_rxn.
  rewrite /copy.
  r_swap 0 1; done.

  swap_tac 0 1.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 1.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  
  swap_tac 0 1.
  swap_tac 1 2.
  rewrite pars_inline_from_big; rewrite //=.
  simp_at 0.
  swap_at 0 0 2.
  swap_tac 1 2.
  rewrite pars_inline_from_big; rewrite //=.
  simp_at 0.
  symmetry.
  swap_tac 0 1.

  swap_tac 1 3.
  rewrite pars_inline_from_big; rewrite //=.

  rewrite {1}/cfold_body //=.
  simp_at 0.
  swap_at 0 0 2.
  swap_tac 1 5.
  rewrite pars_inline_from_big; rewrite //=.
  apply pars_cons_cong.
  rewrite /cfold_body //=.
  apply EqCongReact.
  simp_rxn.
  r_swap 0 3.
  apply EqRxnBind.
  apply eq_EqRxn.
  congr (_ _).
  congr (_ _ _).
  apply/eqP; rewrite eqE //=.
  intros.
  
  r_swap 0 1.
  apply EqRxnBind.
  apply eq_EqRxn.
  congr (_ _).
  congr (_ _ _).
  apply/eqP; rewrite eqE //=.
  intros.

  r_swap 0 1.
  apply EqBind_r; intro.
  rewrite /copy.
  symmetry; simp_rxn.
  apply EqBind_r; intro.
  done.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
Qed.

Definition CFRealSimpl {chan : Type -> Type} (k : nat) {n}
           (honest : pred 'I_(n.+1))
           (out advCommit : (n.+1).-tuple (chan k.-bv)) 
           (advOpen : (n.+1).-tuple (chan unit))
           (advCommitted : (n.+1).-tuple ((n.+1).-tuple (chan unit)))
           (advOpened : (n.+1).-tuple ((n.+1).-tuple (chan k.-bv))) :=
  commit <- newvec n.+1 @ k.-bv ;;
  committed <- newvec n.+1 @ unit ;;
  open <- newvec n.+1 @ unit ;;
  opened <- newvec n.+1 @ k.-bv ;;
  commits_sum <- newvec n.+1 @ k.-bv ;;
  opens_sum <- newvec n.+1 @ unit ;;
  pars [::
          \||_(i < n.+1) FComm k (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);
          \||_(i < n.+1 | honest i) CFRealParty_honest_external k committed opened (tnth commit i) (tnth open i);
       \||_(i < n.+1 | honest i) Out (tnth out i)
          (
            _ <-- Read (tnth opens_sum ord_max) ;;
            x <-- Read (tnth commits_sum ord_max) ;;
            Ret x);
       \||_(i < n.+1 | ~~ honest i) CFRealParty_corr k _ advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i);
          @cfold _ _ k.-bv k.-bv commit xort id commits_sum;
          read_all open opens_sum
]. 


Lemma CFRealSimplE {chan : Type -> Type} (k : nat) {n}
           (honest : pred 'I_(n.+1))
           (out advCommit : (n.+1).-tuple (chan k.-bv)) 
           (advOpen : (n.+1).-tuple (chan unit))
           (advCommitted : (n.+1).-tuple ((n.+1).-tuple (chan unit)))
           (advOpened : (n.+1).-tuple ((n.+1).-tuple (chan k.-bv))) :
  CFReal k _ honest out advCommit advOpen advCommitted advOpened =p
  CFRealSimpl k honest out advCommit advOpen advCommitted advOpened.
  rewrite /CFReal.
  etransitivity.
  apply EqCongNew_vec => commit .
  apply EqCongNew_vec => committed .
  apply EqCongNew_vec => open .
  apply EqCongNew_vec => opened .
  rewrite -(@new_cfold_remove chan _ k.-bv k.-bv commit xort id).
  apply EqCongNew_vec => commits_sum .
  rewrite -(@new_cfold_remove chan _ unit unit open (fun _ _ => tt) (fun _ => tt)).
  apply EqCongNew_vec => opens_sum .
  rewrite -(@new_cfold_remove chan _ k.-bv k.-bv opened xort id).
  apply EqCongNew_vec => opened_sum.
  swap_tac 0 4.
  swap_tac 1 4.
  rewrite (pars_split 2); simpl.
  rewrite CFRealParty_compE.
  rewrite -pars_cat //=.
  swap_tac 0 4.
  swap_tac 1 6.
  swap_tac 2 3.
  swap_tac 3 5.
  rewrite (pars_split 4); simpl.
  rewrite opened_sumE.
  rewrite -pars_cat; simpl.
  swap_tac 0 6.
  swap_tac 1 2.
  etransitivity.
  apply pars_big_replace; intros.
  rewrite pars_inline_from_big.
  edit_tac 0.
  simp_rxn.
  done.
  apply EqRefl.
  done.
  done.
  apply EqRefl.

  rewrite /CFRealSimpl.

  apply EqCongNew_vec => commit .
  apply EqCongNew_vec => committed .
  apply EqCongNew_vec => open .
  apply EqCongNew_vec => opened .

  apply EqCongNew_vec => commits_sum .
  apply EqCongNew_vec => opens_sum .

  etransitivity.
  etransitivity.
  apply EqCongNew_vec => x; swap_tac 0 1.
  apply EqRefl.
  rewrite pars_big_remove.
  apply EqRefl.

  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 1.
  apply pars_cons_cong; rewrite //=.
  align.
Qed.

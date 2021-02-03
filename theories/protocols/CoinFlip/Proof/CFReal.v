Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Typing Lib.Set Lib.OrdLems.  
Require Import CoinFlip CFold.

Lemma eq_EqRxn {t} (r1 r2 : rxn t) :
  r1 = r2 ->
  EqRxn _ r1 r2.
  move => -> //=.
Qed.

Definition CFRealParty_honest_external (k : nat) {n} (committed : (n.+1).-tuple (chan TUnit)) (opened : (n.+1).-tuple (chan k)) (commit : chan k) (open : chan TUnit)  :=
  committed_sum <- newvec n.+1 @ TUnit ;;
  opened_sum' <- newvec n.+1 @ k ;;
  pars [::
          Out commit (Unif k);
          read_all committed committed_sum;
          Out open (copy (tnth committed_sum ord_max));
          @cfold _ k k opened xort id opened_sum'
       ].
          
Lemma CFRealParty_honest_externalE (k : nat) {n} (committed : (n.+1).-tuple (chan TUnit)) (opened : (n.+1).-tuple (chan k)) (commit : chan k) (open : chan TUnit) (out : chan k) (opened_sum : (n.+1).-tuple (chan k)) :
  pars [::
          CFRealParty_honest k _ committed opened commit open out;
          @cfold _ k k opened xort id opened_sum ] =0 
  pars [::
          CFRealParty_honest_external k committed opened commit open ;
          Out out (copy (tnth opened_sum ord_max)); 
       @cfold _ k k opened xort id opened_sum ].
  rewrite newPars.
  rewrite newPars.
  setoid_rewrite newPars.
  apply EqNew_vec => committed_sum _ _.
  apply EqNew_vec => opened_sum' _ _.
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
  rewrite /copy; apply EqOut; simp_rxn; done.
  apply _.
  apply _.
Qed.

Lemma CFRealPartyE (k : nat) {n} (honest : pred 'I_(n.+1)) advCommit advOpen advCommitted advOpened i committed opened commit open out opened_sum :
  pars [::
          CFParty k _ honest advCommit advOpen advCommitted advOpened i committed opened commit open out;
          @cfold _ k k opened xort id opened_sum ] =0 
  pars [::
          if honest i then pars [::
                                   CFRealParty_honest_external k committed opened commit open; Out out (copy (tnth opened_sum ord_max))] else CFRealParty_corr k _ advCommit advOpen advCommitted advOpened i committed opened commit open;
       @cfold _ k k opened xort id opened_sum ].
  rewrite /CFParty.
  destruct (honest i).
  rewrite pars_pars.
  apply CFRealParty_honest_externalE.
  done.
Qed.

Lemma CFRealParty_compE (k : nat) {n} (honest : pred 'I_(n.+1)) advCommit advOpen advCommitted advOpened committed opened commit open out opened_sum :
  pars [::
         \||_(i < n.+1) CFParty k _ honest advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i) (tnth out i) ; 
          @cfold _ k k opened xort id opened_sum ] =0 
  pars [::
          \||_(i < n.+1 | honest i) CFRealParty_honest_external k committed opened (tnth commit i) (tnth open i);
          \||_(i < n.+1 | honest i) Out (tnth out i) (copy (tnth opened_sum ord_max));
       \||_(i < n.+1 | ~~ honest i) CFRealParty_corr k _ advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i);
          @cfold _ k k opened xort id opened_sum ]. 
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
          
Lemma opened_sumE (k : nat) {n} (commits : (n.+1).-tuple (chan k)) (opens : (n.+1).-tuple (chan TUnit)) (committed : (n.+1).-tuple (chan TUnit)) (opened : (n.+1).-tuple (chan k)) (opened_sum : (n.+1).-tuple (chan k))
      (opens_sum : (n.+1).-tuple (chan TUnit))
      (commits_sum : (n.+1).-tuple (chan k))
  :
  pars [::
          @cfold _ k k commits xort id commits_sum;
          read_all opens opens_sum;
          @cfold _ k k opened xort id opened_sum;
          \||_(i < n.+1) FComm k (tnth commits i)  (tnth committed i) (tnth opens i) (tnth opened i)]  =0

  pars [::
          @cfold _ k k commits xort id commits_sum;
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
  apply EqOut.
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
  apply EqOut.
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

Definition CFRealSimpl (k : nat) {n}
           (honest : pred 'I_(n.+1))
           (out advCommit : (n.+1).-tuple (chan k)) 
           (advOpen : (n.+1).-tuple (chan TUnit))
           (advCommitted : (n.+1).-tuple ((n.+1).-tuple (chan TUnit)))
           (advOpened : (n.+1).-tuple ((n.+1).-tuple (chan k))) :=
  commit <- newvec n.+1 @ k ;;
  committed <- newvec n.+1 @ TUnit ;;
  open <- newvec n.+1 @ TUnit ;;
  opened <- newvec n.+1 @ k ;;
  commits_sum <- newvec n.+1 @ k ;;
  opens_sum <- newvec n.+1 @ TUnit ;;
  pars [::
          \||_(i < n.+1) FComm k (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);
          \||_(i < n.+1 | honest i) CFRealParty_honest_external k committed opened (tnth commit i) (tnth open i);
       \||_(i < n.+1 | honest i) Out (tnth out i)
          (
            _ <-- Read (tnth opens_sum ord_max) ;;
            x <-- Read (tnth commits_sum ord_max) ;;
            Ret x);
       \||_(i < n.+1 | ~~ honest i) CFRealParty_corr k _ advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i);
          @cfold _ k k commit xort id commits_sum;
          read_all open opens_sum
]. 


Lemma CFRealSimplE (k : nat) {n}
           (honest : pred 'I_(n.+1))
           (out advCommit : (n.+1).-tuple (chan k)) 
           (advOpen : (n.+1).-tuple (chan TUnit))
           (advCommitted : (n.+1).-tuple ((n.+1).-tuple (chan TUnit)))
           (advOpened : (n.+1).-tuple ((n.+1).-tuple (chan k))) :
  CFReal k _ honest out advCommit advOpen advCommitted advOpened =0
  CFRealSimpl k honest out advCommit advOpen advCommitted advOpened.
  rewrite /CFReal.
  etransitivity.
  apply EqNew_vec => commit _ _.
  apply EqNew_vec => committed _ _.
  apply EqNew_vec => open _ _.
  apply EqNew_vec => opened _ _.
  rewrite -(@new_cfold_remove _ k k commit xort id).
  apply EqNew_vec => commits_sum _ _.
  rewrite -(@new_cfold_remove _ TUnit TUnit open (fun _ _ => vtt) (fun _ => vtt)).
  apply EqNew_vec => opens_sum _ _.
  rewrite -(@new_cfold_remove _ k k opened xort id).
  apply EqNew_vec => opened_sum _ _.
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

  intros; repeat set_tac.
  right; right; left.
  eapply In_big; rewrite //=.
  right; left; right; done.
  apply mem_index_enum.

  intros; repeat set_tac.
  right; left.
  eapply In_big; rewrite //=.
  right; left; left; right; done.
  apply mem_index_enum.

  intros; repeat set_tac.
  left.
  eapply In_big; rewrite //=.
  left; left; right; done.
  apply mem_index_enum.

  rewrite /CFRealSimpl.

  apply EqNew_vec => commit _ _.
  apply EqNew_vec => committed _ _.
  apply EqNew_vec => open _ _.
  apply EqNew_vec => opened _ _.

  apply EqNew_vec => commits_sum _ _.
  apply EqNew_vec => opens_sum _ _.

  etransitivity.
  etransitivity.
  apply EqNew_vec => x _ _; swap_tac 0 1.
  apply EqRefl.
  rewrite pars_big_remove.
  apply EqRefl.

  intros; repeat set_tac.
  right; right; right; right; right; left.
  eapply In_big; rewrite //=.
  right; done.
  apply mem_index_enum.

  right; left.
  eapply In_big; rewrite //=.
  right; done.
  apply mem_index_enum.

  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 1.
  apply pars_cons_cong; rewrite //=.
  align.
Qed.

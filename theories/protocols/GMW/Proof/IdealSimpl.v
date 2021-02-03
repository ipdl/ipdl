Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Lib.Crush Lib.SeqOps Lib.OrdLems Lib.Set Ipdl.Big Pars.

Require Import Circ GMWIdeal.

From AAC_tactics Require Import AAC.


Lemma F_new_copy_tup_in {A B n : nat}
      (inA : A.-tuple (chan TBool))
      (inB : B.-tuple (chan TBool))
      (wires : n.-tuple (chan TBool))
      (c : Circ A B n)
      (a2f : A.-tuple (chan TBool)) 
      (b2f : B.-tuple (chan TBool)) :
  pars [::
          evalCirc a2f b2f c wires;
          copy_tup inA a2f;
       copy_tup inB b2f]
  =0
  pars [::
          evalCirc inA inB c wires;
          copy_tup inA a2f;
       copy_tup inB b2f].
    intros.
    apply pars_big_replace; intros.
    destruct (c i); simpl; rewrite //=.
    rewrite /copy.
    rewrite pars_inline_from_big //= /copy.
    align.
    apply EqOut; simp_rxn; done.
    swap_tac 1 2.
    rewrite pars_inline_from_big //= /copy.
    align.
    apply EqOut; simp_rxn; done.
Qed.

Definition GMWIdealSimpl {A B n O : nat}
           (inA : A.-tuple (chan TBool))
           (inB : B.-tuple (chan TBool))
           (outA outB : O.-tuple (chan TBool))
           a2advI a2advO b2advI_timing 
           (c : Circ A B n)
           (outs : circOuts n O) :=
  wires <- newvec n @ TBool ;;
  pars [::
          evalCirc inA inB c wires;
          deliverOuts outs wires outA;
          deliverOuts outs wires a2advO;
          deliverOuts outs wires outB;
          copy_tup inA a2advI;
          Outvec b2advI_timing (fun j => _ <-- Read (tnth inB j) ;; Ret vtt) ].
         
Lemma GMWIdealE {A B n O : nat} `{Inhabited 'I_O} `{Inhabited 'I_A} `{Inhabited 'I_B} `{Inhabited 'I_n}
           (inA : A.-tuple (chan TBool))
           (inB : B.-tuple (chan TBool))
           (outA outB : O.-tuple (chan TBool))
           a2advI a2advO b2advI_timing 
           (c : Circ A B n)
           (outs : circOuts n O) :
  tup_disj inB b2advI_timing ->
  tup_disj inA a2advI ->
  GMWIdeal inA inB outA outB a2advI a2advO b2advI_timing c outs =0
  GMWIdealSimpl inA inB outA outB a2advI a2advO b2advI_timing c outs.
  intros.
  rewrite /GMWIdeal.
  etransitivity.
  apply EqNew_vec => a2f _ _.
  apply EqNew_vec => b2f _ _.
  apply EqNew_vec => f2a _ _.
  apply EqNew_vec => f2b _ _.
  rewrite /Funct.
  rewrite newPars.
  apply EqNew_vec => w _ _.
  setoid_rewrite pars_pars at 1; simpl.
  rewrite /IdealParty_alice.
  swap_tac 0 3.
  setoid_rewrite pars_pars at 1; simpl.
  swap_tac 0 7.
  setoid_rewrite pars_pars at 1; simpl.
  rewrite /copy_tup /deliverOuts.
  rewrite /copy.
  repeat ltac:(do_big_inline; simp_all).
  apply EqRefl.
  simpl.
  swap_tac 0 1.
  setoid_rewrite (newvec_newvec O n).
  under_new rewrite pars_big_remove; last first; [ intros; repeat set_tac | apply EqRefl].
  left; eapply in_big_ord; left; right; done.
  simpl.

  setoid_rewrite (newvec_newvec O n).
  swap_tac 0 6.
  under_new rewrite pars_big_remove; last first; [ intros; repeat set_tac | apply EqRefl].
  left; eapply in_big_ord; left; right; done.
  simpl.

  etransitivity.
  apply EqNew_vec => x _ _ .
  apply EqNew_vec => y _ _ .
  apply EqNew_vec => z _ _ .
  swap_tac 0 6.
  swap_tac 1 7.
  rewrite (pars_split 3); simpl.
  rewrite F_new_copy_tup_in //=.
  rewrite -pars_cat //=.
  apply EqRefl.

  simpl.
  setoid_rewrite (newvec_newvec B).
  swap_tac 0 2.
  under_new rewrite pars_big_remove; last first; [ intros; repeat set_tac | apply EqRefl].
  right; right; right; left; eapply in_big_ord; left; right; done.
  simpl.
  rewrite newvec_newvec.
  under_new rewrite pars_big_remove; last first; [ intros; repeat set_tac | apply EqRefl].
  right; right; right; right; right; left; eapply in_big_ord; left; right; done.
  simpl.
  apply EqNew_vec => v _ _.
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 1.
  apply pars_cons_cong; rewrite //=.
 Qed.

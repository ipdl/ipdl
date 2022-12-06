Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Lib.SeqOps Lib.OrdLems Lib.Set Ipdl.Big Pars.

Require Import Circ GMWIdeal.


Lemma F_new_copy_tup_in {chan : Type -> Type} {A B n : nat}
      (inA : A.-tuple (chan bool))
      (inB : B.-tuple (chan bool))
      (wires : n.-tuple (chan bool))
      (c : Circ A B n)
      (a2f : A.-tuple (chan bool)) 
      (b2f : B.-tuple (chan bool)) :
  pars [::
          evalCirc a2f b2f c wires;
          copy_tup inA a2f;
       copy_tup inB b2f]
  =p
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
    apply EqCongReact; simp_rxn; done.
    swap_tac 1 2.
    rewrite pars_inline_from_big //= /copy.
    align.
    apply EqCongReact; simp_rxn; done.
Qed.

Definition GMWIdealSimpl {chan : Type -> Type} {A B n O : nat}
           (inA : A.-tuple (chan bool))
           (inB : B.-tuple (chan bool))
           (outA outB : O.-tuple (chan bool))
           a2advI a2advO b2advI_timing 
           (c : Circ A B n)
           (outs : circOuts n O) :=
  wires <- newvec n @ bool ;;
  pars [::
          evalCirc inA inB c wires;
          deliverOuts outs wires outA;
          deliverOuts outs wires a2advO;
          deliverOuts outs wires outB;
          copy_tup inA a2advI;
          Outvec b2advI_timing (fun j => _ <-- Read (tnth inB j) ;; Ret tt) ].
         
Lemma GMWIdealE {chan : Type -> Type} {A B n O : nat} `{Inhabited 'I_O} `{Inhabited 'I_A} `{Inhabited 'I_B} `{Inhabited 'I_n}
           (inA : A.-tuple (chan bool))
           (inB : B.-tuple (chan bool))
           (outA outB : O.-tuple (chan bool))
           a2advI a2advO b2advI_timing 
           (c : Circ A B n)
           (outs : circOuts n O) :
  GMWIdeal inA inB outA outB a2advI a2advO b2advI_timing c outs =p
  GMWIdealSimpl inA inB outA outB a2advI a2advO b2advI_timing c outs.
  intros.
  rewrite /GMWIdeal.
  etransitivity.
  apply EqCongNew_vec => a2f .
  apply EqCongNew_vec => b2f .
  apply EqCongNew_vec => f2a .
  apply EqCongNew_vec => f2b .
  rewrite /Funct.
  rewrite newPars.
  apply EqCongNew_vec => w .
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
  under_new rewrite pars_big_remove; apply EqRefl.
  simpl.

  setoid_rewrite (newvec_newvec O n).
  swap_tac 0 6.
  under_new rewrite pars_big_remove; apply EqRefl.
  simpl.

  etransitivity.
  apply EqCongNew_vec => x  .
  apply EqCongNew_vec => y  .
  apply EqCongNew_vec => z  .
  swap_tac 0 6.
  swap_tac 1 7.
  rewrite (pars_split 3); simpl.
  rewrite F_new_copy_tup_in //=.
  rewrite -pars_cat //=.
  apply EqRefl.

  simpl.
  setoid_rewrite (newvec_newvec B).
  swap_tac 0 2.
  under_new rewrite pars_big_remove; apply EqRefl.
  simpl.
  rewrite newvec_newvec.
  under_new rewrite pars_big_remove; apply EqRefl.
  simpl.
  apply EqCongNew_vec => v .
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 1.
  apply pars_cons_cong; rewrite //=.
 Qed.

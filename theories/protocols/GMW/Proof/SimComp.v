
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Ipdl.Tacs Lib.Crush Lib.Set Ipdl.Big Pars. 

Require Import GMWIdeal OTIdeal Circ GMWReal IdealSimpl.


Definition sim_perform_op {A B n} (o : Op A B n) (ot_bit : chan TBool)
           (aliceIn : A.-tuple (chan TBool)) (bobIn : B.-tuple (chan TBool))
           (wires : n.-tuple (chan TBool)) (w : chan TBool) :=
  match o with
  | InA a => Out w (copy (tnth aliceIn a))
  | InB a => Out w (copy (tnth bobIn a))
  | Xor x y =>
    Out w (a <-- Read (tnth wires x) ;; b <-- Read (tnth wires y) ;; Ret (a (+) b : TBool)) 
  | Not x =>
    Out w (
          x <-- Read (tnth wires x) ;;
          Ret (~~ x : TBool))
  | And x y =>
    r <- new TBool ;;
    pars [::
            Out r (Unif TBool);
            Out ot_bit (copy r) ;
          Out w (
                r <-- Read r ;;
                x <-- Read (tnth wires x) ;;
                y <-- Read (tnth wires y) ;;
                Ret (r (+) (x && y) : TBool))]
         end.

Definition sim_comp {A B n} (c : Circ A B n) (ot_bits : n.-tuple (chan TBool))
           (aliceIn : A.-tuple (chan TBool)) (bobIn : B.-tuple (chan TBool)) (wires : n.-tuple (chan TBool)) :=
  \||_(j < n) sim_perform_op (c j) (tnth ot_bits j) aliceIn bobIn (tuple_trunc wires j) (tnth wires j).

Definition GMWSim {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (I_a2advI : A.-tuple (chan TBool))
           (I_a2advO : o.-tuple (chan TBool))
           (I_b2advI_timing : B.-tuple (chan TUnit))
           (R_leakOTBits : n.-tuple (chan TBool))
           (R_leakAIn : A.-tuple (chan TBool))
           (R_leakInit_a2b : A.-tuple (chan TBool))
           (R_leakInit_b2a : B.-tuple (chan TBool))
           (R_leakFinal_b2a : o.-tuple (chan TBool)) :=
  wires <- newvec n @ TBool ;;
  a2a <- newvec A @ TBool ;;
  b2a <- newvec B @ TBool ;;
  a2b <- newvec A @ TBool ;;
  pars [::
          copy_tup I_a2advI R_leakAIn;
          Outvec a2b (fun j => _ <-- Read (tnth I_a2advI j) ;; y <-- Unif TBool ;; Ret y) ;
          copy_tup a2b R_leakInit_a2b;
          Outvec b2a (fun j => _ <-- Read (tnth I_b2advI_timing j) ;; y <-- Unif TBool ;; Ret y);
          copy_tup b2a R_leakInit_b2a ;
          Outvec a2a (fun j =>
                        x <-- Read (tnth a2b j) ;;
                        y <-- Read (tnth I_a2advI j) ;;
                        Ret (x (+) y : TBool));
       sim_comp c R_leakOTBits a2a b2a wires;
       Outvec R_leakFinal_b2a (fun j =>
                                 x <-- Read (tnth wires (tnth outs j)) ;;
                                 y <-- Read (tnth I_a2advO j) ;;
                                 Ret (x (+) y : TBool)) ].
       
Definition GMWIdeal_Sim {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (inA : A.-tuple (chan TBool))
           (inB : B.-tuple (chan TBool))
           (outA outB : o.-tuple (chan TBool))
           (R_leakOTBits : n.-tuple (chan TBool))
           (R_leakAIn : A.-tuple (chan TBool))
           (R_leakInit_a2b : A.-tuple (chan TBool))
           (R_leakInit_b2a : B.-tuple (chan TBool))
           (R_leakFinal_b2a : o.-tuple (chan TBool)) :=
  i_a2advi <- newvec A @ TBool ;;
  i_a2advo <- newvec o @ TBool ;;
  i_b2advi_timing <- newvec B @ TUnit ;;
  pars [::
          GMWIdeal inA inB outA outB i_a2advi i_a2advo i_b2advi_timing c outs;
          GMWSim c outs i_a2advi i_a2advo i_b2advi_timing R_leakOTBits R_leakAIn R_leakInit_a2b R_leakInit_b2a R_leakFinal_b2a ].

(* Now we simplify away the ideal leakage channels *)

Definition GMWSimComp_init {A B}
           (inA : A.-tuple (chan TBool))
           (btIn : B.-tuple (chan TBool))
           (leakInA : A.-tuple (chan TBool))
           (a2a : A.-tuple (chan TBool))
           (a2b : A.-tuple (chan TBool))
           (b2a : B.-tuple (chan TBool))
           (leak_a2b : A.-tuple (chan TBool))
           (leak_b2a : B.-tuple (chan TBool)) :=
  pars [::
          copy_tup inA leakInA;
          Outvec a2b (fun j => _ <-- Read (tnth inA j) ;; x <-- Unif TBool ;; Ret x);
          copy_tup a2b leak_a2b;
          Outvec b2a (fun j => _ <-- Read (tnth btIn j) ;; x <-- Unif TBool ;; Ret x);
          copy_tup b2a leak_b2a;
          Outvec a2a (fun j => x <-- Read (tnth a2b j) ;; y <-- Read (tnth inA j) ;; Ret (x (+) y : TBool)) ].

Definition GMWSimComp_comp {A B n}
           (c : Circ A B n) (inA : A.-tuple (chan TBool)) (inB : B.-tuple (chan TBool))
           (a2a : A.-tuple (chan TBool)) (b2a : B.-tuple (chan TBool))
           (wires : n.-tuple (chan TBool)) (wA : n.-tuple (chan TBool)) (leakOTBits : n.-tuple (chan TBool)) :=
  pars [::
          evalCirc inA inB c wires;
          sim_comp c leakOTBits a2a b2a wA
  ].
       
Definition GMWSimComp_out {n o} (outs : circOuts n o)
           (wires : n.-tuple (chan TBool)) (wA : n.-tuple (chan TBool))
           (outA : o.-tuple (chan TBool)) (outB : o.-tuple (chan TBool))
           (leakb2a_final : o.-tuple (chan TBool)) :=
  pars [::
          deliverOuts outs wires outA;
          deliverOuts outs wires outB;
          Outvec leakb2a_final (fun j => 
            x <-- Read (tnth wires (tnth outs j)) ;;
            y <-- Read (tnth wA (tnth outs j)) ;;
            Ret (x (+) y : TBool))].

Definition GMWIdeal_sim_comp {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (inA : A.-tuple (chan TBool))
           (inB : B.-tuple (chan TBool))
           (outA outB : o.-tuple (chan TBool))
           (R_leakOTBits : n.-tuple (chan TBool))
           (R_leakAIn : A.-tuple (chan TBool))
           (R_leakInit_a2b : A.-tuple (chan TBool))
           (R_leakInit_b2a : B.-tuple (chan TBool))
           (R_leakFinal_b2a : o.-tuple (chan TBool)) :=
  wires <- newvec n @ TBool ;;
  wA <- newvec n @ TBool ;;
  a2a <- newvec A @ TBool ;;
  b2a <- newvec B @ TBool ;;
  a2b <- newvec A @ TBool ;;
  pars [::
          GMWSimComp_init inA inB R_leakAIn a2a a2b b2a R_leakInit_a2b R_leakInit_b2a;
          GMWSimComp_comp c inA inB a2a b2a wires wA R_leakOTBits;
          GMWSimComp_out outs wires wA outA outB R_leakFinal_b2a ].

Lemma GMWIdeal_simE {A B n o} `{Inhabited 'I_A} `{Inhabited 'I_B} `{Inhabited 'I_n} `{Inhabited 'I_o} (c : Circ A B n) (outs : circOuts n o)
           (inA : A.-tuple (chan TBool))
           (inB : B.-tuple (chan TBool))
           (outA outB : o.-tuple (chan TBool))
           (R_leakOTBits : n.-tuple (chan TBool))
           (R_leakAIn : A.-tuple (chan TBool))
           (R_leakInit_a2b : A.-tuple (chan TBool))
           (R_leakInit_b2a : B.-tuple (chan TBool))
           (R_leakFinal_b2a : o.-tuple (chan TBool)) :
  GMWIdeal_Sim c outs inA inB outA outB R_leakOTBits R_leakAIn R_leakInit_a2b R_leakInit_b2a R_leakFinal_b2a ~=
  GMWIdeal_sim_comp c outs inA inB outA outB R_leakOTBits R_leakAIn R_leakInit_a2b R_leakInit_b2a R_leakFinal_b2a. 
  intros.
  rewrite /GMWIdeal_Sim.
  rewrite /GMWIdeal_sim_comp.
  rewrite /GMWSim.
  etransitivity.
  swap_tac 0 1.
  repeat setoid_rewrite newPars.
  Check newPars.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 8.
  rewrite /GMWIdeal.
  repeat setoid_rewrite newPars.
  setoid_rewrite pars_pars; simpl.
  setoid_rewrite pars_pars; simpl.
  rewrite /IdealParty_alice.
  swap_tac 0 3; setoid_rewrite pars_pars; simpl.
  swap_tac 0 7.
  setoid_rewrite pars_pars; simpl.

  etransitivity.
  repeat ltac:(apply EqNew_vec; intro => _ _).
  rewrite /copy_tup /copy.
  simp_all.

  do_big_inline; simp_all.
  do_big_inline; simp_all.
  do_big_inline; simp_all.
  do_big_inline; simp_all.
  do_big_inline; simp_all.
  
  apply EqRefl.
  simpl.
  swap_tac 0 1.
  swap_tac 1 5.
  swap_tac 2 3.
  rotate_news; simpl.
  rotate_news; simpl.
  under_new rewrite pars_big_remove; [ apply EqRefl; simpl | ].
  intros; repeat set_tac.
    right; right; right; left; eapply in_big_ord; left; right; done.
  simpl.

  under_new rewrite pars_big_remove; [ apply EqRefl; simpl | ].
  intros; repeat set_tac.
    do 7 right; left; eapply in_big_ord; left; right; done.
  simpl.
  
  rotate_news; simpl.
  under_new rewrite pars_big_remove; [ apply EqRefl; simpl | ].
  intros; repeat set_tac.
    do 9 right; left; eapply in_big_ord; left; right; done.
  simpl.

  apply EqRefl.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.


  etransitivity.
  repeat ltac:(apply EqNew_vec; intro =>  _ _).
  swap_tac 0 5.
  swap_tac 1 6.
  swap_tac 2 9.
  rewrite (pars_split 3); simpl.
  rewrite F_new_copy_tup_in //=.
  rewrite -pars_cat //=.
  apply EqRefl.
  simpl.

  rewrite /copy_tup.
  unused_to_front; simpl.
  do 5 ltac:(rotate_news; simpl).
  under_new rewrite pars_big_remove; [ apply EqRefl; simpl | ].
  intros; repeat set_tac.
  do 10 right; left; eapply in_big_ord; left; right; done.
  simpl.
  unused_to_front; simpl.
  rotate_news; simpl.

  under_new rewrite pars_big_remove; [ apply EqRefl; simpl | ].
  intros; repeat set_tac.
  do 5 right; left; eapply in_big_ord; left; right; done.
  simpl.

  rewrite /deliverOuts.
  etransitivity.
  repeat ltac:(apply EqNew_vec; intro => _ _).
  simp_all.
  do_big_inline; simp_all.
  do_big_inline; simp_all.
  do_big_inline; simp_all.
  apply EqRefl.
  simpl.

  
  swap_tac 0 1.
  rotate_news; simpl.
  rotate_news; simpl.
  under_new rewrite pars_big_remove; [ apply EqRefl; simpl | ].
  intros; repeat set_tac.
  left; eapply in_big_ord; left; right; done.
  simpl.

  swap_tac 0 1.
  under_new rewrite pars_big_remove; [ apply EqRefl; simpl | ].
  intros; repeat set_tac.
  left; eapply in_big_ord; left; right; done.
  simpl.

  repeat ltac:(apply EqNew_vec; intro => _ _).
  symmetry.
  rewrite pars_pars //=.
  swap_tac 0 6.
  rewrite pars_pars //=.
  swap_tac 0 8.
  rewrite pars_pars //=.
  rewrite /deliverOuts /copy_tup.
  align; apply Eq_Outvec; intro; repeat ltac:(apply EqBind_r; intros).
  rewrite addbC //=.
  r_swap 0 1.
  done.
Qed.


Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Typ Lib.Perm Lib.SeqOps.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Ipdl.Tacs Lib.Set Ipdl.Big Pars. 

Require Import GMWIdeal OTIdeal Circ GMWReal IdealSimpl.

Section SimComp.
  Context {chan : Type -> Type}.
  Open Scope bool_scope.

Definition sim_perform_op {A B n} (o : Op A B n) (ot_bit : chan bool)
           (aliceIn : A.-tuple (chan bool)) (bobIn : B.-tuple (chan bool))
           (wires : n.-tuple (chan bool)) (w : chan bool) :=
  match o with
  | InA a => pars [:: w ::= (copy (tnth aliceIn a)); close ot_bit]
  | InB a => pars [:: w ::= (copy (tnth bobIn a)); close ot_bit]
  | Xor x y =>
    pars [:: w ::= (a <-- Read (tnth wires x) ;; b <-- Read (tnth wires y) ;; Ret (a (+) b )) ; close ot_bit]
  | Not x =>
    pars [:: w ::= (
          x <-- Read (tnth wires x) ;;
          Ret (~~ x)); close ot_bit]
  | And x y =>
    r <- new bool ;;
    pars [::
            Out r (Samp Unif);
            Out ot_bit (copy r) ;
          Out w (
                r <-- Read r ;;
                x <-- Read (tnth wires x) ;;
                y <-- Read (tnth wires y) ;;
                Ret (r (+) (x && y)))]
         end.

Definition sim_comp {A B n} (c : Circ A B n) (ot_bits : n.-tuple (chan bool))
           (aliceIn : A.-tuple (chan bool)) (bobIn : B.-tuple (chan bool)) (wires : n.-tuple (chan bool)) :=
  \||_(j < n) sim_perform_op (c j) (tnth ot_bits j) aliceIn bobIn (tuple_trunc wires j) (tnth wires j).

Definition GMWSim {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (I_a2advI : A.-tuple (chan bool))
           (I_a2advO : o.-tuple (chan bool))
           (I_b2advI_timing : B.-tuple (chan unit))
           (R_leakOTBits : n.-tuple (chan bool))
           (R_leakAIn : A.-tuple (chan bool))
           (R_leakInit_a2b : A.-tuple (chan bool))
           (R_leakInit_b2a : B.-tuple (chan bool))
           (R_leakFinal_b2a : o.-tuple (chan bool)) :=
  wires <- newvec n @ bool ;;
  a2a <- newvec A @ bool ;;
  b2a <- newvec B @ bool ;;
  a2b <- newvec A @ bool ;;
  pars [::
          copy_tup I_a2advI R_leakAIn;
          Outvec a2b (fun j => _ <-- Read (tnth I_a2advI j) ;; y <-- Samp Unif;; Ret y) ;
          copy_tup a2b R_leakInit_a2b;
          Outvec b2a (fun j => _ <-- Read (tnth I_b2advI_timing j) ;; y <-- Samp Unif;; Ret y);
          copy_tup b2a R_leakInit_b2a ;
          Outvec a2a (fun j =>
                        x <-- Read (tnth a2b j) ;;
                        y <-- Read (tnth I_a2advI j) ;;
                        Ret (x (+) y : bool));
       sim_comp c R_leakOTBits a2a b2a wires;
       Outvec R_leakFinal_b2a (fun j =>
                                 x <-- Read (tnth wires (tnth outs j)) ;;
                                 y <-- Read (tnth I_a2advO j) ;;
                                 Ret (x (+) y : bool)) ].
       
Definition GMWIdeal_Sim {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (inA : A.-tuple (chan bool))
           (inB : B.-tuple (chan bool))
           (outA outB : o.-tuple (chan bool))
           (R_leakOTBits : n.-tuple (chan bool))
           (R_leakAIn : A.-tuple (chan bool))
           (R_leakInit_a2b : A.-tuple (chan bool))
           (R_leakInit_b2a : B.-tuple (chan bool))
           (R_leakFinal_b2a : o.-tuple (chan bool)) :=
  i_a2advi <- newvec A @ bool ;;
  i_a2advo <- newvec o @ bool ;;
  i_b2advi_timing <- newvec B @ unit ;;
  pars [::
          GMWIdeal inA inB outA outB i_a2advi i_a2advo i_b2advi_timing c outs;
          GMWSim c outs i_a2advi i_a2advo i_b2advi_timing R_leakOTBits R_leakAIn R_leakInit_a2b R_leakInit_b2a R_leakFinal_b2a ].

(* Now we simplify away the ideal leakage channels *)

Definition GMWSimComp_init {A B}
           (inA : A.-tuple (chan bool))
           (btIn : B.-tuple (chan bool))
           (leakInA : A.-tuple (chan bool))
           (a2a : A.-tuple (chan bool))
           (a2b : A.-tuple (chan bool))
           (b2a : B.-tuple (chan bool))
           (leak_a2b : A.-tuple (chan bool))
           (leak_b2a : B.-tuple (chan bool)) :=
  pars [::
          copy_tup inA leakInA;
          Outvec a2b (fun j => _ <-- Read (tnth inA j) ;; x <-- Samp Unif;; Ret x);
          copy_tup a2b leak_a2b;
          Outvec b2a (fun j => _ <-- Read (tnth btIn j) ;; x <-- Samp Unif;; Ret x);
          copy_tup b2a leak_b2a;
          Outvec a2a (fun j => x <-- Read (tnth a2b j) ;; y <-- Read (tnth inA j) ;; Ret (x (+) y : bool)) ].

Definition GMWSimComp_comp {A B n}
           (c : Circ A B n) (inA : A.-tuple (chan bool)) (inB : B.-tuple (chan bool))
           (a2a : A.-tuple (chan bool)) (b2a : B.-tuple (chan bool))
           (wires : n.-tuple (chan bool)) (wA : n.-tuple (chan bool)) (leakOTBits : n.-tuple (chan bool)) :=
  pars [::
          evalCirc inA inB c wires;
          sim_comp c leakOTBits a2a b2a wA
  ].
       
Definition GMWSimComp_out {n o} (outs : circOuts n o)
           (wires : n.-tuple (chan bool)) (wA : n.-tuple (chan bool))
           (outA : o.-tuple (chan bool)) (outB : o.-tuple (chan bool))
           (leakb2a_final : o.-tuple (chan bool)) :=
  pars [::
          deliverOuts outs wires outA;
          deliverOuts outs wires outB;
          Outvec leakb2a_final (fun j => 
            x <-- Read (tnth wires (tnth outs j)) ;;
            y <-- Read (tnth wA (tnth outs j)) ;;
            Ret (x (+) y : bool))].

Definition GMWIdeal_sim_comp {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (inA : A.-tuple (chan bool))
           (inB : B.-tuple (chan bool))
           (outA outB : o.-tuple (chan bool))
           (R_leakOTBits : n.-tuple (chan bool))
           (R_leakAIn : A.-tuple (chan bool))
           (R_leakInit_a2b : A.-tuple (chan bool))
           (R_leakInit_b2a : B.-tuple (chan bool))
           (R_leakFinal_b2a : o.-tuple (chan bool)) :=
  wires <- newvec n @ bool ;;
  wA <- newvec n @ bool ;;
  a2a <- newvec A @ bool ;;
  b2a <- newvec B @ bool ;;
  a2b <- newvec A @ bool ;;
  pars [::
          GMWSimComp_init inA inB R_leakAIn a2a a2b b2a R_leakInit_a2b R_leakInit_b2a;
          GMWSimComp_comp c inA inB a2a b2a wires wA R_leakOTBits;
          GMWSimComp_out outs wires wA outA outB R_leakFinal_b2a ].

Lemma GMWIdeal_simE {A B n o} `{Inhabited 'I_A} `{Inhabited 'I_B} `{Inhabited 'I_n} `{Inhabited 'I_o} (c : Circ A B n) (outs : circOuts n o)
           (inA : A.-tuple (chan bool))
           (inB : B.-tuple (chan bool))
           (outA outB : o.-tuple (chan bool))
           (R_leakOTBits : n.-tuple (chan bool))
           (R_leakAIn : A.-tuple (chan bool))
           (R_leakInit_a2b : A.-tuple (chan bool))
           (R_leakInit_b2a : B.-tuple (chan bool))
           (R_leakFinal_b2a : o.-tuple (chan bool)) :
  GMWIdeal_Sim c outs inA inB outA outB R_leakOTBits R_leakAIn R_leakInit_a2b R_leakInit_b2a R_leakFinal_b2a =p
  GMWIdeal_sim_comp c outs inA inB outA outB R_leakOTBits R_leakAIn R_leakInit_a2b R_leakInit_b2a R_leakFinal_b2a. 
  intros.
  rewrite /GMWIdeal_Sim.
  rewrite /GMWIdeal_sim_comp.
  rewrite /GMWSim.
  etransitivity.
  swap_tac 0 1.
  repeat setoid_rewrite newPars.
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
  repeat ltac:(apply EqCongNew_vec; intro).
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
  setoid_rewrite pars_big_remove.
  setoid_rewrite pars_big_remove.
  
  rotate_news; simpl.
  setoid_rewrite pars_big_remove.

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
  repeat ltac:(apply EqCongNew_vec; intro).
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
  setoid_rewrite pars_big_remove.
  unused_to_front; simpl.
  rotate_news; simpl.
  setoid_rewrite pars_big_remove.

  rewrite /deliverOuts.
  etransitivity.
  repeat ltac:(apply EqCongNew_vec; intro).
  simp_all.
  do_big_inline; simp_all.
  do_big_inline; simp_all.
  do_big_inline; simp_all.
  apply EqRefl.
  simpl.

  
  swap_tac 0 1.
  rotate_news; simpl.
  rotate_news; simpl.
  setoid_rewrite pars_big_remove.

  swap_tac 0 1.
  setoid_rewrite pars_big_remove.

  repeat ltac:(apply EqCongNew_vec; intro).
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


Definition GMWSim_t {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (I_a2advI : A.-tuple (chan bool))
           (I_a2advO : o.-tuple (chan bool))
           (I_b2advI_timing : B.-tuple (chan unit))
           (R_leakOTBits : n.-tuple (chan bool))
           (R_leakAIn : A.-tuple (chan bool))
           (R_leakInit_a2b : A.-tuple (chan bool))
           (R_leakInit_b2a : B.-tuple (chan bool))
           (R_leakFinal_b2a : o.-tuple (chan bool)) :
  ipdl_t  (tags R_leakAIn ++ tags R_leakInit_a2b ++ tags R_leakInit_b2a ++ tags R_leakOTBits ++ tags R_leakFinal_b2a)
          (GMWSim c outs I_a2advI I_a2advO I_b2advI_timing R_leakOTBits R_leakAIn R_leakInit_a2b R_leakInit_b2a R_leakFinal_b2a).
  rewrite /GMWSim.
  repeat type_tac.
  apply Outvec_t.
  apply Outvec_t.
  apply Outvec_t.
  eapply Bigpar_t.
  move => i.
  rewrite /sim_perform_op.
  instantiate (1 := fun i => [:: tag (cs ## i); tag (R_leakOTBits ## i) ] ).
  simpl.
  destruct (c i); rewrite /close; repeat type_tac.
  perm_match.
  rewrite !flatten_map_cons !flatten_map_nil cats0.
  rewrite !map_tag_enum.
  done.
  rewrite /tags.
  rewrite !catA.
  perm_tac.
Qed.

End SimComp.

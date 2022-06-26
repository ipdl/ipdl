
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Ipdl.Tacs Pars Big Lib.Set Lib.OrdLems.  

Require Import GMWIdeal OTIdeal Circ GMWReal RealCleanup IdealSimpl SimComp.

  (*
        fold_op a2a a2b b2a b2b (tuple_trunc wA j) (tuple_trunc wB j) (tnth wA j) (tnth wB j) (tnth leakOTBits j) (c j) 
        Out (tnth w j) 
        def of a2a
        def of b2b

        =
        evalOp inA inB (tuple_trunc w j) (c j)  
        sim_perform_op (c j) (tnth otbits j) AIn BIn wA      
        wB := w xor wA
  *)

Ltac align_with_eq H :=
  let t := type of H in
  match t with
  | EqProt (pars ?rs) _ =>
    etransitivity; [ instantiate (1 := pars rs); align |]
                     end.

Section RealIdeal.
  Context {chan : Type -> Type}.
  Open Scope bool_scope.

Lemma GMWProof_core {A B n} (c : Circ A B n)
      (inA : A.-tuple (chan bool))
      (inB : B.-tuple (chan bool))
      (a2a a2b : A.-tuple (chan bool)) 
      (b2a b2b : B.-tuple (chan bool))
      (w wA wB : n.-tuple (chan bool))
      (ot_bits : n.-tuple (chan bool))
  :
    pars [::
          \||_(j < n) fold_op a2a a2b b2a b2b (tuple_trunc wA j) (tuple_trunc wB j) (tnth wA j) (tnth wB j) (tnth ot_bits j) (c j);
         Outvec w (fun j => x <-- Read (tnth wA j) ;; y <-- Read (tnth wB j) ;; Ret ((x (+) y) : bool));
          Outvec a2a
            (fun j : 'I_A =>
             a <-- Read (tnth inA j);;
             b <-- Read (tnth a2b j);; Ret (a (+) b : bool));
          Outvec b2b
            (fun j : 'I_B =>
             a <-- Read (tnth inB j);;
             b <-- Read (tnth b2a j);; Ret (a (+) b : bool));
          Outvec a2b
            (fun j : 'I_A => _ <-- Read (tnth inA j);; y <-- Samp Unif;; Ret y);
          Outvec b2a
            (fun j : 'I_B => _ <-- Read (tnth inB j);; y <-- Samp Unif;; Ret y)
         ] =p 
    pars [::
            Outvec w (fun j => evalOp inA inB (tuple_trunc w j) (c j));
            \||_(j < n) sim_perform_op (c j) (tnth ot_bits j) a2a b2a (tuple_trunc wA j) (tnth wA j);
            Outvec wB (fun j => x <-- Read (tnth wA j) ;; y <-- Read (tnth w j) ;; Ret (x (+) y : bool));
          Outvec a2a
            (fun j : 'I_A =>
             a <-- Read (tnth inA j);;
             b <-- Read (tnth a2b j);; Ret (a (+) b : bool));
          Outvec b2b
            (fun j : 'I_B =>
             a <-- Read (tnth inB j);;
             b <-- Read (tnth b2a j);; Ret (a (+) b : bool));
          Outvec a2b
            (fun j : 'I_A => _ <-- Read (tnth inA j);; y <-- Samp Unif;; Ret y);
          Outvec b2a
            (fun j : 'I_B => _ <-- Read (tnth inB j);; y <-- Samp Unif;; Ret y)
         ]. 
  intros.
  rewrite -par_in_pars.
  rewrite -bigpar_par.
  symmetry.
  rewrite -par_in_pars.
  rewrite -bigpar_par.
  rewrite -par_in_pars.
  rewrite -bigpar_par.
  symmetry.
  
  apply pars_big_hybrid2 => j.
  rewrite !bigpar_par !par_in_pars => Hj.
  swap_tac 0 2.
  rewrite par_in_pars.
  symmetry.
    swap_tac 0 2.
    rewrite !par_in_pars.
  symmetry.
  swap_tac 2 3.
  remember (c j) as op; destruct op.
  + (* case inA *)
    
  rewrite (pars_split 2); simpl.
  rewrite Hj.
  rewrite -pars_cat.
  rewrite pars_pars //=.

  (* 
     lhs w = wA j + wB j = a2a o + a2b o -> inA
     rhs w = inA
  
     ----

     lhs wB = a2b o
     rhs wB = wA j + w j = a2a o + inA o -> a2b o
   *)
  
  inline_tac (Out (tnth w j)) (Out (tnth wA j)); simp_all.
  swap_tac 1 7.
  rewrite pars_inline_from_big //=; simp_all.
  swap_at 0 0 2.
  inline_tac (Out (tnth w j)) (Out (tnth wB j)); simp_all.
  edit_tac 0.
     r_swap 1 2.
     rewrite EqReadSame.
     apply EqBind_r; intro.
     apply EqBind_r; intro.
     rewrite addbK; done.
  swap_tac 1 9.

  rewrite pars_unused_from_big.
    edit_tac 0.
    simp_rxn.
    done.
    2: {
      intros t0 c0.
      case.
      intro; subst; left; done.
      case; intro; case; rewrite //=.
      case; done.
    }

  swap_tac 1 9.
  symmetry.
  swap_tac 0 1; rewrite pars_pars; simpl.
  inline_tac (Out (tnth wB j)) (Out (tnth wA j)); simp_all.
  swap_tac 1 (Outvec a2a).
  rewrite pars_inline_from_big //=; simp_all.
  swap_at 0 0 2.
  inline_tac (Out (tnth wB j)) (Out (tnth w j)); simp_all.
  edit_tac 0.
    rewrite EqReadSame.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    rewrite -addbA addbC addbK //=.
  swap_tac 1 (Outvec a2b).
  
  rewrite pars_tr_from_big //=; last first.
     left; done.
     left; done.
  symmetry.
  swap_tac 3 7.
  rewrite (pars_split 4); simpl.
  rewrite -Hj //= -pars_cat //=.

  symmetry.
  align.

  done.
 + (* case inB *)
    (* first rewrite IH *)
    
  rewrite (pars_split 2); simpl.
  rewrite Hj.
  rewrite -pars_cat.
  rewrite pars_pars //=.

  (* lhs w = wA j + wB j = b2a o + b2b o = inB o
     rhs w = inB o
     -----
     lhs wB = b2b o
     rhs wB = wA j + w j = b2a o + inB o
   *)
  inline_tac (Out (tnth w j)) (Out (tnth wA j)); simp_all.
  swap_at 0 0 1.
  inline_tac (Out (tnth w j)) (Out (tnth wB j)); simp_all.
  swap_tac 1 (Outvec b2b).
  rewrite pars_inline_from_big //=; simp_all.
  edit_tac 0.
    apply EqBind_r; intro.
    rewrite EqReadSame.
    apply EqBind_r; intro.
    rewrite addbC addbK //=.
    apply EqRxnRefl.
  swap_at 0 0 1.
  swap_tac 1 (Outvec b2a).
  rewrite pars_unused_from_big.
      edit_tac 0.
      simp_rxn.
      done.
      2: {
      intros t0 c0.
      case.
      intro; subst; left; done.
      case; intro; case; rewrite //=.
      case; done.
      }
  
  swap_tac 0 (Out (tnth wB j)).
  rewrite fold_outvecE //=.
  swap_tac 1 10.
  rewrite pars_inline_from_big //=; simp_all.
  symmetry.
  swap_tac 0 1; rewrite pars_pars; simpl.
  inline_tac (Out (tnth wB j)) (Out (tnth wA j)); simp_all.
  swap_at 0 0 1.
  inline_tac (Out (tnth wB j)) (Out (tnth w j)); simp_all.
  swap_tac 4 5.
  rewrite (pars_split 4); simpl.
  rewrite Hj //= -pars_cat //=.
  symmetry.
  align.
     apply EqCongReact.
     apply EqBind_r; intro.
     apply EqBind_r; intro.
     rewrite addbC //=.
 done.
+ (* case And *)
  rewrite //= /fold_and //=.
  symmetry; swap_tac 0 1; symmetry.
  rewrite !newPars; apply EqCongNew => r.
  rewrite !pars_pars //=.

  
  (*
  rewrite (pars_split 5); simpl.
  
  rewrite Hj; rewrite -pars_cat //=.
*)
  inline_tac (Out (tnth w j)) (Out (tnth wA j)); simp_all.
  swap_at 0 0 3.
  inline_tac (Out (tnth w j)) (Out (tnth wB j)); simp_all.
  edit_tac 0.
    r_swap 1 6.
    rewrite EqReadSame; apply EqBind_r => xA.
    apply EqBind_r => xB.
    r_swap 1 4.
    rewrite EqReadSame; apply EqBind_r => yA.
    apply EqBind_r => yB.
    rewrite EqReadSame; apply EqBind_r => b.
    instantiate (1 := fun _ => Ret ((xA (+) xB) && (yA (+) yB) : bool)).
    destruct xA, xB, yA, yB, b; rewrite //=.
  swap_at 0 0 4.
  swap_tac 1 (Out r).
  rewrite pars_unused; last by done.
  symmetry.
  swap_tac 0 3.
  swap_tac 1 5.
  rewrite !tnth_tuple_trunc //=.
  rewrite pars_inline_from_big //=; simp_all.
  swap_at 0 0 2.
  rewrite pars_inline_from_big //=; simp_all.

  swap_tac 0 (Out (tnth wB j)).
  inline_tac (Out (tnth wB j)) (Out (tnth wA j)); simp_all.
  swap_at 0 0 3. 
  inline_tac (Out (tnth wB j)) (Out (tnth w j)); simp_all.
  
  
  align.
     apply EqCongReact.
     r_swap 0 2.
     r_swap 1 3.
     done.
     apply EqCongReact.
     r_swap 1 6.
     rewrite EqReadSame.
     r_swap 0 5.
     r_swap 1 3.
     rewrite EqReadSame.
     apply EqBind_r => x.
     r_swap 0 2.
     apply EqBind_r => y.
     apply EqBind_r => z.
     apply EqBind_r => a.
     apply EqBind_r => b.
     destruct x, y, z, a, b; done.

+ (* case Xor *)
  simpl.
  rewrite !pars_pars //=.
  inline_tac (Out (tnth w j)) (Out (tnth wA j)); simp_all.
  swap_at 0 0 2.
  inline_tac (Out (tnth w j)) (Out (tnth wB j)); simp_all.
  edit_tac 0.
  instantiate (1 :=
                 x <-- (a <-- Read (tnth (tuple_trunc wA j) o) ;;
                        b <-- Read (tnth (tuple_trunc wB j) o) ;; Ret (a (+) b : bool)) ;;
                 y <-- (a <-- Read (tnth (tuple_trunc wA j) o0) ;;
                        b <-- Read (tnth (tuple_trunc wB j) o0) ;; Ret (a (+) b : bool)) ;;
                 Ret (x (+) y : bool)).
  symmetry; simp_rxn.
    r_swap 0 1.
    r_swap 1 3.
    repeat ltac:(apply EqBind_r; intro).
    destruct x, x0, x1, x2; rewrite //=.
  swap_tac 1 5.
  rewrite !tnth_tuple_trunc.
  rewrite -pars_inline_from_big //=.
  swap_at 0 0 1.
  rewrite -pars_inline_from_big //=.

  (* Now align wB *)
  swap_tac 1 2.
  swap_tac 2 4.
  symmetry.
  swap_tac 0 1; rewrite pars_pars //=.
  inline_tac (Out (tnth wB j)) (Out (tnth wA j)); simp_all.
  swap_at 0 0 2.
  inline_tac (Out (tnth wB j)) (Out (tnth w j)); simp_all.
  symmetry.

  swap_tac 2 3.

  swap_tac 4 5.
  swap_tac 3 4.
  rewrite (pars_split 4); simpl.
  rewrite Hj -pars_cat //=.

  swap_tac 0 3.
  swap_tac 1 6.

  rewrite pars_inline_from_big //=; simp_all.
  swap_at 0 0 2.
  rewrite pars_inline_from_big //=; simp_all.
  swap_tac 1 6.
  rewrite (pars_split 4); simpl.
  rewrite -Hj -pars_cat //=.
  align.
    apply EqCongReact.
    r_swap 0 3.
    r_swap 1 2.
    r_swap 2 3.
    repeat ltac:(apply EqBind_r; intro).
    destruct x, x0, x1, x2; rewrite //=.
    apply EqCongReact.
    r_swap 0 1.
    done.

 +  (* Case Not *)

   simpl.
   rewrite !pars_pars //=.
   symmetry.
   rewrite !tnth_tuple_trunc.
   swap_tac 0 1; rewrite pars_pars; simpl.
   inline_tac (Out (tnth wB j)) (Out (tnth wA j)); simp_all.
   swap_at 0 0 1.
   inline_tac (Out (tnth wB j)) (Out (tnth w j)); simp_all.
   symmetry.
   rewrite (pars_split 4); simpl.
   rewrite Hj -pars_cat //=.
   swap_tac 0 1.
   swap_tac 1 6.
   rewrite pars_inline_from_big //=; simp_all.
   swap_tac 6 1.
   swap_tac 1 0.

   inline_tac (Out (tnth w j)) (Out (tnth wA j)); simp_all.
   swap_at 0 0 1.
   inline_tac (Out (tnth w j)) (Out (tnth wB j)); simp_all.
   edit_tac 0.
    r_swap 1 2.
    rewrite EqReadSame.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    instantiate (1 := fun x0 => Ret (~~ x0 : bool)).
    destruct x; rewrite //=.

   rewrite (pars_split 4); simpl.
   rewrite -Hj -pars_cat //=.
   swap_tac 1 5.
   rewrite pars_tr_from_big //=; last first.
    2: {
         left; done.
         }
    destruct o; done.
    left; done.
   align. 
    apply EqCongReact.
    r_swap 0 1.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    destruct x0, x; done.
Qed.


Lemma GMWProof' {A B n o} (c : Circ A B n) (outs : circOuts n o)
      (AIn : A.-tuple (chan bool)) (BIn : B.-tuple (chan bool)) 
      (AOut BOut : o.-tuple (chan bool)) (leakOTBits : n.-tuple (chan bool)) (leak_AIn leakInit_a2b : A.-tuple (chan bool)) (leakInit_b2a : B.-tuple (chan bool)) (leakFinal_b2a : o.-tuple (chan bool)) :

  GMWReal_simpl c outs AIn BIn AOut BOut leakOTBits leak_AIn leakInit_a2b leakInit_b2a leakFinal_b2a =p 
  GMWIdeal_sim_comp c outs AIn BIn AOut BOut leakOTBits leak_AIn leakInit_a2b leakInit_b2a leakFinal_b2a.
  rewrite /GMWReal_simpl.
  rewrite /GMWIdeal_sim_comp.
  symmetry.
  (* wires, wA, a2a, b2a, a2b *)
  rotate_news; simpl.
  rotate_news; simpl.
  rotate_news; simpl.
  rotate_news; simpl.
  apply EqCongNew_vec => a2b.
  rotate_news; simpl.
  rotate_news; simpl.
  apply EqCongNew_vec => a2a.
  apply EqCongNew_vec => b2a.
  unfold GMWSimComp_comp.
  (* add wB channel to LHS *)
  etransitivity.
  apply EqCongNew_vec => w.
  apply EqCongNew_vec => wA.
  rewrite -(pars_big_remove (fun (n : 'I_n) =>
                               x <-- Read (tnth w n) ;;
                               y <-- Read (tnth wA n) ;;
                               Ret ((x (+) y) : bool))); last first.
  apply EqRefl.
  simpl.

  (* add b2b channel to LHS *)
  etransitivity.
  apply EqCongNew_vec => w.
  apply EqCongNew_vec => wA.
  apply EqCongNew_vec => wB.
  rewrite -(pars_big_remove (fun (n : 'I_B) =>
                               x <-- Read (tnth BIn n) ;;
                               y <-- Read (tnth b2a n) ;;
                               Ret ((x (+) y) : bool))); last first.
  apply EqRefl.
  simpl.

  (* add w channel to RHS *)
  symmetry.
  etransitivity.
  apply EqCongNew_vec => b2b.
  apply EqCongNew_vec => wA.
  apply EqCongNew_vec => wB.
  rewrite -(pars_big_remove (fun (n : 'I_n) =>
                               x <-- Read (tnth wA n) ;;
                               y <-- Read (tnth wB n) ;;
                               Ret ((x (+) y) : bool))); last first.
  apply EqRefl.
  simpl.
  symmetry.

  rotate_news; simpl.
  rotate_news; simpl.
  rotate_news; simpl.
  apply EqCongNew_vec => b2b.

  rewrite (newvec_newvec).
  apply EqCongNew_vec => wA.
  rewrite (newvec_newvec).
  apply EqCongNew_vec => wB.
  apply EqCongNew_vec => w.

  rewrite /GMWSimComp_init.
  swap_tac 0 2; rewrite pars_pars //=.
  swap_tac 0 8; rewrite pars_pars //=.
  swap_tac 0 10.
  rewrite /GMWSimComp_out pars_pars //=.
  symmetry.
  swap_tac 0 1.
  rewrite pars_pars //=.
  swap_tac 0 9.
  rewrite pars_pars //=.

  rewrite /deliverOuts /sim_comp /copy_tup /evalCirc.

  swap_tac 0 10.
  swap_tac 1 9.
  swap_tac 2 3.
  swap_tac 3 5.
  swap_tac 4 11.
  swap_tac 5 11.
  
  rewrite (pars_split 6); simpl.
  rewrite GMWProof_core //= -pars_cat //=.

  rewrite !fold_outvecE.
  
  swap_tac 0 11.
  swap_Outvec_at 0 0 1. 
  swap_tac 1 2.
  rewrite pars_big_inline //=.
  simp_all.
  swap_tac 2 1.
  swap_tac 11 0.

  rewrite (pars_split 7); simpl.
  rewrite -GMWProof_core //= -pars_cat //=.

  swap_tac 0 10.
  focus_tac 0.
      apply EqProt_big_r; intros.
      apply EqCongReact.
      r_swap 1 2; rewrite EqReadSame.
      apply EqBind_r; intro.
      apply EqBind_r; intro.
      rewrite addbA addbC addbA addbK.
      done.
 
 swap_tac 0 1; simpl.
 rewrite fold_outvecE.
 focus_tac 1.
 instantiate (1 :=
                Outvec AOut (fun j =>
                               _ <-- Read (tnth wA (id ((tnth outs) j))) ;;
                               x <-- Read (tnth w (tnth outs j)) ;; Ret x)).
 apply Eq_Outvec; intro; done.
 rewrite -pars_big_tr_general //=; last first.
 intros; left; done.
 intros; left; done.
 
    
 swap_tac 0 1.
 swap_tac 0 10.
 rewrite (pars_split 6); simpl.
 rewrite GMWProof_core //= -pars_cat //=.

 (* adjust leakFinal_b2a and BOut *)
 
 swap_tac 0 10.
 swap_tac 1 2.
 swap_Outvec_at 0 0 1.
 rewrite pars_big_inline //=.
 simp_all.

 focus_tac 0.
 apply Eq_Outvec.
    intros.
    r_swap 1 2.
    rewrite EqReadSame.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    rewrite addbA addbC addbA addbK //=.
 
 swap_tac 0 12.
 rewrite pars_big_inline //=.
 simp_all.

 swap_tac 0 12.
 swap_tac 1 2.
 swap_tac 0 10. 
 rewrite (pars_split 7); simpl.
 rewrite -GMWProof_core //= -pars_cat //=.


 swap_tac 1 9.
 swap_tac 0 9.

 focus_tac 1.
 instantiate (1 :=
                Outvec BOut (fun j =>
                               _ <-- Read (tnth wA (id ((tnth outs) j))) ;;
                               x <-- Read (tnth w (tnth outs j)) ;; Ret x)).
 apply Eq_Outvec; intro; done.
 rewrite -pars_big_tr_general //=; last first.
 intros; left; done.
 intros; left; done.

 swap_tac 9 0; swap_tac 1 9.

 rewrite (pars_split 6); simpl.
 rewrite GMWProof_core //= -pars_cat //=.
 align.
 apply Eq_Outvec => j.
 r_swap 0 1.
 apply EqBind_r; intro.
 apply EqBind_r; intro.
 rewrite addbC //=.
 apply Eq_Outvec => j.
 r_swap 0 1.
 apply EqBind_r; intro.
 apply EqBind_r; intro.
 rewrite addbC //=.

 apply Eq_Outvec => j.
 r_swap 0 1.
 apply EqBind_r; intro.
 apply EqBind_r; intro.
 rewrite addbC //=.
Qed.

Lemma GMWProof {A B n o} `{Inhabited 'I_n} `{Inhabited 'I_o} `{Inhabited 'I_A} `{Inhabited 'I_B} (c : Circ A B n) (outs : circOuts n o)
      (AIn : A.-tuple (chan bool)) (BIn : B.-tuple (chan bool)) 
      (AOut BOut : o.-tuple (chan bool)) (leakOTBits : n.-tuple (chan bool)) (leak_AIn leakInit_a2b : A.-tuple (chan bool)) (leakInit_b2a : B.-tuple (chan bool)) (leakFinal_b2a : o.-tuple (chan bool)) :

  GMWReal c outs AIn BIn AOut BOut leakOTBits leak_AIn leakInit_a2b leakInit_b2a leakFinal_b2a =p 
  GMWIdeal_Sim c outs AIn BIn AOut BOut leakOTBits leak_AIn leakInit_a2b leakInit_b2a leakFinal_b2a.
  rewrite GMWReal_simplE.
  rewrite GMWIdeal_simE.
  apply GMWProof'.
Qed.

End RealIdeal.

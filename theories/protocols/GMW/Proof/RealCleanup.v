
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Ipdl.Tacs Ipdl.Big Pars Lib.Set.  

Require Import GMWIdeal OTIdeal Circ GMWReal .

Search withOT14.

Check withOTs.

Print NewLike.

Section RealCleanup.
  Context {chan : Type -> Type}.
  Open Scope bool_scope.

Lemma withOTs_cong L o (k1 k2 : L.-tuple OTChannels -> ipdl) :
  (forall v, k1 v =p k2 v) ->
  withOTs L o k1 =p @withOTs chan L o k2.
  intros.
  rewrite /withOTs.
  setoid_rewrite H.
  done.
Qed.
  

Global Instance NewLike_withOTs L o : NewLike chan (withOTs L o).
  constructor.
  intros.
  rewrite /withOTs.
  rewrite newComp; Intro => ins.
  rewrite newComp; Intro => m.
  rewrite newComp; Intro => o0.
  Search (pars _ ||| _).
  rewrite pars_rcons /rcons //=.
  swap_tac 0 2.
  symmetry; swap_tac 0 1.
  rewrite par_in_pars.
  align.
  intros.
  apply withOTs_cong; done.
  intros.
  rewrite /withOTs.
  swap_tac 0 1.
  setoid_rewrite New_in_pars.
  symmetry; rotate_news; simpl.
  Intro => x.
  Intro => y.
  Intro => z.
  Intro => w.
  align.
Qed.

Definition performOuts_comp {n o}
           (outs : circOuts n o) (wA wB : n.-tuple (chan bool))
           (oA oB : o.-tuple (chan bool)) (leak_b2a : o.-tuple (chan bool)) :=
  pars [::
          Outvec oA (fun j =>
                       x <-- Read (tnth wA (tnth outs j)) ;;
                       y <-- Read (tnth wB (tnth outs j)) ;;
                       Ret (x (+) y : bool)%bool);
          Outvec oB (fun j =>
                       x <-- Read (tnth wA (tnth outs j)) ;;
                       y <-- Read (tnth wB (tnth outs j)) ;;
                       Ret (x (+) y : bool)%bool);
          Outvec leak_b2a (fun j => copy (tnth wB (tnth outs j))) ].

Lemma performOuts_compE {n o} `{Inhabited 'I_n} `{Inhabited 'I_o}
           (outs : circOuts n o) (wA wB : n.-tuple (chan bool))
           (oA oB : o.-tuple (chan bool)) (leak_b2a : o.-tuple (chan bool)) :
  a2b <- newvec o @ bool ;;
  b2a <- newvec o @ bool ;;
  pars [::
           performOuts outs wA oA a2b b2a;
           performOuts outs wB oB b2a a2b;
           copy_tup b2a leak_b2a
       ] =p
   performOuts_comp outs wA wB oA oB leak_b2a.
  rewrite /performOuts_comp.
  etransitivity.
  apply EqCongNew_vec => a2b  .
  apply EqCongNew_vec => b2a  .
  rewrite pars_pars //=.
  swap_tac 0 2.
  rewrite pars_pars //=.
  rewrite /copy_tup /copy.
  repeat ltac:(do_big_inline; simp_all).
  apply EqRefl.
  simpl.
  swap_tac 0 3.
  under_new rewrite pars_big_remove; apply EqRefl.
  under_new rewrite pars_big_remove; apply EqRefl.
  align.
  apply Eq_Outvec; intros; r_swap 0 1; done.
  apply Eq_Outvec; intros; apply EqBind_r; intro; apply EqBind_r; intro; rewrite addbC //=.
Qed.

Definition jointInit {A B} (inA a2b a2a : A.-tuple (chan bool)) (inB b2a b2b : B.-tuple (chan bool)) (leakAdv leaka2b : A.-tuple (chan bool)) (leakb2a : B.-tuple (chan bool)) :=
  pars [::
          Outvec a2b (fun j => _ <-- Read (tnth inA j) ;; y <-- Samp Unif;; Ret y);
          Outvec a2a (fun j =>
                        a <-- Read (tnth inA j) ;;
                        b <-- Read (tnth a2b j) ;;
                        Ret (a (+) b : bool)%bool );
          Outvec b2a (fun j =>
                        _ <-- Read (tnth inB j) ;;
                        y <-- Samp Unif;; Ret y);
          Outvec b2b (fun j =>
                        a <-- Read (tnth inB j) ;;
                        b <-- Read (tnth b2a j) ;;
                        Ret (a (+) b : bool)%bool );
          copy_tup inA leakAdv;
          copy_tup a2b leaka2b;
          copy_tup b2a leakb2a ].

Lemma jointInitE {A B} (inA a2b a2a : A.-tuple (chan bool)) (inB b2a b2b : B.-tuple (chan bool)) (leakAdv leaka2b : A.-tuple (chan bool)) (leakb2a : B.-tuple (chan bool)) :
  pars [::
          initAlice _ _ inA leakAdv a2b leaka2b a2a b2a leakb2a;
          initBob _ inB b2a b2b] =p jointInit inA a2b a2a inB b2a b2b leakAdv leaka2b leakb2a.
  rewrite /initAlice.
  rewrite pars_pars //=.
  rewrite /initBob.
  swap_tac 0 5.
  rewrite pars_pars //=.
  rewrite /jointInit.
  align.
Qed.

Definition fold_and (Ax Ay Bx By Az Bz : chan bool) (leakBit : chan bool) :=
  b <- new bool ;;
  pars [::
          Out b (Samp Unif);
          Out leakBit (copy b);
          Out Az (
                r <-- Read b ;;
                x <-- Read Ax ;;
                y <-- Read Ay ;;
                Ret (r (+) (x && y) : bool));
          Out Bz (
                xa <-- Read Ax ;;
                xb <-- Read Bx ;;
                ya <-- Read Ay ;;
                yb <-- Read By ;;
                r <-- Read b ;;
                Ret (
                    (xb && yb) (+) 
                    (xa && yb) (+) 
                                  (ya && xb) (+) r : bool))
       ].

Lemma and_compE (Ax Ay Bx By Az Bz : chan bool) (leakBit : chan bool) :
  withOT14 bool (fun '(i, m, o) =>
                pars [::
                        alice_and Ax Ay leakBit m Az;
                        bob_and Bx By i o Bz ]) =p
  fold_and Ax Ay Bx By Az Bz leakBit.
  rewrite /fold_and.
  rewrite /withOT14.
  rewrite /OT14Ideal.
  swap_tac 0 1.
  setoid_rewrite (pars_pars); simpl.
  swap_tac 0 1; rewrite /bob_and.
  setoid_rewrite (pars_pars); simpl.
  swap_tac 0 1.
  swap_tac 1 3.
  setoid_rewrite pars_fold.
  etransitivity.
  apply EqCongNew => i .
  apply EqCongNew => m .
  rewrite /alice_and; swap_tac 0 1.
  rewrite newPars.
  apply EqCongNew => c .
  rewrite pars_pars //=.
  simp_all.
  swap_tac 0 4.
  swap_tac 1 2.
  swap_at 0 0 1.
  rewrite pars_inline //=; simp_all.
  swap_at 0 0 3.
  swap_tac 1 5.
  rewrite pars_inline //=; simp_all.
  swap_at 0 1 5.
  rewrite EqReadSame.
  swap_at 0 0 5.
  swap_at 0 1 2.
  rewrite EqReadSame.
  
  apply EqRefl.
  setoid_rewrite EqNewExch at 2.
  swap_tac 0 5.
  under_new rewrite new_pars_remove; apply EqRefl.
  rewrite EqNewExch.
  under_new rewrite new_pars_remove; apply EqRefl.
  apply EqCongNew => c .
  align.
  apply EqCongReact.
  r_swap 0 3; apply EqBind_r; intro.
  r_swap 0 1; apply EqBind_r; intro.
  r_swap 0 2; apply EqBind_r; intro.
  apply EqBind_r; intro.
  apply EqBind_r; intro.
  simpl in *.
  repeat match goal with
           | [ x : bool |- _ ] => destruct x end; rewrite //=.
Qed.

Definition fold_op {A B n}
           (AIn_alice AIn_bob : A.-tuple (chan bool))
           (BIn_alice BIn_bob : B.-tuple (chan bool))
           (wA wB : n.-tuple (chan bool)) (zA zB : chan bool) (leakBit : chan bool) (o : Op A B n) :=
  match o with
  | InA a =>
    pars [::
            Out zA (copy (tnth AIn_alice a));
            Out zB (copy (tnth AIn_bob a));
            close leakBit
         ]
  | InB b =>
    pars [::
            Out zA (copy (tnth BIn_alice b));
            Out zB (copy (tnth BIn_bob b));
            close leakBit
         ]
  | And x y =>
    fold_and (tnth wA x) (tnth wA y) (tnth wB x) (tnth wB y) zA zB leakBit
  | Xor x y =>
    pars [::
            Out zA (
              x <-- Read (tnth wA x) ;;
              y <-- Read (tnth wA y) ;;
              Ret (x (+) y : bool));
            Out zB (
              x <-- Read (tnth wB x) ;;
              y <-- Read (tnth wB y) ;;
              Ret (x (+) y : bool));
            close leakBit
         ]
  | Not x =>
    pars [::
            Out zA (
              x <-- Read (tnth wA x) ;; Ret (~~ x : bool));
         Out zB (
               copy (tnth wB x));
            close leakBit
         ] end.

Lemma fold_opE  {A B n} (c : Circ A B n) a2a b2a_init a2b_init b2b wA wB leakOTs :
      (\||_(j < n) withOT14 _ (fun '(i, m, o) =>
                              pars [::
                                      performOp alice (c j) (mkOTChannels i m o (tnth leakOTs j)) a2a b2a_init (tuple_trunc wA j) (tnth wA j);
                                      close_ots alice (c j) (mkOTChannels i m o (tnth leakOTs j));
                                   performOp bob (c j) (mkOTChannels i m o (tnth leakOTs j)) a2b_init b2b (tuple_trunc wB j) (tnth wB j);
                                   close_ots bob (c j) (mkOTChannels i m o (tnth leakOTs j))

      ])) =p
      \||_(j < n) fold_op a2a a2b_init b2a_init b2b (tuple_trunc wA j) (tuple_trunc wB j) (tnth wA j) (tnth wB j) (tnth leakOTs j) (c j).
  apply EqProt_big_r => x _ _.
  destruct (c x); simpl; rewrite /withOT14 /OT14Ideal /performOp.
  swap_tac 0 1; setoid_rewrite pars_pars; simpl.
  swap_tac 0 4; setoid_rewrite new_pars_remove.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 1.
  setoid_rewrite new_pars_remove.
  swap_tac 0 2; setoid_rewrite new_pars_remove.
  align.

  swap_tac 0 4; setoid_rewrite new_pars_remove.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 1.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 1.
  setoid_rewrite new_pars_remove.
  swap_tac 0 3; rewrite new_pars_remove.
  align.

  swap_tac 0 1.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 3.
  setoid_rewrite pars_prot0.
  setoid_rewrite pars_prot0.
  rewrite -and_compE /withOT14; symmetry.
  swap_tac 0 1; setoid_rewrite pars_pars at 1; simpl.

  rewrite /OT14Ideal.
  swap_tac 0 1.
  done.


  setoid_rewrite new_pars_remove.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 1; setoid_rewrite pars_pars; simpl.
  swap_tac 0 1; setoid_rewrite new_pars_remove.
  swap_tac 0 3; setoid_rewrite new_pars_remove.
  align.


  setoid_rewrite new_pars_remove.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 1; setoid_rewrite pars_pars; simpl.
  swap_tac 0 1; setoid_rewrite new_pars_remove.
  swap_tac 0 3; setoid_rewrite new_pars_remove.
  align.
Qed.

Lemma withOTs_big {n} leakOTs (f : _ -> _ -> @ipdl chan) :
  withOTs n leakOTs (fun ots => \||_(j < n) (f j (tnth ots j))) =p
  \||_(j < n) withOT14 _ (fun '(i, m, o) => f j (mkOTChannels i m o (tnth leakOTs j))).
  rewrite /withOTs.
  rewrite /withOT14.
  rewrite bigpar_new.
  Intro => ins.
  rewrite bigpar_new.
  Intro => m.
  rewrite bigpar_new.
  Intro => o.
  rewrite big_pars2.
  align.
  apply EqProt_big_r => x _ _.
  rewrite tnth_mktuple //=.
Qed.

Lemma fold_opE1 {A B n} (c : Circ A B n) a2a b2a_init a2b_init b2b wA wB leakOTs :
      (\||_(j < n) withOT14 _ (fun '(i, m, o) =>
                              pars [::
                                      performOp alice (c j) (mkOTChannels i m o (tnth leakOTs j)) a2a b2a_init (tuple_trunc wA j) (tnth wA j);
                                      close_ots alice (c j) (mkOTChannels i m o (tnth leakOTs j));
                                   performOp bob (c j) (mkOTChannels i m o (tnth leakOTs j)) a2b_init b2b (tuple_trunc wB j) (tnth wB j);
                                      close_ots bob (c j) (mkOTChannels i m o (tnth leakOTs j))
      ])) =p
       @withOTs chan _ leakOTs (fun ots =>
                            \||_(j < n) pars [::
                                                performOp alice (c j) (tnth ots j) a2a b2a_init (tuple_trunc wA j) (tnth wA j);
                                                close_ots alice (c j) (tnth ots j);
                                             performOp bob (c j) (tnth ots j) a2b_init b2b (tuple_trunc wB j) (tnth wB j);
                                      close_ots bob (c j) (tnth ots j)
                         ]).
  by rewrite (withOTs_big leakOTs
                       (fun j otc =>
                          pars [::
                                  performOp alice (c j) otc a2a b2a_init (tuple_trunc wA j) (tnth wA j);
                                  close_ots alice (c j) otc;
                                  performOp bob (c j) otc a2b_init b2b (tuple_trunc wB j) (tnth wB j);
                                  close_ots bob (c j) otc])).
Qed.

Section Simpl.
  Context {A B n o} `{Inhabited 'I_n} `{Inhabited 'I_o} (c : Circ A B n) (outs : circOuts n o)
           (AIn : A.-tuple (chan bool)) 
           (BIn : B.-tuple (chan bool)) 
           (AOut BOut : o.-tuple (chan bool))
           (leakOTs : n.-tuple (chan bool))
           (leak_AIn leakInit_a2b : A.-tuple (chan bool))
           (leakInit_b2a : B.-tuple (chan bool))
           (leakFinal_b2a : o.-tuple (chan bool)).

  Definition GMWReal_simpl :=
  a2b <- newvec A @ bool ;;
  a2a <- newvec A @ bool ;;
  b2a <- newvec B @ bool ;;
  b2b <- newvec B @ bool ;;
  wA <- newvec n @ bool ;;
  wB <- newvec n @ bool ;;
  pars [::
          jointInit AIn a2b a2a BIn b2a b2b leak_AIn leakInit_a2b leakInit_b2a;
          \||_(j < n) fold_op a2a a2b b2a b2b (tuple_trunc wA j) (tuple_trunc wB j) (tnth wA j) (tnth wB j) (tnth leakOTs j) (c j);
          performOuts_comp outs wA wB AOut BOut leakFinal_b2a].

  Lemma GMWReal_simplE :
    GMWReal c outs AIn BIn AOut BOut leakOTs leak_AIn leakInit_a2b leakInit_b2a leakFinal_b2a =p GMWReal_simpl.
    symmetry; rewrite /GMWReal_simpl.
    etransitivity.
    repeat ltac:(apply EqCongNew_vec; intro).
    rewrite -jointInitE.
    rewrite -fold_opE.
    rewrite fold_opE1.
    rewrite pars_pars //=.
    rewrite -performOuts_compE.
    swap_tac 0 3.
    setoid_rewrite newPars at 1.
    setoid_rewrite newPars at 1.
    setoid_rewrite pars_pars at 1; simpl.
    apply EqRefl.
    apply _.
    apply _.
    simpl.
    rewrite /GMWReal.
    repeat setoid_rewrite newPars at 1.
    repeat setoid_rewrite withOTs_newvec.
    simpl.
    rewrite /bobReal.
    symmetry.
    setoid_rewrite pars_pars at 1; simpl.
    swap_tac 0 4.
    repeat setoid_rewrite newPars at 1.
    repeat setoid_rewrite (new_newvec (withOTs n leakOTs) _).
    apply EqCongNew_vec => x.
    setoid_rewrite (newvec_newvec A B).
    apply EqCongNew_vec => y.
    repeat setoid_rewrite (newvec_newvec o A).
    apply EqCongNew_vec => z.
    repeat setoid_rewrite (newvec_newvec _ B).
    apply EqCongNew_vec => x0. 
    rotate_news; simpl.
    rotate_news; simpl.
    setoid_rewrite (newvec_newvec n n).
    apply EqCongNew_vec => y0.
    apply EqCongNew_vec => z0.
    setoid_rewrite (newvec_newvec o o).
    apply EqCongNew_vec => o0.
    apply EqCongNew_vec => o1.
    symmetry.
    swap_tac 0 4.
    rewrite newPars.
    apply newCong; intros.
    rewrite pars_pars; simpl.
    swap_tac 0 3.
    apply pars_cons_cong; rewrite //=.
    symmetry; swap_tac 0 1; symmetry.
    apply pars_cons_cong; rewrite //=.
    symmetry; swap_tac 0 3; symmetry.
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 1.
    symmetry; swap_tac 0 1; symmetry.
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 1.
    symmetry; swap_tac 0 2; symmetry.
    apply pars_cons_cong; rewrite //=.
    rewrite pars1.
    rewrite /performComp.
    etransitivity.
    apply EqProt_big_r; intros.
    rewrite (pars_split 2); simpl; apply EqRefl.
    simpl.
    rewrite bigpar_par.
    rewrite pars2.
    rewrite EqCompComm.
    apply EqCong; done.
    apply _.
    apply _.
    apply _.
    apply _.
 Qed.
End Simpl.

End RealCleanup.

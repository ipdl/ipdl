
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Ipdl.Tacs Ipdl.Big Pars Lib.Set.  

Require Import GMWIdeal OTIdeal Circ GMWReal .

Lemma withOT14_cong L k1 k2 :
  (forall i m o, k1 i m o ~= k2 i m o ) ->
  withOT14 L k1 ~= withOT14 L k2.
  intros; rewrite /withOT14.
  apply EqNew => i _ _ .
  apply EqNew => m _ _ .
  apply EqNew => o _ _ .
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
Qed.

Lemma withOTs_newvec L leak I t k :
  withOTs L leak (fun s =>
                 x <- newvec I @ t ;;
                 k x s) ~=
                           x <- newvec I @ t ;;
                           withOTs L leak (k x).
  induction L.
  simpl.
  done.
  simpl.

  rewrite /withOT14.
  rewrite (New_newvec).
  apply EqNew => i _ _ .
  rewrite (New_newvec).
  apply EqNew => m _ _ .
  rewrite (New_newvec).
  apply EqNew => o _ _ .
  swap_tac 0 1.
  rewrite pars_cons.
  rewrite IHL.
  rewrite -pars_cons.
  rewrite newPars.

  apply EqNew_vec => ots _ _.
  swap_tac 0 1.
  apply pars_cons_cong; rewrite //=.
Qed.

Lemma withOTs_pars_irrel L leak r rs :
  withOTs L leak (fun s =>
                    pars [:: r & rs s]) ~=
  pars [:: r; withOTs L leak (fun s => pars (rs s))].                                               
  induction L.
  simpl.
  apply pars_cons_cong.
  done.
  rewrite pars_pars //= cats0 //=.
  simpl.
  rewrite /withOT14.
  symmetry; swap_tac 0 1.
  repeat setoid_rewrite New_in_pars.
  apply EqNew => i _ _ .
  apply EqNew => m _ _ .
  apply EqNew => o _ _ .
  rewrite pars_pars.
  apply pars_cons_cong; rewrite //=.
  rewrite pars1.
  rewrite IHL.
  swap_tac 0 1.
  done.
Qed.

Lemma withOT14_pars_irrel L r rs :
  withOT14 L (fun i m o => pars [:: r & rs i m o]) ~=
  pars [:: r; withOT14 L (fun i m o => pars (rs i m o))].                                                      
  rewrite /withOT14.
  symmetry.
  swap_tac 0 1.
  repeat setoid_rewrite New_in_pars.
  apply EqNew => x _ _ .
  apply EqNew => y _ _ .
  apply EqNew => z _ _ .
  rewrite pars_pars //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 1.
  rewrite pars_pars //= cats0 //=.
  apply pars_cons_cong; rewrite //=.
  rewrite pars_pars //= cats0 //=.
 Qed.

Require Import Setoid Relation_Definitions Morphisms.
Close Scope bool_scope.

Add Parametric Morphism L : (withOT14 L)
   with signature (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ EqProt))) ==> EqProt as ot14_rel.
  intros.
  apply withOT14_cong.
  done.
Qed.

Lemma withOTs_cong L cs1 cs2 k1 k2 :
  (forall l, k1 l ~= k2 l) ->
  cs1 = cs2 ->
  withOTs L cs1 k1 ~= withOTs L cs2 k2.
  intros; subst; induction L; rewrite //=.
  apply withOT14_cong; intros.
  apply IHL.
  done.
Qed.

Check withOTs.
Add Parametric Morphism L cs : (withOTs L cs)
   with signature (pointwise_relation _ EqProt) ==> EqProt as new_rel.
  intros.
  apply withOTs_cong; done.
Qed.

Open Scope bool_scope.

Instance withOTs_newLike L cs : NewLike (withOTs L cs).
    constructor.
    induction L.
    rewrite //=.
    rewrite //=.
    intros.
    rewrite withOT14_irrel.
    rewrite IHL.
    done.
    intros.
    induction L; rewrite //=.
    rewrite /withOT14.
    repeat setoid_rewrite newComp.
    apply newCong; intro.
    apply newCong; intro.
    apply newCong; intro.
    rewrite pars_rcons //=.
    apply pars_cons_cong; rewrite //=.
    rewrite pars1.
    rewrite -IHL.
    rewrite pars2 //=.
    intros; apply withOTs_cong; done.
Qed.

Lemma newvec_withOTs I t L cs k :
  x <- newvec I @ t ;;
  withOTs L cs (fun s => k x s) ~=
  withOTs L cs (fun s =>
                  x <- newvec I @ t ;;
                  k x s).
    induction L; rewrite //=.
    rewrite /withOT14.
    rewrite New_newvec.
    apply newCong; intros.
    rewrite New_newvec.
    apply newCong; intros.
    rewrite New_newvec.
    apply newCong; intros.
    symmetry; swap_tac 0 1; rewrite pars_cons.
    rewrite -IHL.
    rewrite newComp.
    apply newCong; intros.
    symmetry; swap_tac 0 1.
    rewrite pars_cons.
    done.
Qed.

Definition performOuts_comp {n o}
           (outs : circOuts n o) (wA wB : n.-tuple (chan TBool))
           (oA oB : o.-tuple (chan TBool)) (leak_b2a : o.-tuple (chan TBool)) :=
  pars [::
          Outvec oA (fun j =>
                       x <-- Read (tnth wA (tnth outs j)) ;;
                       y <-- Read (tnth wB (tnth outs j)) ;;
                       Ret (x (+) y : TBool));
          Outvec oB (fun j =>
                       x <-- Read (tnth wA (tnth outs j)) ;;
                       y <-- Read (tnth wB (tnth outs j)) ;;
                       Ret (x (+) y : TBool));
          Outvec leak_b2a (fun j => copy (tnth wB (tnth outs j))) ].

Lemma performOuts_compE {n o} `{Inhabited 'I_n} `{Inhabited 'I_o}
           (outs : circOuts n o) (wA wB : n.-tuple (chan TBool))
           (oA oB : o.-tuple (chan TBool)) (leak_b2a : o.-tuple (chan TBool)) :
  a2b <- newvec o @ TBool ;;
  b2a <- newvec o @ TBool ;;
  pars [::
           performOuts outs wA oA a2b b2a;
           performOuts outs wB oB b2a a2b;
           copy_tup b2a leak_b2a
       ] ~=
   performOuts_comp outs wA wB oA oB leak_b2a.
  rewrite /performOuts_comp.
  etransitivity.
  apply EqNew_vec => a2b _ _ .
  apply EqNew_vec => b2a _ _ .
  rewrite pars_pars //=.
  swap_tac 0 2.
  rewrite pars_pars //=.
  rewrite /copy_tup /copy.
  repeat ltac:(do_big_inline; simp_all).
  apply EqRefl.
  simpl.
  swap_tac 0 3.
  under_new rewrite pars_big_remove; [apply EqRefl | ].
  intros; repeat set_tac.
  right; left; eapply in_big_ord; left; right; done.
  simpl.
  under_new rewrite pars_big_remove; [apply EqRefl | ].
  intros; repeat set_tac.
  right; left; eapply in_big_ord; left; right; done.
  align.
  apply Eq_Outvec; intros; r_swap 0 1; done.
  apply Eq_Outvec; intros; apply EqBind_r; intro; apply EqBind_r; intro; rewrite addbC //=.
Qed.





Definition jointInit {A B} (inA a2b a2a : A.-tuple (chan TBool)) (inB b2a b2b : B.-tuple (chan TBool)) (leakAdv leaka2b : A.-tuple (chan TBool)) (leakb2a : B.-tuple (chan TBool)) :=
  pars [::
          Outvec a2b (fun j => _ <-- Read (tnth inA j) ;; y <-- Unif TBool ;; Ret y);
          Outvec a2a (fun j =>
                        a <-- Read (tnth inA j) ;;
                        b <-- Read (tnth a2b j) ;;
                        Ret (a (+) b : TBool) );
          Outvec b2a (fun j =>
                        _ <-- Read (tnth inB j) ;;
                        y <-- Unif TBool ;; Ret y);
          Outvec b2b (fun j =>
                        a <-- Read (tnth inB j) ;;
                        b <-- Read (tnth b2a j) ;;
                        Ret (a (+) b : TBool) );
          copy_tup inA leakAdv;
          copy_tup a2b leaka2b;
          copy_tup b2a leakb2a ].

Lemma jointInitE {A B} (inA a2b a2a : A.-tuple (chan TBool)) (inB b2a b2b : B.-tuple (chan TBool)) (leakAdv leaka2b : A.-tuple (chan TBool)) (leakb2a : B.-tuple (chan TBool)) :
  pars [::
          initAlice _ _ inA leakAdv a2b leaka2b a2a b2a leakb2a;
          initBob _ inB b2a b2b] ~= jointInit inA a2b a2a inB b2a b2b leakAdv leaka2b leakb2a.
  rewrite /initAlice.
  rewrite pars_pars //=.
  rewrite /initBob.
  swap_tac 0 5.
  rewrite pars_pars //=.
  rewrite /jointInit.
  align.
Qed.


Definition fold_and (Ax Ay Bx By Az Bz : chan TBool) (leakBit : chan TBool) :=
  b <- new TBool ;;
  pars [::
          Out b (Unif TBool);
          Out leakBit (copy b);
          Out Az (
                r <-- Read b ;;
                x <-- Read Ax ;;
                y <-- Read Ay ;;
                Ret (r (+) (x && y) : TBool));
          Out Bz (
                xa <-- Read Ax ;;
                xb <-- Read Bx ;;
                ya <-- Read Ay ;;
                yb <-- Read By ;;
                r <-- Read b ;;
                Ret (
                    (xb && yb) (+) 
                    (xa && yb) (+) 
                                  (ya && xb) (+) r : TBool))
       ].

Lemma and_compE (Ax Ay Bx By Az Bz : chan TBool) (leakBit : chan TBool) :
  withOT14 TBool (fun i m o =>
                pars [::
                        alice_and Ax Ay leakBit m Az;
                        bob_and Bx By i o Bz ]) ~=
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
  apply EqNew => i _ _.
  apply EqNew => m _ _.
  rewrite /alice_and; swap_tac 0 1.
  rewrite newPars.
  apply EqNew => c _ _.
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
  setoid_rewrite NewNew at 2.
  swap_tac 0 5.
  under_new rewrite new_pars_remove; [ apply EqRefl | intros; repeat set_tac].
  rewrite NewNew.
  under_new rewrite new_pars_remove; [ apply EqRefl | intros; repeat set_tac].
  apply EqNew => c _ _.
  align.
  apply EqOut.
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
           (AIn_alice AIn_bob : A.-tuple (chan TBool))
           (BIn_alice BIn_bob : B.-tuple (chan TBool))
           (wA wB : n.-tuple (chan TBool)) (zA zB : chan TBool) (leakBit : chan TBool) (o : Op A B n) :=
  match o with
  | InA a =>
    pars [::
            Out zA (copy (tnth AIn_alice a));
            Out zB (copy (tnth AIn_bob a)) ]
  | InB b =>
    pars [::
            Out zA (copy (tnth BIn_alice b));
            Out zB (copy (tnth BIn_bob b)) ]
  | And x y =>
    fold_and (tnth wA x) (tnth wA y) (tnth wB x) (tnth wB y) zA zB leakBit
  | Xor x y =>
    pars [::
            Out zA (
              x <-- Read (tnth wA x) ;;
              y <-- Read (tnth wA y) ;;
              Ret (x (+) y : TBool));
            Out zB (
              x <-- Read (tnth wB x) ;;
              y <-- Read (tnth wB y) ;;
              Ret (x (+) y : TBool))]
  | Not x =>
    pars [::
            Out zA (
              x <-- Read (tnth wA x) ;; Ret (~~ x : TBool));
         Out zB (
               copy (tnth wB x))] end.

Lemma fold_opE  {A B n} (c : Circ A B n) a2a b2a_init a2b_init b2b wA wB leakOTs :
      (\||_(j < n) withOT14 _ (fun i m o =>
                              pars [::
                                      performOp alice (c j) (mkOTChannels i m o (tnth leakOTs j)) a2a b2a_init (tuple_trunc wA j) (tnth wA j);
                                   performOp bob (c j) (mkOTChannels i m o (tnth leakOTs j)) a2b_init b2b (tuple_trunc wB j) (tnth wB j) ])) ~=
      \||_(j < n) fold_op a2a a2b_init b2a_init b2b (tuple_trunc wA j) (tuple_trunc wB j) (tnth wA j) (tnth wB j) (tnth leakOTs j) (c j).
  apply EqProt_big_r => x _ _.
  destruct (c x); simpl.
  rewrite withOT14_irrel //=.
  rewrite withOT14_irrel //=.
  rewrite and_compE //=.
  rewrite withOT14_irrel //=.
  rewrite withOT14_irrel //=.
Qed.

Lemma withOTs_big {n} leakOTs f :
  withOTs n leakOTs (fun ots => \||_(j < n) (f j (tnth ots j))) ~=
  \||_(j < n) withOT14 _ (fun i m o => f j (mkOTChannels i m o (tnth leakOTs j))).
  induction n.
  rewrite //= !big_ord0 //=.
  symmetry; rewrite big_ord_recl.
  destruct (tupleP leakOTs) as [ot0 leakOTs]; simpl.
  etransitivity.
  edit_right.
  edit_big; intros.
  rewrite tnthS.
  apply EqRefl.
  simpl.
  rewrite -(IHn leakOTs (fun c ots => f (lift ord0 c) ots)).
  rewrite -pars2.
  swap_tac 0 1.
  etransitivity.
  focus_tac 1.
  Search withOT14.
  apply withOT14_cong; intros.
  symmetry.
  apply pars1.
  rewrite -withOT14_pars_irrel.
  apply withOT14_cong; intros.
  rewrite newPars.
  apply withOTs_cong; last first.
  apply eq_tuple; done.
  intros.
  rewrite big_ord_recl -pars2.
  swap_tac 0 1.
  apply pars_cons_cong.
  rewrite tnth0 //=.
  apply pars_cons_cong; rewrite //=.
  apply EqProt_big_r; intros.
  rewrite tnthS //=.
Qed.


  

Lemma fold_opE1 {A B n} (c : Circ A B n) a2a b2a_init a2b_init b2b wA wB leakOTs :
      (\||_(j < n) withOT14 _ (fun i m o =>
                              pars [::
                                      performOp alice (c j) (mkOTChannels i m o (tnth leakOTs j)) a2a b2a_init (tuple_trunc wA j) (tnth wA j);
                                   performOp bob (c j) (mkOTChannels i m o (tnth leakOTs j)) a2b_init b2b (tuple_trunc wB j) (tnth wB j) ])) ~=

       withOTs _ leakOTs (fun ots =>
                            \||_(j < n) pars [::
                                                performOp alice (c j) (tnth ots j) a2a b2a_init (tuple_trunc wA j) (tnth wA j);
                                                performOp bob (c j) (tnth ots j) a2b_init b2b (tuple_trunc wB j) (tnth wB j) ]).
  by rewrite (withOTs_big leakOTs
                       (fun j otc =>
                          pars [::
                                  performOp alice (c j) otc a2a b2a_init (tuple_trunc wA j) (tnth wA j);
                                  performOp bob (c j) otc a2b_init b2b (tuple_trunc wB j) (tnth wB j)])).
Qed.

Section Simpl.
  Context {A B n o} `{Inhabited 'I_n} `{Inhabited 'I_o} (c : Circ A B n) (outs : circOuts n o)
           (AIn : A.-tuple (chan TBool)) 
           (BIn : B.-tuple (chan TBool)) 
           (AOut BOut : o.-tuple (chan TBool))
           (leakOTs : n.-tuple (chan TBool))
           (leak_AIn leakInit_a2b : A.-tuple (chan TBool))
           (leakInit_b2a : B.-tuple (chan TBool))
           (leakFinal_b2a : o.-tuple (chan TBool)).

  Definition GMWReal_simpl :=
  a2b <- newvec A @ TBool ;;
  a2a <- newvec A @ TBool ;;
  b2a <- newvec B @ TBool ;;
  b2b <- newvec B @ TBool ;;
  wA <- newvec n @ TBool ;;
  wB <- newvec n @ TBool ;;
  pars [::
          jointInit AIn a2b a2a BIn b2a b2b leak_AIn leakInit_a2b leakInit_b2a;
          \||_(j < n) fold_op a2a a2b b2a b2b (tuple_trunc wA j) (tuple_trunc wB j) (tnth wA j) (tnth wB j) (tnth leakOTs j) (c j);
          performOuts_comp outs wA wB AOut BOut leakFinal_b2a].

  Lemma GMWReal_simplE :
    GMWReal c outs AIn BIn AOut BOut leakOTs leak_AIn leakInit_a2b leakInit_b2a leakFinal_b2a ~= GMWReal_simpl.
    symmetry; rewrite /GMWReal_simpl.
    etransitivity.
    repeat ltac:(apply EqNew_vec; intro => _ _).
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
    repeat setoid_rewrite withOTs_newvec at 1.
    apply EqNew_vec => x _ _.
    setoid_rewrite (newvec_newvec A B).
    apply EqNew_vec => y _ _ .
    repeat setoid_rewrite (newvec_newvec o A).
    apply EqNew_vec => z _ _ .
    repeat setoid_rewrite (newvec_newvec _ B).
    apply EqNew_vec => x0 _ _ .
    rotate_news; simpl.
    rotate_news; simpl.
    setoid_rewrite (newvec_newvec n n).
    apply EqNew_vec => y0 _ _ .
    apply EqNew_vec => z0 _ _ .
    setoid_rewrite (newvec_newvec o o).
    apply EqNew_vec => o0 _ _ .
    apply EqNew_vec => o1 _ _ .
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
    etransitivity.
    edit_big; intros.
    rewrite pars2; apply EqRefl; simpl.
    simpl.
    rewrite bigpar_par.
    rewrite pars2.
    rewrite ParSym.
    apply EqCong; done.
    apply _.
    apply _.
    apply _.
    apply _.
 Qed.
End Simpl.

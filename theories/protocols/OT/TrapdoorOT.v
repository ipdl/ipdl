
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Lib.Base Pars.
Require Import HCBit OTIdeal.

Module TrapdoorOT (P : HCParams).
  Module HCBit := HCBit(P).
  Import HCBit.

  (* OT channels *)
  Context (i : chan TBool).
  Context (m : chan (TBool ** TBool)).
  Context (o : chan TBool).

  (* Leakage channels for receiver *)
  Context (leaky0 leaky1 : chan D).
  Context (leakEK : chan ek).
  Context (leakd01 : chan (TBool ** TBool)).


  Definition TD_Snd (uv : chan (D ** D)) (c_ek : chan ek) (d01 : chan (TBool ** TBool)) :=
    New tk (fun c_tk =>
     pars [::
       Out c_tk (Samp sampK);
       Out c_ek (x <-- Read c_tk ;; Ret (evalKey x));
       Out d01 (
        m01 <-- Read m;;
        uv <-- Read uv;;
        tk <-- Read c_tk ;;
        Ret (
            let '(m0, m1) := m01 in
            let '(u, v) := uv in
            let c0 := B (evalInv tk u) in
            let c1 := B (evalInv tk v) in
            {{ m0 (+) c0 : TBool, m1 (+) c1 : TBool  }} ) ) ] ).

  Definition TD_Rcv (uv : chan (D ** D)) (c_ek : chan ek) (d01 : chan (TBool ** TBool)) :=
    New D (fun y0 =>
       New D (fun y1 =>
           pars [::
                Out leakEK (copy c_ek);
                Out y0 (Unif D);
                Out leaky0 (copy y0);
                Out y1 (Unif D);
                Out leaky1 (copy y1);
                Out uv (
                      i <-- Read i ;;
                      ek <-- Read c_ek ;;
                      x0 <-- Read y0 ;;
                      x1 <-- Read y1 ;;
                      Ret (if i then {{ x0, eval ek x1 }} else {{ eval ek x0, x1 }} ) );
                Out leakd01 (copy d01);
                Out o (
                      i <-- Read i ;;
                      d01 <-- Read d01 ;;
                      x0 <-- Read y0 ;;
                      x1 <-- Read y1 ;;
                      Ret ((d01 # i) (+) B ((x0, x1) # i) : TBool))
                    ])).

  Definition OT_trapdoor :=
    New _ (fun uv =>
             New _ (fun c_ek =>
                      New _ (fun d01 =>
                                      pars [::
                                              TD_Snd uv c_ek d01;
                                              TD_Rcv uv c_ek d01
             ]))).


  (*+ Begin proof +*)

  Definition OT_trapdoor_simp_r :=
c <- new ek;;
c0 <- new tk;;
c1 <- new D;;
c2 <- new D;;
c3 <- new D;;
c4 <- new D;;
[pars [:: Out leakd01
            (x <-- Read c0;;
             x0 <-- Read c3;;
             x1 <-- Read c4;;
             i0 <-- Read i;;
             m0 <-- Read m;;
             (if i0
              then
                Ret (
                    let '(m1, m2) := m0 in
                    {{
                        m1 (+) B x0 : TBool,
                        m2 (+) B (eval (evalKey x) x1) : TBool
                  }})
              else
                Ret (
                    let '(m1, m2) := m0 in
                    {{
                        m1 (+) B (eval (evalKey x) x0) : TBool,
                        m2 (+) B x1 : TBool
                  }} )
            ) );
          Out c (x <-- Read c0;; Ret (evalKey x)); Out c0 (Samp sampK);
          Out c3 (Unif D);
          Out c2 (x <-- Read c4;; x0 <-- Read c0;; Ret (eval (evalKey x0) x));
          Out c4 (Unif D);
          Out leakEK (copy c); 
         Out leaky0 (copy c1); Out leaky1 (copy c2);
          Out c1 (x <-- Read c3;; x0 <-- Read c0;; Ret (eval (evalKey x0) x))] ].

  Definition OT_trapdoor_simp :=
Out o (x <-- Read i;; m0 <-- Read m;; Ret (m0 # x : TBool))
    ||| OT_trapdoor_simp_r.

  Lemma OT_trapdoor_simpE : OT_trapdoor =0 OT_trapdoor_simp.
    rewrite /OT_trapdoor.
    rewrite /TD_Snd.
    setoid_rewrite newPars.
    setoid_rewrite pars_pars.
    rewrite //=.
    rewrite /TD_Rcv.
    swap_tac 0 3.
    setoid_rewrite newPars.
    setoid_rewrite newPars.
    setoid_rewrite pars_pars.
    simpl.
    etransitivity.
    repeat ltac:(apply EqNew; intro => _ _).
    swap_in (Out o) 0 1.
    inline_tac (Out o) (Out c1).
    simp_tac (Out o).

    swap_in (Out o) 0 1.
    inline_tac (Out o) (Out c).
    simp_tac (Out o).

    swap_in (Out o) 0 1.
    inline_tac (Out o) (Out c0).
    simp_tac (Out o).

    edit_tac 0.

    {
        r_swap 1 5.
        rewrite EqReadSame; apply EqBind_r => tk.
        r_swap 1 4.
        rewrite EqReadSame; apply EqBind_r => i.
        r_swap 1 3.
        rewrite EqReadSame; apply EqBind_r => y.
        r_swap 1 2.
        rewrite EqReadSame; apply EqBind_r => x.
        apply EqBind_r => m.
        instantiate (1 := fun m => Ret (m # i : TBool)).
        destruct m; destruct i; rewrite //= eval_cancel addbK //=.
    }

    (* Undep o *)
    undep_tac (Out o) (Out c2).
    swap_in (Out o) 0 1.
    undep_tac (Out o) (Out c3).
    swap_in (Out o) 0 1.
    undep_tac (Out o) (Out c4).

    apply EqRefl.
    (* Move down c1 *)
    setoid_rewrite (NewNew (TBool ** TBool) tk).
    setoid_rewrite (NewNew (TBool ** TBool) D).
    setoid_rewrite (NewNew (TBool ** TBool) D).
    
    swap_tac 6 0.
    swap_tac 1 5.
    setoid_rewrite pars_fold.

    etransitivity.
    repeat ltac:(apply EqNew; intros).
    simp_tac (Out leakd01).
    swap_at 0 0 1.
    apply EqRefl.

    setoid_rewrite (NewNew (D ** D) ek).
    setoid_rewrite (NewNew (D ** D) tk).
    setoid_rewrite (NewNew (D ** D) D).
    setoid_rewrite (NewNew (D ** D) D).
    swap_tac 1 7.
    setoid_rewrite pars_fold.

    etransitivity.
    repeat ltac:(apply EqNew; intros).
    simp_tac (Out leakd01).
    apply EqRefl.

    (* Now pull out o *)
    swap_tac 0 4.
    setoid_rewrite new_pars_pull; last by apply _.
    setoid_rewrite <- newComp_r; last by apply _.
    setoid_rewrite <- newComp_r; last by apply _.
    setoid_rewrite <- newComp_r; last by apply _.

    (* Now map the c's through the permutation, simplify leakd01 *)
    apply EqCong.
    done.
    etransitivity.
    apply EqNew => ek _ _.
    apply EqNew => tk _ _.

    (* Make the samps depend on tk *)
    swap_tac 1 6.
    apply EqNew; intro => _ _.
    apply EqNew; intro => _ _.
    rewrite pars_mkdep //=.
    edit_tac 0.
    apply EqBind_r; intro.
    apply (EqSampBijection _ (eval (evalKey x))).
    eapply can_inj.
    apply eval_cancel.
    swap_at 0 0 1.
    rewrite -pars_fold.

    swap_tac 0 3.
    swap_tac 1 2.
    apply EqNew; intro  => _ _;
    rewrite pars_mkdep //=.
    edit_tac 0.
    apply EqBind_r; intro.
    apply (EqSampBijection _ (eval (evalKey x))).
    eapply can_inj.
    apply eval_cancel.
    swap_at 0 0 1.
    rewrite -pars_fold.
    apply EqNew; intro => _ _.

    swap_at 5 0 3.
    swap_at 5 1 3.
    apply EqRefl.

    (* Now inline the postcomputations *)
    etransitivity.
    repeat ltac:(apply EqNew; intro => _ _).
    inline_tac (Out leakd01) (Out c2).
    simp_tac leakd01.
    swap_at 0 0 2. 
    inline_tac (Out leakd01) (Out c1).
    simp_tac leakd01.
    swap_at 0 0 5.
    inline_tac (Out leakd01) (Out c).
    simp_tac leakd01.

    edit_tac 0.
    r_swap 1 2.
    rewrite EqReadSame.
    r_swap 1 3.
    rewrite EqReadSame.
    r_swap 1 5.
    rewrite EqReadSame.
    apply EqBind_r; intros.
    apply EqBind_r; intros.
    apply EqBind_r; intros.
    apply EqBind_r; intro i.
    apply EqBind_r; intros m.
    apply EqRxnRefl.
    apply EqRefl.
    repeat ltac:(apply EqNew; intro => _ _).
    apply pars_cons_cong.
    apply EqOut.
    repeat ltac:(apply EqBind_r; intro).
    destruct x3.
    destruct x2.
    simpl.
    rewrite !eval_cancel //=.
    rewrite //=.
    rewrite !eval_cancel //=.
    rewrite //=.
    apply _.
    apply _.
    apply _.
 Qed.

Definition OT_trapdoor_HCBitPairSim c_ek y1 y2 (b1 b2 : chan TBool) :=
                  pars [::
                     Out leaky0 (copy y1);
                     Out leaky1 (copy y2);
                     Out leakEK (copy c_ek);
                       Out leakd01 (
                             ek <-- Read c_ek ;;
                             y1 <-- Read y1 ;;
                             y2 <-- Read y2 ;;
                             i <-- Read i ;;
                             m <-- Read m ;;
                             b1 <-- Read b1 ;;
                             b2 <-- Read b2 ;;
                             Ret (
                                 let '(m1, m2) := m in
                                 if i then
                                   {{ m1 (+) b1 : TBool,
                                           m2 (+) (B y2) : TBool }}
                                 else
                                   {{
                                       m1 (+) B y1 : TBool,
                                       m2 (+) b2 : TBool
                                                     }} ) ) ].
                                                                    

Lemma OT_trapdoor_simp_rE :
  OT_trapdoor_simp_r =0
                        withHCBitPairReal OT_trapdoor_HCBitPairSim.
  rewrite /withHCBitPairReal /OT_trapdoor_HCBitPairSim.
  rewrite /OT_trapdoor_simp_r.
  apply EqNew => ek Hek.
  symmetry.
  rewrite /HCBitPairReal.
  setoid_rewrite newPars.
  setoid_rewrite newPars.
  setoid_rewrite newPars.
  setoid_rewrite pars_pars.
  simpl.
  swap_tac 0 8.
  setoid_rewrite pars_pars.
  simpl.
  rewrite (NewNew tk D).
  apply EqNew => y1 _ _.
  rewrite (NewNew tk D).
  apply EqNew => y2 _ _.
  setoid_rewrite (NewNew TBool tk).
  setoid_rewrite (NewNew TBool tk).
  apply EqNew => tk _ _.
  setoid_rewrite (NewNew TBool D).
  setoid_rewrite (NewNew TBool D).
  apply EqNew => w1 _ _.
  setoid_rewrite (NewNew TBool D).
  setoid_rewrite (NewNew TBool D).
  apply EqNew => w2 _ _.

  (* fold in the b's *)
  etransitivity.
  apply EqNew; intro => _ _.
  apply EqNew; intro => _ _.
  swap_at 3 0 6.
  apply EqRefl.

  swap_tac 0 3.
  swap_tac 1 10.
  setoid_rewrite pars_fold.
  etransitivity.
  apply EqNew; intro => _ _.
  simp_tac leakd01.
  swap_at 0 0 6.
  apply EqRefl.

  swap_tac 1 8.
  setoid_rewrite pars_fold.
  simp_tac leakd01.
  swap_at 0 0 2.
  inline_tac leakd01 (Out ek).
  simp_tac leakd01.

  swap_at 0 0 3.
  inline_tac leakd01 (Out y1).
  simp_tac leakd01.

  swap_at 0 0 5.
  inline_tac leakd01 (Out y2).
  simp_tac leakd01.

  swap_at 0 1 2.
  rewrite EqReadSame.
  swap_at 0 0 5.
  swap_at 0 1 2.
  rewrite EqReadSame.
  swap_at 0 0 2.
  swap_at 0 1 4.
  rewrite EqReadSame.

  swap_at 0 0 2.
  inline_tac leakd01 (Out ek).
  simp_tac leakd01.
  swap_at 0 1 3.
  rewrite EqReadSame.
  apply pars_cons_cong.
  apply EqOut.
  repeat ltac:(apply EqBind_r; intros).
  destruct x3; destruct x2; done.

  inline_tac (Out y2) (Out ek).
  simp_tac y2.
  inline_tac (Out y1) (Out ek).
  simp_tac y1.

  align.
  apply EqOut; r_swap 0 1; done.
  apply EqOut; r_swap 0 1; done.
  apply _.
  apply _.
  apply _.
Qed.


Definition OT_trapdoor_OTSim (leakO : chan TBool) :=
  withHCBitPairIdeal (fun c_ek y1 y2 b1 b2 =>
                  pars [::
                     Out leaky0 (copy y1);
                     Out leaky1 (copy y2);
                     Out leakEK (copy c_ek);
                       Out leakd01 (
                             ek <-- Read c_ek ;;
                             y1 <-- Read y1 ;;
                             y2 <-- Read y2 ;;
                             i <-- Read i ;;
                             o <-- Read leakO ;;
                             b1 <-- Read b1 ;;
                             b2 <-- Read b2 ;;
                             Ret (
                                 if i then
                                   {{
                                       b1 : TBool,
                                       o (+) B y2 : TBool
                                   }}
                                 else
                                   {{
                                       o (+) B y1 : TBool,
                                                    b2
                                                      }} )) ]).

Lemma OT_trapdoor_OTSimE :
  withHCBitPairIdeal OT_trapdoor_HCBitPairSim =0 (leakO <- new TBool ;; OT_trapdoor_OTSim leakO ||| OTIdeal _ i m leakO).
  symmetry.
  (* First, fold in the leakO *)

  rewrite /OT_trapdoor_OTSim.
  rewrite /withHCBitPairIdeal.
  rewrite /OTIdeal.
  repeat setoid_rewrite NewComp.
  setoid_rewrite pars_rcons; simpl.
  swap_tac 0 1.
  setoid_rewrite pars_pars; simpl.

  setoid_rewrite (NewNew TBool ek).
  setoid_rewrite (NewNew TBool D).
  setoid_rewrite (NewNew TBool D).
  setoid_rewrite (NewNew TBool TBool) at 1.
  setoid_rewrite (NewNew TBool TBool) at 2.
  etransitivity.
  repeat ltac:(apply EqNew; intro => _ _).
  swap_tac 0 3.
  swap_at 0 0 4.
  apply EqRefl.
  swap_tac 1 5.
  setoid_rewrite pars_fold.
  (* Now fold in the flips *)
  etransitivity.
  repeat ltac:(apply EqNew; intro => _ _).
  simp_tac leakd01.
  rewrite /HCBitPairIdeal.
  swap_tac 0 3.
  rewrite pars_pars; simpl.
  swap_at (Out leakd01) 0 7.
  swap_at (Out leakd01) 1 7.
  apply EqRefl.
  swap_tac 0 7.
  swap_tac 1 4.
  setoid_rewrite pars_fold.
  swap_tac 1 2.

  under_new swap_at 0 0 1.
  setoid_rewrite pars_fold.
  symmetry.

  rewrite /OT_trapdoor_HCBitPairSim.
  swap_tac 0 5.
  setoid_rewrite par_in_pars.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 3.
  under_new swap_at 0 0 6.
  swap_tac 1 8.
  setoid_rewrite pars_fold.
  under_new swap_at 0 0 6.
  swap_tac 1 6.
  setoid_rewrite pars_fold.
  apply EqNew; intro => _ _.
  apply EqNew; intro => _ _.
  apply EqNew; intro => _ _.
  apply pars_cons_cong.
  apply EqOut.
  r_swap 0 5.
  r_swap 1 3.
  r_swap 2 5.
  r_swap 3 6.
  r_swap 4 6.
  symmetry.
  r_swap 0 2.
  r_swap 1 7.
  rewrite EqReadSame.
  apply EqBind_r; intros.
  r_swap 0 3.
  apply EqBind_r; intros.
  r_swap 0 4.
  apply EqBind_r; intros.
  r_swap 0 2.
  apply EqBind_r; intros.
  r_swap 0 2.
  apply EqBind_r; intros.
  destruct x2; simpl.
  destruct x.
  r_swap 0 1.
  symmetry; r_swap 0 1; symmetry.
  apply EqBind_r; intros.
  rewrite EqBind_r_samp_bijection.
  apply EqBind_r; intro.
  reflexivity.
  apply addbI.
  apply EqBind_r; intros.
  rewrite EqBind_r_samp_bijection.
  apply EqBind_r; intro.
  reflexivity.
  apply addbI.
  align.
  swap_tac 0 6.
  rewrite pars_prot0.
  align.

  reflexivity.
Qed.

  Lemma OT_Trapdoor_Security : 
  (forall c1 c2 c3, 
  HCBitReal c1 c2 c3 =0 HCBitIdeal c1 c2 c3) ->
    OT_trapdoor =0 (leakO <- new TBool ;; pars [:: OTIdeal _ i m o; OT_trapdoor_OTSim leakO; OTIdeal _ i m leakO] ).
    intro.
    rewrite OT_trapdoor_simpE.
    rewrite /OT_trapdoor_simp.
    symmetry.
    rewrite new_pars_pull.
    apply EqCong.
    done.
    setoid_rewrite pars2.
    rewrite OT_trapdoor_simp_rE.
    rewrite -OT_trapdoor_OTSimE.
    rewrite withHCBitPairRealP.
    done.
    done.
   Qed.

End TrapdoorOT.

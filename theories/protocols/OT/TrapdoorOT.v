(* The classic construction of an oblivious transfer protocol from a hard-core predicate, due to GMW. We assume the receiver is semi-honest. *)


Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Lib.Base Pars.
Require Import HCBit OTIdeal Ipdl.Approx.

Open Scope bool_scope. 
Module TrapdoorOT (P : HCParams).
  Module HCBit := HCBit(P).
  Import HCBit.
  

  Section TrapdoorOT.
  Context {chan : Type -> Type}.
  (* OT channels *)
  Context (i : chan bool).
  Context (m : chan (bool * bool)).
  Context (o : chan bool).

  (* Leakage channels for receiver *)
  Context (leaky0 leaky1 : chan D.-bv).
  Context (leakEK : chan ek.-bv).
  Context (leakd01 : chan (bool * bool)).


  Definition TD_Snd (uv : chan (D.-bv * D.-bv)) (c_ek : chan ek.-bv) (d01 : chan (bool * bool)) :=
    c_tk <- new tk.-bv ;;
     pars [::
       c_tk ::= (Samp sampK);
       c_ek ::= (x <-- Read c_tk ;; Ret (evalKey x));
       d01 ::= (
        m01 <-- Read m;;
        uv <-- Read uv;;
        tk <-- Read c_tk ;;
        Ret (
            let '(m0, m1) := m01 in
            let '(u, v) := uv in
            let c0 := B (evalInv tk u) in
            let c1 := B (evalInv tk v) in
            (m0 (+) c0, m1 (+) c1)) ) ].

  Definition TD_Rcv (uv : chan (D.-bv * D.-bv)) (c_ek : chan ek.-bv) (d01 : chan (bool * bool)) :=
    y0 <- new D.-bv ;;
    y1 <- new D.-bv ;;
           pars [::
                leakEK ::= (copy c_ek);
                y0 ::= (Samp Unif);
                leaky0 ::= (copy y0);
                y1 ::= (Samp Unif);
                leaky1 ::= (copy y1);
                uv ::= (
                      i <-- Read i ;;
                      ek <-- Read c_ek ;;
                      x0 <-- Read y0 ;;
                      x1 <-- Read y1 ;;
                      Ret (if i then ( x0, eval ek x1 ) else (eval ek x0, x1) ) );
                leakd01 ::= (copy d01);
                o ::= (
                      i <-- Read i ;;
                      d01 <-- Read d01 ;;
                      x0 <-- Read y0 ;;
                      x1 <-- Read y1 ;;
                      Ret ((d01 # i) (+) B ((x0, x1) # i) : bool))
                    ].

  Definition OT_trapdoor :=
    uv <- new _ ;;
    c_ek <- new _ ;;
    d01 <- new _ ;;
    pars [:: TD_Snd uv c_ek d01;
            TD_Rcv uv c_ek d01].

  (*+ Begin proof +*)

  Definition OT_trapdoor_simp_r :=
c <- new ek.-bv;;
c0 <- new tk.-bv;;
c1 <- new D.-bv;;
c2 <- new D.-bv;;
c3 <- new D.-bv;;
c4 <- new D.-bv;;
[pars [:: leakd01 ::=
            (x <-- Read c0;;
             x0 <-- Read c3;;
             x1 <-- Read c4;;
             i0 <-- Read i;;
             m0 <-- Read m;;
             (if i0
              then
                Ret (
                    let '(m1, m2) := m0 in
                    ( 
                        m1 (+) B x0 : bool,
                        m2 (+) B (eval (evalKey x) x1) : bool
                  ))
              else
                Ret (
                    let '(m1, m2) := m0 in
                    (
                        m1 (+) B (eval (evalKey x) x0) : bool,
                        m2 (+) B x1 : bool
                  ) )
            ) );
          c ::= (x <-- Read c0;; Ret (evalKey x)); Out c0 (Samp sampK);
          c3 ::= (Samp Unif);
          c2 ::= (x <-- Read c4;; x0 <-- Read c0;; Ret (eval (evalKey x0) x));
          c4 ::= (Samp Unif);
          leakEK ::= (copy c); 
         leaky0 ::= (copy c1); Out leaky1 (copy c2);
          c1 ::= (x <-- Read c3;; x0 <-- Read c0;; Ret (eval (evalKey x0) x))] ].

  Definition OT_trapdoor_simp :=
Out o (x <-- Read i;; m0 <-- Read m;; Ret (m0 # x : bool))
    ||| OT_trapdoor_simp_r.

  Lemma OT_trapdoor_simpE : OT_trapdoor =p OT_trapdoor_simp.
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
    repeat ltac:(apply EqCongNew; intro).
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
        rewrite EqReadSame; apply EqBind_r => i'.
        r_swap 1 3.
        rewrite EqReadSame; apply EqBind_r => y.
        r_swap 1 2.
        rewrite EqReadSame; apply EqBind_r => x.
        apply EqBind_r => m'.
        instantiate (1 := fun m' => Ret (m' # i' : bool)).
        destruct m'; destruct i'; rewrite //= eval_cancel addbK //=.
    }

    (* Undep o *)
    swap_tac 0 (Out o).
    swap_tac 1 (Out c2).
    rewrite -pars_mkdep //=.
    swap_in (Out o) 0 1.
    swap_tac 1 (Out c3).
    rewrite -pars_mkdep //=.
    swap_in (Out o) 0 1.
    swap_tac 1 (Out c4).
    rewrite -pars_mkdep //=.

    apply EqRefl.
    (* Move down c1 *)
    simpl.
    setoid_rewrite (EqNewExch (bool * bool) tk.-bv).
    setoid_rewrite (EqNewExch (bool * bool) D.-bv).
    setoid_rewrite (EqNewExch (bool * bool) D.-bv).
    
    swap_tac 6 0.
    swap_tac 1 5.
    setoid_rewrite pars_fold.

    etransitivity.
    repeat ltac:(apply EqCongNew; intros).
    simp_tac (Out leakd01).
    swap_at 0 0 1.
    apply EqRefl.

    setoid_rewrite (EqNewExch (D.-bv * D.-bv) ek.-bv).
    setoid_rewrite (EqNewExch (D.-bv * D.-bv) tk.-bv).
    setoid_rewrite (EqNewExch (D.-bv * D.-bv) D.-bv).
    setoid_rewrite (EqNewExch (D.-bv * D.-bv) D.-bv).
    swap_tac 1 7.
    setoid_rewrite pars_fold.

    etransitivity.
    repeat ltac:(apply EqCongNew; intros).
    simp_tac (Out leakd01).
    apply EqRefl.

    (* Now pull out o *)
    simpl.
    swap_tac 0 4.
    setoid_rewrite new_pars_pull; last by apply _.
    setoid_rewrite <- newComp_r; last by apply _.
    setoid_rewrite <- newComp_r; last by apply _.
    setoid_rewrite <- newComp_r; last by apply _.

    (* Now map the c's through the permutation, simplify leakd01 *)
    apply EqCong.
    done.
    etransitivity.
    apply EqCongNew => ek .
    apply EqCongNew => tk .

    (* Make the samps depend on tk *)
    swap_tac 1 6.
    apply EqCongNew; intro.
    apply EqCongNew; intro.
    rewrite pars_mkdep //=.
    edit_tac 0.
    apply EqBind_r; intro.
    apply (EqSampBijection _ (eval (evalKey x))).
    eapply can_inj.
    apply eval_cancel.
    apply uniform_Unif.
    swap_at 0 0 1.
    rewrite -pars_fold.

    swap_tac 0 3.
    swap_tac 1 2.
    apply EqCongNew; intro;
    rewrite pars_mkdep //=.
    edit_tac 0.
    apply EqBind_r; intro.
    apply (EqSampBijection _ (eval (evalKey x))).
    eapply can_inj.
    apply eval_cancel.
    apply uniform_Unif.
    swap_at 0 0 1.
    rewrite -pars_fold.
    apply EqCongNew; intro.

    swap_at 5 0 3.
    swap_at 5 1 3.
    apply EqRefl.

    (* Now inline the postcomputations *)
    etransitivity.
    repeat ltac:(apply EqCongNew; intro).
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
    apply EqBind_r; intro i'.
    apply EqBind_r; intros m'.
    apply EqRxnRefl.
    apply EqRefl.
    repeat ltac:(apply EqCongNew; intro).
    apply pars_cons_cong.
    apply EqCongReact.
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

Definition OT_trapdoor_HCBitPairSim c_ek y1 y2 (b1 b2 : chan bool) :=
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
                                   ( m1 (+) b1 : bool,
                                           m2 (+) (B y2) : bool )
                                 else
                                   (
                                       m1 (+) B y1 : bool,
                                       m2 (+) b2 : bool
                                                     ) ) ) ].
                                                                    

Lemma OT_trapdoor_simp_rE :
  OT_trapdoor_simp_r =p
                        withHCBitPairReal OT_trapdoor_HCBitPairSim.
  rewrite /withHCBitPairReal /OT_trapdoor_HCBitPairSim.
  rewrite /OT_trapdoor_simp_r.
  apply EqCongNew => ek.
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
  rewrite (EqNewExch tk.-bv D.-bv).
  apply EqCongNew => y1 .
  rewrite (EqNewExch tk.-bv D.-bv).
  apply EqCongNew => y2 .
  setoid_rewrite (EqNewExch bool tk.-bv).
  setoid_rewrite (EqNewExch bool tk.-bv).
  apply EqCongNew => tk .
  setoid_rewrite (EqNewExch bool D.-bv).
  setoid_rewrite (EqNewExch bool D.-bv).
  apply EqCongNew => w1 .
  setoid_rewrite (EqNewExch bool D.-bv).
  setoid_rewrite (EqNewExch bool D.-bv).
  apply EqCongNew => w2 .

  (* fold in the b's *)
  etransitivity.
  apply EqCongNew; intro.
  apply EqCongNew; intro.
  swap_at 3 0 6.
  apply EqRefl.

  simpl.
  swap_tac 0 3.
  swap_tac 1 10.
  setoid_rewrite pars_fold.
  etransitivity.
  apply EqCongNew; intro.
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
  apply EqCongReact.
  repeat ltac:(apply EqBind_r; intros).
  destruct x3; destruct x2; done.

  inline_tac (Out y2) (Out ek).
  simp_tac y2.
  inline_tac (Out y1) (Out ek).
  simp_tac y1.

  align.
  apply EqCongReact; r_swap 0 1; done.
  apply EqCongReact; r_swap 0 1; done.
  apply _.
  apply _.
  apply _.
Qed.


Definition OT_trapdoor_OTSim (leakO : chan bool) :=
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
                                   (
                                       b1 : bool,
                                       o (+) B y2 : bool
                                   )
                                 else
                                  ( 
                                       o (+) B y1 : bool,
                                                    b2
                                                      ) )) ]).

Lemma OT_trapdoor_OTSimE :
  withHCBitPairIdeal OT_trapdoor_HCBitPairSim =p (leakO <- new bool ;; OT_trapdoor_OTSim leakO ||| OTIdeal _ i m leakO).
  symmetry.
  (* First, fold in the leakO *)

  rewrite /OT_trapdoor_OTSim.
  rewrite /withHCBitPairIdeal.
  rewrite /OTIdeal.
  repeat setoid_rewrite EqCompNew.
  setoid_rewrite pars_rcons; simpl.
  swap_tac 0 1.
  setoid_rewrite pars_pars; simpl.

  setoid_rewrite (EqNewExch bool ek.-bv).
  setoid_rewrite (EqNewExch bool D.-bv).
  setoid_rewrite (EqNewExch bool D.-bv).
  setoid_rewrite (EqNewExch bool bool) at 1.
  setoid_rewrite (EqNewExch bool bool) at 2.
  etransitivity.
  repeat ltac:(apply EqCongNew; intro).
  swap_tac 0 3.
  swap_at 0 0 4.
  apply EqRefl.
  simpl.
  swap_tac 1 5.
  setoid_rewrite pars_fold.
  (* Now fold in the flips *)
  etransitivity.
  repeat ltac:(apply EqCongNew; intro).
  simp_tac leakd01.
  rewrite /HCBitPairIdeal.
  swap_tac 0 3.
  rewrite pars_pars; simpl.
  swap_at 7 0 7.
  swap_at 7 1 7.
  apply EqRefl.
  simpl.
  swap_tac 0 7.
  swap_tac 1 4.
  setoid_rewrite pars_fold.
  swap_tac 1 2.

  under_new swap_at 0 0 1.
  simpl.
  setoid_rewrite pars_fold.
  symmetry.

  rewrite /OT_trapdoor_HCBitPairSim.
  swap_tac 0 5.
  setoid_rewrite par_in_pars.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 3.
  under_new swap_at 0 0 6.
  simpl.
  swap_tac 1 8.
  setoid_rewrite pars_fold.
  under_new swap_at 0 0 6.
  simpl.
  swap_tac 1 6.
  setoid_rewrite pars_fold.
  apply EqCongNew; intro.
  apply EqCongNew; intro.
  apply EqCongNew; intro.
  apply pars_cons_cong.
  apply EqCongReact.
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
  apply uniform_boolP.
  apply addbI.
  apply EqBind_r; intros.
  rewrite EqBind_r_samp_bijection.
  apply EqBind_r; intro.
  reflexivity.
  apply uniform_boolP.
  apply addbI.
  align.
  swap_tac 0 6.
  rewrite pars_prot0.
  align.

  reflexivity.
Qed.


  Lemma OT_Trapdoor_Security e : 
  (forall c1 c2 c3, 
    @HCBitReal chan c1 c2 c3 =a_(e) HCBitIdeal c1 c2 c3) ->
    OT_trapdoor =a_(comp_err (e +e comp_err e 3) 5) (leakO <- new bool ;; pars [:: OTIdeal _ i m o; OT_trapdoor_OTSim leakO; OTIdeal _ i m leakO] ).
    intro.
    rewrite OT_trapdoor_simpE.
    rewrite /OT_trapdoor_simp.
    symmetry.
    rewrite new_pars_pull.
    eapply AEq_err_eq; last first.
    rewrite /OTIdeal.
    apply AEq_comp_r.
    apply _.
    setoid_rewrite pars2.
    rewrite OT_trapdoor_simp_rE.
    rewrite -OT_trapdoor_OTSimE.
    symmetry.
    apply withHCBitPairRealP.
    apply _.
    intros; apply H.
    rewrite comp_err_comp.
    done.
   Qed.

  Require Import Permutation Typ Lib.SeqOps.

  Lemma OT_trapdoor_t :
    ipdl_t [:: tag o; tag leaky0; tag leaky1; tag leakEK; tag leakd01] OT_trapdoor.
    rewrite /OT_trapdoor /TD_Snd /TD_Rcv.
    repeat type_tac.
    symmetry.
    perm_match_step.
    perm_match.
  Qed.

  Lemma OT_trapdoor_OTSim_t c :
    ipdl_t [:: tag leaky0; tag leaky1; tag leakEK; tag leakd01] (OT_trapdoor_OTSim c).
    rewrite /OT_trapdoor_OTSim.
    rewrite /withHCBitPairIdeal.
    rewrite /HCBitPairIdeal.
    repeat type_tac.
    perm_match.
  Qed.
  End TrapdoorOT.

End TrapdoorOT.

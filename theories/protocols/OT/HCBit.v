
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Lib.Base Lib.SeqOps Pars.

Module Type HCParams.
  Parameters (D ek tk: nat)
             (evalKey : tk -> ek)
             (sampK : Dist tk)
             (eval : ek -> D -> D)
             (evalInv : tk -> D -> D) 
             (eval_cancel : forall tk, cancel (eval (evalKey tk)) (evalInv tk))
             (B : D -> bool).
End HCParams.

Module HCBit (P : HCParams).
  Export P.
  
  Definition HCBitReal (c_ek : chan ek) (y : chan D) (b : chan TBool) :=
    New tk (fun c_tk =>
           New D (fun w =>
                pars [::
                         Out c_tk (Samp sampK);
                         Out c_ek (x <-- Read c_tk ;; Ret (evalKey x));
                         Out w (Unif D);
                     Out y (e <-- Read c_ek ;; w <-- Read w ;; Ret (eval e w));
                     Out b (x <-- Read w ;; Ret (B x : TBool)) ] ) ).
                     
  Definition HCBitIdeal (c_ek : chan ek) (y : chan D) (b : chan TBool) :=   
              pars [::
                    Out c_ek (x <-- Samp sampK;; Ret (evalKey x));
                    Out y (Unif D);
                    Out b (Unif TBool)
                        ].
     
  Definition HCBitPairReal (c_ek : chan ek) (y1 y2 : chan D) (b1 b2 : chan TBool) :=
    New tk (fun c_tk =>
           New D (fun w1 =>
              New D (fun w2 =>
                pars [::
                         Out c_tk (Samp sampK);
                         Out c_ek (x <-- Read c_tk ;; Ret (evalKey x));
                         Out w1 (Unif D);
                         Out w2 (Unif D);
                         Out y1 (e <-- Read c_ek ;; w <-- Read w1 ;; Ret (eval e w));
                         Out y2 (e <-- Read c_ek ;; w <-- Read w2 ;; Ret (eval e w));
                         Out b1 (x <-- Read w1 ;; Ret (B x : TBool));
                         Out b2 (x <-- Read w2 ;; Ret (B x : TBool))
           ] ) ) ).

  Definition HCBitPairIdeal (c_ek : chan ek) (y1 y2 : chan D) (b1 b2 : chan TBool) :=
              pars [::
                         Out c_ek (x <-- Samp sampK ;; Ret (evalKey x));
                         Out y1 (Unif D);
                         Out y2 (Unif D);
                         Out b1 (Unif TBool);
                         Out b2 (Unif TBool) ].

  Lemma HCBitPair_security c_ek :
    (forall y b, EqProt (HCBitReal c_ek y b) (HCBitIdeal c_ek y b)) ->
    forall y1 y2 b1 b2,
      EqProt (HCBitPairReal c_ek y1 y2 b1 b2) (HCBitPairIdeal c_ek y1 y2 b1 b2).
    intros.
    rewrite /HCBitPairReal.
    swap_tac 0 3.
    swap_tac 1 5.
    swap_tac 2 7.
    split_tac 3.
    setoid_rewrite <- NewComp.
    setoid_rewrite <- NewComp_r.
    setoid_rewrite <- NewComp_r.
    etransitivity.
    apply EqCong.
    done.
    swap_tac 1 2.
    swap_tac 2 4.
    swap_tac 3 4.
    rewrite /HCBitReal in H.
    rewrite (H y1 b1).
    done.
    rewrite /HCBitIdeal.
    rewrite NewComp.
    setoid_rewrite <- pars_cat; simpl.
    swap_tac 0 3.
    setoid_rewrite <- pars_fold.
    rewrite NewNew.
    rewrite /HCBitReal in H.
    swap_tac 0 1.
    swap_tac 2 4.
    swap_tac 3 4.
    setoid_rewrite (pars_split 5); simpl.
    setoid_rewrite <- NewComp.
    setoid_rewrite <- NewComp.
    rewrite (H y2 b2).
    rewrite /HCBitIdeal.
    rewrite -pars_cat; simpl.
    rewrite -pars_fold.
    symmetry; rewrite NewComp.
    apply EqNew; intros.
    rewrite -pars_cat //=.
    repeat align_step.
Qed.

  Definition withHCBitPairReal (f : chan ek -> chan D -> chan D -> chan TBool -> chan TBool -> rset) :=
    New ek (fun c1 =>
              New D (fun y1 =>
                New D (fun y2 =>
                  New TBool (fun b1 =>
                    New TBool (fun b2 =>
                             pars [::
                                     HCBitPairReal c1 y1 y2 b1 b2;
                                     f c1 y1 y2 b1 b2] ) ) ) ) ).

  Definition withHCBitPairIdeal (f : chan ek -> chan D -> chan D -> chan TBool -> chan TBool -> rset) :=
    New ek (fun c1 =>
              New D (fun y1 =>
                New D (fun y2 =>
                  New TBool (fun b1 =>
                    New TBool (fun b2 =>
                             pars [::
                                     HCBitPairIdeal c1 y1 y2 b1 b2;
                                     f c1 y1 y2 b1 b2] ) ) ) ) ).

  Lemma withHCBitPairRealP f :
    (forall c_ek y b, EqProt (HCBitReal c_ek y b) (HCBitIdeal c_ek y b)) ->
    withHCBitPairReal f ~= withHCBitPairIdeal f.
    intros.
    repeat ltac:(apply EqNew; intros).
    rewrite pars_cons.
    rewrite HCBitPair_security.
    rewrite -pars_cons.
    done.
    done.
  Qed.


End HCBit.

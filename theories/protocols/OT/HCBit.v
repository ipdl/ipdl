(* The following development formalizes hard-core bits for a trapdoor permutation. This is used in the TrapdoorOT proof. *) 

Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Lib.Base Lib.SeqOps Pars Ipdl.Approx.

Require Import Typ Lib.SeqOps.
Module Type HCBit.

  (* We assume the trapdoor permutation is given by:
   - a length, D, of its domain;
   - a length, ek, for its evaluation keys; 
   - a length, tk, for its trapdoor keys;
   - along with appropriate algorithms for sampling the trapdoor key, creating evaluation keys out of trapdoor keys, and evaluating the trapdoor permutation. *)
  
  Parameters (D ek tk: nat)
             (evalKey : tk.-bv -> ek.-bv)
             (sampK : Dist tk.-bv)
             (eval : ek.-bv -> D.-bv -> D.-bv)
             (evalInv : tk.-bv -> D.-bv -> D.-bv) 
             (eval_cancel : forall tk, cancel (eval (evalKey tk)) (evalInv tk))
             (B : D.-bv -> bool).

  (* The real experiment for HCBit returns the tuple 
    (ek, y, b), 
  where ek is the evaluation key,
  y is an evaluation under ek of a random element, w; and 
  b is the hard-core predicate for w. *)
  Definition HCBitReal {chan} (c_ek : chan ek.-bv) (y : chan D.-bv) (b : chan bool) :=
    c_tk <- new tk.-bv ;;
    w <- new D.-bv ;;
    pars [::
                c_tk ::= (Samp sampK);
                c_ek ::= (x <-- Read c_tk ;; Ret (evalKey x));
                w ::= (Samp (Unif ));
                y ::= (e <-- Read c_ek ;; w <-- Read w ;; Ret (eval e w));
                b ::= (x <-- Read w ;; Ret (B x : bool)) ].
                     
  (* The 'ideal' experiment is the same shape of tuple, but uniformly random. *)
  Definition HCBitIdeal {chan} (c_ek : chan ek.-bv) (y : chan D.-bv) (b : chan bool) :=   
              pars [::
                    c_ek ::= (x <-- Samp sampK;; Ret (evalKey x));
                    y ::= (Samp (Unif ));
                    b ::= (Samp (Unif ))
                        ].

  Parameter (lambda : nat).
  Parameter HCBitSecurity : 
    (forall {chan : Type -> Type} (c_ek : chan ek.-bv) y b, (HCBitReal c_ek y b) =a_(lambda, err1) (HCBitIdeal c_ek y b)).

End HCBit.

Module HCBitPair (Export P : HCBit).
  

  (* HC Bit pair security:
   we prove that if the above two protocols are approximately equivalent, then the distribution
   (ek, y1, y2, b1, b2) is approximately equivalent to uniform. *)

  Definition HCBitPairReal {chan} (c_ek : chan ek.-bv) (y1 y2 : chan D.-bv) (b1 b2 : chan bool) :=
    c_tk <- new tk.-bv ;;
    w1 <- new D.-bv ;;
    w2 <- new D.-bv ;;
    pars [::
                c_tk ::= (Samp sampK);
                c_ek ::= (x <-- Read c_tk ;; Ret (evalKey x));
                w1 ::= (Samp (Unif ));
                w2 ::= (Samp Unif );
                y1 ::= (e <-- Read c_ek ;; w <-- Read w1 ;; Ret (eval e w));
                y2 ::= (e <-- Read c_ek ;; w <-- Read w2 ;; Ret (eval e w));
                b1 ::= (x <-- Read w1 ;; Ret (B x));
                b2 ::= (x <-- Read w2 ;; Ret (B x))
           ] .

  Definition HCBitPairIdeal {chan} (c_ek : chan ek.-bv) (y1 y2 : chan D.-bv) (b1 b2 : chan bool) :=
              pars [::
                         c_ek ::= (x <-- Samp sampK ;; Ret (evalKey x));
                         y1 ::= (Samp Unif );
                         y2 ::= (Samp Unif );
                         b1 ::= (Samp Unif);
                         b2 ::= (Samp Unif) ].


  Lemma HCBitPair_security {chan} c_ek :
    forall y1 y2 b1 b2,
      (@HCBitPairReal chan c_ek y1 y2 b1 b2) =a_(lambda, err1 +e (comp_err err1 3)) (HCBitPairIdeal c_ek y1 y2 b1 b2).
    intros.
    rewrite /HCBitPairReal.
    swap_tac 3 4.
    swap_tac 4 6.
    setoid_rewrite (pars_split 5); simpl.
    setoid_rewrite <- newComp_r.
    setoid_rewrite <- newComp.
    setoid_rewrite <- newComp.
    arewrite (HCBitSecurity c_ek y1 b1).
    rewrite /HCBitIdeal.
    rewrite newComp_r.
    setoid_rewrite <- pars_cat; simpl.
    setoid_rewrite <- pars_fold.
    rewrite EqNewExch.
    swap_tac 0 1.
    swap_tac 2 5. 
    swap_tac 3 4.
    swap_tac 4 6.
    setoid_rewrite (pars_split 5); simpl.
    setoid_rewrite <- newComp.
    setoid_rewrite <- newComp.
    arewrite (HCBitSecurity c_ek y2 b2).
    rewrite /HCBitIdeal.
    rewrite pars_pars; simpl.
    symmetry.
    setoid_rewrite pars_fold.
    rewrite <- pars_cat; simpl.
    apply AEq_zero.
    align.
    done.
    rewrite add_err0.
    rewrite /comp_err /add_err //=.
    apply _.
  Qed.

  Definition withHCBitPairReal {chan} (f : chan ek.-bv -> chan D.-bv -> chan D.-bv -> chan bool -> chan bool -> ipdl) :=
    c1 <- new ek.-bv ;;
    y1 <- new D.-bv ;;
    y2 <- new D.-bv ;;
    b1 <- new bool ;;
    b2 <- new bool ;;
    pars [::
            HCBitPairReal c1 y1 y2 b1 b2;
            f c1 y1 y2 b1 b2] .

  Definition withHCBitPairIdeal {chan} (f : chan ek.-bv -> chan D.-bv -> chan D.-bv -> chan bool -> chan bool -> ipdl) :=
    c1 <- new ek.-bv ;;
    y1 <- new D.-bv ;;
    y2 <- new D.-bv ;;
    b1 <- new bool ;;
    b2 <- new bool ;;
    pars [::
            HCBitPairIdeal c1 y1 y2 b1 b2;
            f c1 y1 y2 b1 b2]. 



  Lemma withHCBitPairRealP {chan} f bnd `{forall c1 y1 y2 b1 b2, IPDLBnd (f c1 y1 y2 b1 b2) bnd} :
    withHCBitPairReal f =a_(lambda, comp_err (err1 +e comp_err err1 3) bnd) @withHCBitPairIdeal chan f.
    intros.
    apply AEq_new; intros.
    apply AEq_new; intros.
    apply AEq_new; intros.
    apply AEq_new; intros.
    apply AEq_new; intros.
    eapply AEq_tr. 
    arewrite (HCBitPair_security c c0 c1 c2 c3).
    done.
    rewrite add_err0 addn0.
    done.
    reflexivity.
    rewrite add_err0 //=.
  Qed.

  Lemma HCBitReal_t {chan} c y b :
    @ipdl_t chan [:: tag c; tag y; tag b] (HCBitReal c y b).
    rewrite /HCBitReal; repeat type_tac.
    perm_match.
  Qed.

End HCBitPair.

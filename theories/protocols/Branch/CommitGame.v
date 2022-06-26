Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.

Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Ipdl.Approx Encodable.  
Open Scope bool_scope.
Section AuthExample.
  Context (K D R : nat) (gen : Dist (K.-bv)) (H : K.-bv -> D.-bv -> R.-bv).

  Definition HashReal (i1 i2 : chan D.-bv) (k : chan (K.-bv)) (o : chan bool) :=
    pars [::
            k ::= Samp gen; 
            o ::=
            (k <-- Read k;;
             x <-- Read i1;;
             y <-- Read i2 ;; Ret (H k x == H k y))].

  Definition HashIdeal (i1 i2 : chan D.-bv) (k : chan (K.-bv)) (o : chan bool) :=
    pars [::
            k ::= Samp gen; 
            o ::=
            (_ <-- Read k ;; x <-- Read i1 ;; y <-- Read i2 ;; Ret (x == y))].

  Definition protocol (key : chan K.-bv) (xA xB : chan D.-bv) (ok : chan unit) :=
    diverge <- new unit;;
    b2a <- new R.-bv;;
    pars [::
            diverge ::= Read diverge;
            key ::= Samp gen;
            b2a ::= (k <-- Read key;; x <-- Read xB ;; Ret (H k x)); 
            ok ::= (k <-- Read key;; x <-- Read xA ;; v <-- Read b2a ;; if (H k x == v) then Ret tt else Read diverge)].

  Definition protocol_ideal (key : chan K.-bv) (xA xB : chan D.-bv) (ok : chan unit) :=
    diverge <- new unit;;
    pars [::
            diverge ::= Read diverge;
            key ::= Samp gen;
            ok ::= (x <-- Read xA ;; y <-- Read xB ;; if x == y then Ret tt else Read diverge) ].

  Lemma protocol_hybrid k xA xB ok :
    protocol k xA xB ok =p 
                           (
                            diverge <- new unit ;;
                            b <- new bool ;;
                            pars [::
                                    diverge ::= Read diverge;
                                    HashReal xA xB k b;
                                    ok ::= (x <-- Read b ;; if x then Ret tt else Read diverge)]).
    rewrite /protocol.
    Intro => diverge.
    swap_tac 0 3.
    swap_tac 1 2.
    under_new swap_at 0 0 2; simpl.
    simpl.
    rewrite pars_fold.
    symmetry.
    rewrite /HashReal.
    swap_tac 0 1.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 3.
    rewrite pars_fold.
    align.
    apply EqCongReact.
    simp_rxn.
    symmetry; simp_rxn.
    r_swap 1 2.
    rewrite EqReadSame.
    r_swap 1 2.
    done.
 Qed.

  Definition protocol_err e ok :=
  ENew
    (fun diverge : chan unit =>
     ENew
       (fun b : chan bool =>
        EComp (e b) [|| ok ::= (x <-- Read b;; (if x then Ret tt else Read diverge));diverge ::= Read diverge])).

  Lemma protocol_secure k xA xB ok e :
    (forall xA xB k b, HashReal xA xB k b =a_(e xA xB k b) HashIdeal xA xB k b) ->
    protocol k xA xB ok =a_(protocol_err (e xA xB k) ok) protocol_ideal k xA xB ok.
    intros.
    etrans.
    apply protocol_hybrid.
    atrans.
    Intro => diverge.
    Intro => b.
    arewrite (H0 xA xB k b).
    apply AEq_zero; apply EqRefl.
    apply EqERefl.
    simpl.
    apply AEq_zero.
    rewrite /protocol_ideal.
    Intro => diverge.
    rewrite /HashIdeal.
    swap_tac 0 1.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 3.
    rewrite pars_fold.
    simp_at 0.
    swap_tac 1 2.
    rewrite -pars_mkdep //=.
    align.
    rewrite adde0.
    setoid_rewrite adde0.
    setoid_rewrite EqCompComp.
    setoid_rewrite pars_rcons; simpl.
    done.
  Qed.

Lemma encodable_prot k xa xb ok : EncodableIPDL (protocol k xa xb ok).
  rewrite /protocol.
  apply _.
Qed.

Require Import Typ Lib.SeqOps.

Lemma protocol_t k xA xB ok :
  ipdl_t [:: mkChan k; mkChan ok] (protocol k xA xB ok).
  rewrite /protocol; repeat type_tac.
  perm_match.
Qed.

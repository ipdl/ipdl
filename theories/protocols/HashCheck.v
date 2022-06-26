Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.

Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Ipdl.Approx Ipdl.Encodable.  
Open Scope bool_scope.
Section AuthExample.
  Context (K D R : nat) (gen : Dist (K.-bv)) (H : K.-bv -> D.-bv -> R.-bv).


  (* Definition of collision resistance *)

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


  (* In the real protocol: 
     1. key service generates a key; delivers it to alice, bob, and the adv
     2. adv gives a value xA to alice, xB to bob
     3. bob sends alice the value b2a = H(xB)
     4. alice outputs ok only if H(x) == v; otherwise, she diverges *)

  Definition protocol (key : chan K.-bv) (xA xB : chan D.-bv) (ok : chan unit) :=
    diverge <- new unit;;
    b2a <- new R.-bv;;
    pars [::
            diverge ::= Read diverge;
            (* Key service that alice and bob can read from *)
            key ::= Samp gen;
            (* message from bob to alice *)
            b2a ::= (k <-- Read key;; x <-- Read xB ;; Ret (H k x)); 
            (* ok message comes from alice *)
            ok ::= (k <-- Read key;; x <-- Read xA ;; v <-- Read b2a ;; if (H k x == v) then Ret tt else Read diverge)].

  (*
     In the ideal protocol:
     1. adv gives values xA, xB
     2. output ok only if xA == xB; otherwise, diverge *)
  Definition protocol_ideal (xA xB : chan D.-bv) (ok : chan unit) :=
    diverge <- new unit;;
    pars [::
            diverge ::= Read diverge;
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
        EComp e [|| ok ::= (x <-- Read b;; (if x then Ret tt else Read diverge));diverge ::= Read diverge])).


  (* We prove that this hashing protocol is equivalent to its idealization, along with a simulator that randomly generates a key. *)
  Lemma protocol_secure k xA xB ok e :
    (forall xA xB k b, HashReal xA xB k b =a_(e) HashIdeal xA xB k b) ->
    protocol k xA xB ok =a_(protocol_err e ok) pars [::
                                                       k ::= Samp gen;
                                                       protocol_ideal xA xB ok].
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
    symmetry; swap_tac 0 1.
    rewrite newPars.
    setoid_rewrite pars_pars; simpl.
    symmetry.
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


    

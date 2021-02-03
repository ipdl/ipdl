
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Typing Lib.Set.  
Require Import CPA.


Definition Net (q n : nat) {l : nat} (leakage : n -> l)
           (I O : q.-tuple (chan n)) (leak : q.-tuple (chan l)) (ok : q.-tuple (chan TUnit)) :=
  [||
       \||_(j < q) (leak ## j) ::= (x <-- Read (I ## j) ;; Ret (leakage x));
       \||_(j < q) (O ## j) ::= (_ <-- Read (ok ## j) ;; x <-- Read (I ## j) ;; Ret x)].

Definition Auth q n := Net q n id.
Definition Sec q n := Net q n (fun _ => [tuple]).
             
Definition FKey {k : nat} (genK : Dist k) (o : chan k) :=
  Out o (Samp genK).

Section MultiChan.
  Context (msg ctxt key : nat).
  Context (genK : Dist key).
  Context (enc : msg -> key -> Dist ctxt).
  Context (dec : ctxt -> key -> msg).
  Context (q : nat).

  Context (Hdec : dec_correct genK enc dec).
  Context (Henc : CPA_Secure q genK enc).

  Definition alice (i : q.-tuple (chan msg)) (k : chan key) (send : q.-tuple (chan ctxt)) :=
    Outvec send (fun j =>
                   m <-- Read (tnth i j) ;; k <-- Read k ;; c <-- Samp (enc m k) ;; Ret c).

  Definition bob (recv : q.-tuple (chan ctxt)) (k : chan key) (o : q.-tuple (chan msg)) :=
    Outvec o (fun j => 
             c <-- Read (tnth recv j) ;; k <-- Read k ;; Ret (dec c k)).

  Definition real (i o : q.-tuple (chan msg)) (leak : q.-tuple (chan ctxt))
             (ok : q.-tuple (chan TUnit)) :=
    k <- new key ;;
    send <- newvec q @ ctxt ;;
    recv <- newvec q @ ctxt ;;
    pars [::
            FKey genK k ;
            alice i k send ;
            Auth q ctxt send recv leak ok;
            bob recv k o].

  Definition ideal (i o : q.-tuple (chan msg)) (leak : q.-tuple (chan 0)) (ok : q.-tuple (chan TUnit)) :=
    Sec q msg i o leak ok.

  Definition Sim (leakI : q.-tuple (chan 0)) (okI : q.-tuple (chan TUnit)) (leakR : q.-tuple (chan ctxt)) (okR : q.-tuple (chan TUnit)) :=
    k <- new key ;;
    pars [::
            Out k (Samp genK) ;
            Outvec leakR (fun j =>
                            _ <-- Read (tnth leakI j) ;; k <-- Read k ;; e <-- Samp (enc [tuple of nseq _ false] k) ;; Ret e);
            Outvec okI (fun j => x <-- Read (tnth okR j) ;; Ret x) ].

  Theorem MultiChan_Security i o leakR okR :
    real i o leakR okR =0 (leakI <- newvec q @ 0 ;; okI <- newvec q @ TUnit ;; pars [:: ideal i o leakI okI; Sim leakI okI leakR okR]).
    symmetry.

    (* First, eliminate ideal chans *)
    rewrite /ideal /Sec /Chan /Sim //=.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 2.
    setoid_rewrite newPars; last by apply _.
    setoid_rewrite pars_pars; simpl.
    setoid_rewrite (New_newvec).
    swap_tac 0 3.
    swap_tac 1 2.
    under_new rewrite pars_big_fold; apply EqRefl.
    simpl.
    rewrite New_newvec.
    swap_tac 0 1.
    swap_tac 1 3.
    under_new rewrite pars_big_fold; apply EqRefl.
    etransitivity.
    apply EqNew => k _ _.
    simp_all.
    apply EqRefl.


    (* Now rewrite using dec_correct *)
    symmetry.
    rewrite /real.
    etransitivity.

    apply EqNew => k _ _.
    rewrite /FKey /alice /Auth /bob /Chan.
    swap_tac 0 2.
    setoid_rewrite pars_pars at 1; simpl.
    swap_tac 0 4.
    
    under_new rewrite pars_big_fold; apply EqRefl; simpl.

    simpl.
    apply EqNew_vec => send _ _.
    simp_all.

    focus_tac 0.
    apply Eq_Outvec; intro.
    instantiate (1 := fun j =>
                   z <-- (x0 <-- Read (tnth send j) ;; x1 <-- Read k ;; Ret (dec x0 x1)) ;; _ <-- Read (tnth okR j) ;; Ret z).
    symmetry; simp_rxn.
    r_swap 0 2; done.
    
    rewrite -pars_big_fold.
    etransitivity.
    apply EqNew_vec => decchan _ _.
    swap_tac 0 3.
    swap_tac 1 2.

    rewrite (pars_split 3); simpl.
    swap_Outvec_at 1 0 1.
    rewrite Multi_dec_correct //=.
    rewrite -pars_cat //=.
    apply EqRefl.
    simpl.
    swap_tac 0 3.
    swap_tac 1 2.
    rewrite pars_big_fold.
    apply EqRefl.

    etransitivity.
    apply EqNew => k _ _.
    swap_tac 0 3.
    rewrite pars_big_fold.
    simp_all.
    apply EqRefl.
    swap_tac 0 2.
    symmetry; swap_tac 0 2; symmetry.
    setoid_rewrite pars_cons.
    rewrite -newComp_r.
    rewrite -newComp_r.
    apply EqCong.
    apply EqProt_big_r; intros; apply EqOut; r_swap 0 1; done.
    have h := (Henc i leakR).
    rewrite /CPA0 in h.
    etransitivity.
    apply EqNew => k _ _.
    swap_Outvec_at 1 0 1.
    apply EqRefl.
    rewrite h.
    done.
 Qed.

  End MultiChan.

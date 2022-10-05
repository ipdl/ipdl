(* Case study of IND-CPA symmetric encryption + an authenticated channel realizes a secure channel. 

   We assume a functionality, FKey, that securely broadcasts a key k to alice and bob.
   Alice wishes to communicate q messages to bob using an authenticated channel. 
   The authenticated channel leaks each value to the adversary, and waits for an 'ok' message before delivering the in-flight 
message.  
   To do so securely, alice sends encryptions of her messages, which bob may decrypt using the shared key, k. *)


Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Ipdl.Big Pars Lib.Set Lib.Dist Ipdl.Approx.  
Require Import CPA.


(* The definition of authenticated / secure network is 
 given by the below definition, which is parameterized by a leakage function.
  When the network gets the i'th input, it forwards this value to the adversary using the leakage function. In an authenticated channel, the leakage is full; in a secure channel, the leakage simply is the empty bitstring, given by [tuple]. 

  The j'th value is delivered to bob only when the adversary inputs (ok ## j).
*)


Definition Net {chan} (q n : nat) {l : nat} (leakage : n.-bv -> l.-bv)
           (I O : q.-tuple (chan n.-bv)) (leak : q.-tuple (chan l.-bv)) (ok : q.-tuple (chan unit)) :=
  [||
       \||_(j < q) (leak ## j) ::= (x <-- Read (I ## j) ;; Ret (leakage x));
       \||_(j < q) (O ## j) ::= (_ <-- Read (ok ## j) ;; x <-- Read (I ## j) ;; Ret x)].

Definition Auth {chan} q n := @Net chan q n _ id.
Definition Sec {chan} q n := @Net chan q n _ (fun _ => [tuple]).
             
Definition FKey {chan} {k : nat} (genK : Dist k.-bv) (o : chan k.-bv) :=
  (o ::= (Samp genK)).

Module MultiChan (Import P : CPA).


  (* Alice's output channels are  'send ## j', which connects to the authenticated channel. Alice takes as input the channels 'i ## j', which come from the environment. *)
  Context (chan : Type -> Type).

  Definition alice (i : q.-tuple (chan msg.-bv)) (k : chan key.-bv) (send : q.-tuple (chan ctxt.-bv)) :=
    \||_(j < q) (send ## j) ::= (
                   m <-- Read (i ## j) ;; k <-- Read k ;; c <-- Samp (enc m k) ;; Ret c).

  Definition bob (recv : q.-tuple (chan ctxt.-bv)) (k : chan key.-bv) (o : q.-tuple (chan msg.-bv)) :=
    \||_(j < q) (o ## j) ::= (
             c <-- Read (recv ## j) ;; k <-- Read k ;; Ret (dec c k)).

  (* The real protocol . *)
  Definition real (i o : q.-tuple (chan msg.-bv)) (leak : q.-tuple (chan ctxt.-bv))
             (ok : q.-tuple (chan unit)) :=
    k <- new key.-bv ;;
    send <- newvec q @ ctxt.-bv ;;
    recv <- newvec q @ ctxt.-bv ;;
    pars [::
            FKey genK k ;
            alice i k send ;
            Auth q ctxt send recv leak ok;
            bob recv k o].

  (* The ideal protocol is simply the secure channel. *)
  Definition ideal (i o : q.-tuple (chan msg.-bv)) (leak : q.-tuple (chan 0.-bv)) (ok : q.-tuple (chan unit)) :=
    Sec q msg i o leak ok.

  (* The simulator receives as input the channels (leakI ## j) and (okR ## j), and must output on the channels (leakR ## j) and (okI ## j). 
     It does so by generating the encryption key itself, and generating fake ciphertexts of the all-0's bitstring. By IND-CPA, these ciphertexts look like the real ones. *)
 
     
  Definition Sim (leakI : q.-tuple (chan 0.-bv)) (okI : q.-tuple (chan unit)) (leakR : q.-tuple (chan ctxt.-bv)) (okR : q.-tuple (chan unit)) :=
    k <- new key.-bv ;;
    pars [::
            k ::= (Samp genK) ;
            \||_(j < q) (leakR ## j) ::= (
                            _ <-- Read (tnth leakI j) ;; k <-- Read k ;; e <-- Samp (enc [tuple of nseq _ false] k) ;; Ret e);
            \||_(j < q) (okI ## j) ::= (x <-- Read (tnth okR j) ;; Ret x) ].


  (* We prove that the real protocol is approximately equivalent to the idel protocol connected to the simulator. *)
  Theorem MultiChan_Security i o leakR okR :
    real i o leakR okR =a_(lambda, comp_err err1 q)
 (leakI <- newvec q @ 0.-bv ;; okI <- newvec q @ unit ;; pars [:: ideal i o leakI okI; Sim leakI okI leakR okR]).


    (* First, eliminate ideal chans *)
    rewrite /ideal /Sec /Net /Sim /=.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 2.
    setoid_rewrite newPars; last by apply _.
    setoid_rewrite pars_pars; simpl.
    setoid_rewrite (New_newvec).
    swap_tac 0 3.
    swap_tac 1 2.
    setoid_rewrite pars_big_fold.
    rewrite New_newvec.
    swap_tac 0 1.
    swap_tac 1 3.
    setoid_rewrite pars_big_fold.
    symmetry.
    etrans.
    Intro => k.
    simp_all.
    apply EqRefl.

    (* Now rewrite using dec_correct *)
    symmetry.
    rewrite /real.
    etrans.

    Intro => k.
    rewrite /FKey /alice /Auth /bob /Net.
    swap_tac 0 2.
    setoid_rewrite pars_pars at 1; simpl.
    swap_tac 0 4.
    setoid_rewrite pars_big_fold at 1.
    Intro => send.
    simp_all.

    focus_tac 0.
    apply Eq_Outvec; intro.
    instantiate (1 := fun j =>
                   z <-- (x0 <-- Read (tnth send j) ;; x1 <-- Read k ;; Ret (dec x0 x1)) ;; _ <-- Read (tnth okR j) ;; Ret z).
    symmetry; simp_rxn.
    r_swap 0 2; done.
    rewrite -pars_big_fold.
    Intro => oks.
    swap_tac 0 3.
    swap_tac 1 2.
    swap_tac 3 4.
    rewrite (pars_split 3); simpl.
    swap_Outvec_at 1 0 1.
    rewrite Multi_dec_correct //=.
    rewrite -pars_cat //=.
    apply EqRefl.
    simpl.

    have h := (CPA_security i leakR).
    rewrite /CPA1 in h.
    symmetry.
    etrans.
    swap_tac 0 2.
    rewrite new_pars_pull.
    apply EqRefl.

    arewrite_inv h.
    simpl.
    apply AEq_zero.
    rewrite /CPA0.
    rewrite -new_pars_pull.
    Intro => k.
    symmetry.
    swap_tac 0 4.
    swap_tac 1 2.
    setoid_rewrite pars_big_fold.
    swap_tac 0 2.
    setoid_rewrite pars_big_fold.
    align.
    apply EqProt_big_r => x _ _.
    apply EqCongReact.
    rewrite /copy; simp_rxn.
    r_swap 0 1.
    done.

    apply EqProt_big_r => x _ _.
    apply EqCongReact.
    rewrite /copy; simp_rxn.
    r_swap 0 1.
    done.
    rewrite muln1 add_err0.
    done.
Qed.
  End MultiChan.

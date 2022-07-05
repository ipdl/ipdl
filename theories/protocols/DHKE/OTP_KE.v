
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Ipdl.Approx DHKE.  


(* This example constructs a one-time pad out of a 
key exchange sub-protocol (here, DHKE, from DHKE.v). 

Alice and Bob first perform the DHKE to get a shared secret; then, they use the shared secret to perform a one-time pad. *)


Module OTP_KE (Import P : DHKEParams).
  Module M := KeyExchange(P).
  Import M.

  Section OTP.
    Context {chan : Type -> Type}.

  Definition Alice_otp (key cin cout : chan group) :=
    pars [::
            cout ::= (k <-- Read key ;; i <-- Read cin ;; Ret (gmul k i))].

  Definition Bob_otp (key cin cout : chan group) :=
    pars [::
            cout ::=
            (k <-- Read key ;;
             i <-- Read cin ;;
             Ret (gmul (ginv k) i))].


Definition alice ke_send ke_recv key cin send :=
  pars [::
          DHKE_RealParty ke_send ke_recv key;
          Alice_otp key cin send ].

Definition bob ke_send ke_recv key recv cout :=
  pars [::
          DHKE_RealParty ke_send ke_recv key;
          Bob_otp key recv cout ].


Definition OTPReal (cin leak1 leak2 cout : chan group) ok1 ok2 leak ok :=
  send <- new group ;;
  recv <- new group ;;
  keyA <- new group ;;
  keyB <- new group ;;
  send1 <- new group ;;
  send2 <- new group ;;
  recv1 <- new group ;;
  recv2 <- new group ;;
  pars [::
          alice send1 recv2 keyA cin send;
          bob send2 recv1 keyB recv cout;
          (* Channel 1 for the key exchange *)
          FAuth send1 recv1 leak1 ok1;
          (* Channel 2 for the key exchange *)
          FAuth send2 recv2 leak2 ok2;
          (* Channel for the OTP ciphertext *)
          FAuth send recv leak ok
       ].

  (* In the ideal protocol, the input is copied to the output. The adversary also learns when the input happens (given by the cin_timing channel. *)
  Definition OTPIdeal (cin cout : chan group) (cin_timing : chan unit) (okI : chan unit) :=
    pars [::
            cout ::= (_ <-- Read okI ;; copy cin);
         cin_timing ::= (_ <-- Read cin ;; Ret tt)
                          ].


  (* We first prove that the OTPReal protocol above 
    can be factored into a version which has DHKEReal 
    embedded inside. This essentially just collects 
    the party's code for the subprotocol.
*)

Lemma OTPReal_equiv cin leak1 leak2 cout ok1 ok2 leak ok :
  OTPReal cin leak1 leak2 cout ok1 ok2 leak ok =p
    send <- new group ;;
    recv <- new group ;;
    keyA <- new group ;;
    keyB <- new group ;;
    pars [::
            Alice_otp keyA cin send;
            Bob_otp keyB recv cout;
            FAuth send recv leak ok;
            DHKEReal keyA keyB leak1 leak2 ok1 ok2].
  symmetry.
  swap_tac 0 3.
  rewrite /DHKEReal.
  setoid_rewrite newPars.
  setoid_rewrite newPars.
  setoid_rewrite newPars.
  setoid_rewrite newPars.
  setoid_rewrite pars_pars; simpl.
  rewrite /OTPReal.
  repeat ltac:(Intro; intro).
  rewrite /alice /bob.
  symmetry.
  rewrite pars_pars //=.
  swap_tac 0 2.
  rewrite pars_pars //=.
  align.
  apply _.
  apply _.
  apply _.
  apply _.
Qed.

(* The hybrid protocol uses DHKEIdeal instead of DHKEReal. *)
  Definition OTPReal_hybrid (cin leak cout : chan group) ok okA okB :=
    send <- new group ;;
    recv <- new group ;;
    keyA <- new group ;;
    keyB <- new group ;;
    pars [::
            Alice_otp keyA cin send;
            Bob_otp keyB recv cout;
            FAuth send recv leak ok;
            DHKEIdeal okA okB keyA keyB].
            


  Definition OTPSim (cin_timing : chan unit) (leak : chan group) (okI okR okA okB : chan unit) :=
    pars [::
        okI ::= (_ <-- Read okR;; _ <-- Read okA;; _ <-- Read okB ;; Ret tt);
        leak ::= (_ <-- Read cin_timing ;; _ <-- Read okA;; Samp unif_group )].

Instance inhab_group : Inhabited group := Hgroup.
Instance inhab_sk : Inhabited sk := Hsk.

(* The hybrid protocol using idealized key exchange is secure (rewritable to OTPIdeal with a simulator. *)
  Lemma OTP_hybrid_secure cin leak cout okR okA okB :
    OTPReal_hybrid cin leak cout okR okA okB =p
    (t <- new unit ;; okI <- new unit ;; pars [:: OTPIdeal cin cout t okI; OTPSim t leak okI okR okA okB]).
    
    rewrite /OTPReal_hybrid.
    rewrite /DHKEIdeal.
    swap_tac 0 3.
    setoid_rewrite New_in_pars.
    setoid_rewrite pars_pars; simpl.
    rewrite /Alice_otp /Bob_otp.
    
    (* Simplify, eliminate channels *)
    swap_tac 0 3.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 4.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 6.
    setoid_rewrite pars_pars; simpl.
    etransitivity.
    repeat (apply EqCongNew; intro).
    rewrite /copy.
    do_inline.
    repeat ltac:(do_inline; simp_all).
    apply EqRefl.
    simpl.
    setoid_rewrite EqNewExch at 2.
    setoid_rewrite EqNewExch at 3.
    setoid_rewrite EqNewExch at 4.
    swap_tac 0 1.
    under_new rewrite new_pars_remove. apply EqRefl.
    simpl.
    setoid_rewrite EqNewExch at 1.
    setoid_rewrite EqNewExch at 2.
    setoid_rewrite EqNewExch at 3.
    under_new rewrite new_pars_remove. apply EqRefl.
    simpl.
    etransitivity.
    repeat (apply EqCongNew; intro).
    repeat ltac:(do_inline; simp_all).
    apply EqRefl.
    simpl.
    setoid_rewrite EqNewExch at 2.
    swap_tac 0 1.
    under_new rewrite new_pars_remove. apply EqRefl.
    simpl.
    rewrite EqNewExch.
    under_new rewrite new_pars_remove. apply EqRefl.
    simpl.

    (* reason about output *)
    etransitivity.
    apply EqCongNew => key.
    edit_tac 1.
    r_swap 0 1.
    r_swap 1 3.
    rewrite EqReadSame.
    apply EqBind_r => k.
    apply EqBind_r => okb.
    apply EqBind_r => oka.
    apply EqBind_r => i.
    apply EqBind_r => okr.
    rewrite -gmulA.
    rewrite (gmulC _ (gexp ggen k)).
    rewrite gmulK gmulC gmul1.
    apply EqRxnRefl.
    swap_tac 0 1.
    swap_tac 1 3.
    rewrite -pars_mkdep //=.
    swap_tac 0 2.
    simp_at 0.
    swap_at 0 0 1.
    apply EqRefl.
    simpl.
    rewrite pars_fold.

    (* now simplify ideal world *)
    symmetry.
    rewrite /OTPSim.
    swap_tac 0 2.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 1.
    swap_tac 0 3.
    setoid_rewrite pars_fold.
    swap_tac 0 2.
    rewrite pars_fold.
    align.
    apply EqCongReact.
    simp_rxn.
    have h : forall x1, @Samp chan _ unif_group =r (x <-- Samp unif_group;; Ret (gmul x x1)).
    intro.
    apply EqSampBijection.
    apply gmul_inj.
    apply Hunif.
    symmetry; r_swap 0 2.
    apply EqBind_r; intro m.
    setoid_rewrite (h m).
    r_swap 0 1.
    apply EqBind_r => _.
    rewrite /unif_group.
    setoid_rewrite EqSampBind.
    symmetry.
    simp_rxn.
    apply EqBind_r => x.
    setoid_rewrite EqSampRet.
    simp_rxn.
    done.


    apply EqCongReact.
    simp_rxn.
    r_swap 0 2.
    apply EqBind_r => _.
    r_swap 0 1.
    apply EqBind_r => _.
    rewrite /copy.
    r_swap 0 1.
    done.
Qed.

  (* The error term shows that the error for the construction 
     is a simple reduction over the error term for DHKE. *)
 

(* We can replace the real DHKE protocol with the ideal one. *)
Lemma OTPReal_equiv2 cin leak1 leak2 cout ok1 ok2 leak ok e :
  (forall ddh_samp, @DDH0 chan ddh_samp =a_(e) DDH1 ddh_samp) ->
    (send <- new group ;;
    recv <- new group ;;
    keyA <- new group ;;
    keyB <- new group ;;
    pars [::
            Alice_otp keyA cin send;
            Bob_otp keyB recv cout;
            FAuth send recv leak ok;
         DHKEReal keyA keyB leak1 leak2 ok1 ok2]) =a_(comp_err e 8)
    (okA <- new unit ;; okB <- new unit ;;
     pars [::
             DHKESim ok1 ok2 okA okB leak1 leak2;
             OTPReal_hybrid cin leak cout ok okA okB]).
  intro.
  atrans.
  Intro => send.
  Intro => recv.
  Intro => keyA.
  Intro => keyB.
  arewrite (DHKE_security keyA keyB leak1 leak2 ok1 ok2 e H).
  apply AEq_zero.
  apply EqRefl.
  done.
  simpl.
  apply AEq_zero.
  rewrite /DHKESimIdeal.
  swap_tac 0 3.
  setoid_rewrite newPars.
  setoid_rewrite newPars.
  setoid_rewrite pars_pars; simpl.
  symmetry.
  rewrite /OTPReal_hybrid.
  swap_tac 0 4.
  setoid_rewrite newPars.
  setoid_rewrite newPars.
  setoid_rewrite newPars.
  setoid_rewrite newPars.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 3.
  rewrite /DHKEIdeal.
  setoid_rewrite newPars.
  setoid_rewrite pars_pars; simpl.
  symmetry.
  rotate_news; simpl.
  rotate_news; simpl.
  rotate_news; simpl.
  rotate_news; simpl.
  Intro => x.
  Intro => x0.
  symmetry.
  rotate_news; simpl.
  rotate_news; simpl.
  rotate_news; simpl.
  rotate_news; simpl.
  Intro => k.
  Intro; intro.
  Intro; intro.
  Intro; intro.
  Intro; intro.
  symmetry.
  rewrite /DHKESim.
  swap_tac 0 3.
  rewrite pars_pars; simpl.
  align.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
  apply _.
  rewrite add_err0 !comp_err_comp add_err0.
  done.
Qed.

(* Finally, we show that the OTPReal protocol realizes OTPIdeal, with the simulators for DHKE (DHKESim) and OTP (OTPSim). *)
Lemma OTP_security cin leak1 leak2 cout ok1 ok2 leak ok e :
  (forall ddh_samp, @DDH0 chan ddh_samp =a_(e) DDH1 ddh_samp) ->
  OTPReal cin leak1 leak2 cout ok1 ok2 leak ok =a_(comp_err e 8) (
    (okA <- new unit ;; okB <- new unit ;;
     t <- new unit ;; okI <- new unit ;;
     pars [:: DHKESim ok1 ok2 okA okB leak1 leak2; OTPIdeal cin cout t okI; OTPSim t leak okI ok okA okB])).
  intros.
  rewrite OTPReal_equiv.
  atrans.
  apply OTPReal_equiv2.
  apply H.
  apply AEq_zero.
  setoid_rewrite OTP_hybrid_secure.
  swap_tac 0 1.
  Intro => okA.
  Intro => okB.
  rewrite newPars.
  Intro => c.
  rewrite newPars.
  Intro => okI.
  rewrite pars_pars //=.
  align.
  rewrite add_err0 //=.
Qed.

End OTP.
End OTP_KE.

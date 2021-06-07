
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Lib.SeqOps Permutation.  

(* TODO: - simplify group interface
         - separate into different modules *)

Parameter (group : nat) (q : nat) (ident : group) (gexp : group -> q -> group) (qmul : q -> q -> q).
Parameter (gexp_gexp : forall g x y, gexp (gexp g x) y = gexp g (qmul x y)).
Parameter (gmul : group -> group -> group) (gmulA : associative gmul) (gmulC : commutative gmul).
Parameter (ginv : group -> group) (gmulK : forall x, gmul x (ginv x) = ident) (gmul1 : forall g, gmul ident g  = g).
Parameter (qmulC : commutative qmul).
Parameter (unifq : Dist q).

Definition unif_group :=
  (x <-- Samp unifq ;; Ret (gexp ident x)).

(* Need to do this since unif_group is not yet seen as a uniform distribution by the system. This should be a straightforward fix. *)
Parameter (unif_group_bij : forall g,
             (x <-- unif_group ;; Ret (gmul x g)) =r unif_group).

Definition FAuth (cin cout : chan group) (leak : chan group) (ok : chan TUnit) :=
  pars [::
          leak ::= copy cin;
          cout ::= (_ <-- Read ok ;; copy cin)
       ].

Definition DDH0 (out : chan (group ** group ** group)) : rset :=
  x <- new q ;;
  y <- new q ;;
  pars [::
          x ::= Samp unifq;
          y ::= Samp unifq;
          out ::=
          (x <-- Read x;; y <-- Read y ;;
           Ret {{ {{ gexp ident x, gexp ident y }}, gexp ident (qmul x y) }}) ].

Definition DDH1 (out : chan (group ** group ** group)) : rset :=
  x <- new q ;;
  y <- new q ;;
  z <- new q ;;
  pars [::
          x ::= Samp unifq;
          y ::= Samp unifq;
          z ::= Samp unifq;
          out ::=
          (x <-- Read x;; y <-- Read y ;; z <-- Read z ;;
           Ret {{ {{ gexp ident x, gexp ident y }}, gexp ident z }}) ].
          

Definition RealParty (send recv out : chan group) :=
  x <- new q ;;
  pars [::
          x ::= Samp unifq;
          send ::= (x <-- Read x ;; Ret (gexp ident x));
          out ::=  (x <-- Read x ;; h <-- Read recv ;; Ret (gexp h x)) ].

Definition DHKEReal (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan TUnit) :=
  send1 <- new group ;;
  send2 <- new group ;;
  recv1 <- new group ;;
  recv2 <- new group ;;
  pars [::
          RealParty send1 recv2 outA;
          RealParty send2 recv1 outB;
          FAuth send1 recv1 leak1 ok1;
          FAuth send2 recv2 leak2 ok2
                ].

Definition KEIdeal (okA okB : chan TUnit) (outA outB : chan group) :=
  x <- new q ;; 
  pars [::
          x ::= Samp unifq;
          outA ::= (_ <-- Read okA ;; x <-- Read x ;; Ret (gexp ident x));
          outB ::= (_ <-- Read okB ;; x <-- Read x ;; Ret (gexp ident x))
                                                     ].

Definition DHKESim (ok1 ok2 okA okB : chan TUnit) (leak1 leak2 : chan group) :=
  pars [::
          okA ::= copy ok2;
          okB ::= copy ok1;
          leak1 ::= (x <-- Samp unifq;; Ret (gexp ident x));
          leak2 ::= (x <-- Samp unifq;; Ret (gexp ident x))
                   ].

Definition DHKESimIdeal (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan TUnit) :=
  okA <- new TUnit ;;
  okB <- new TUnit ;;
  pars [::
          KEIdeal okA okB outA outB;
          DHKESim ok1 ok2 okA okB leak1 leak2
               ].

(* Begin proof *)

Definition DHKERealHybrid (b : bool) (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan TUnit) :=
  ddh_samp <- new group ** group ** group ;;
  pars [::
          if b then DDH0 ddh_samp else DDH1 ddh_samp;
          outA ::= (_ <-- Read ok2;; p <-- Read ddh_samp;; Ret (p.2 : group));
          outB ::= (_ <-- Read ok1;; p <-- Read ddh_samp;; Ret (p.2 : group));
          leak1 ::= (p <-- Read ddh_samp ;; Ret (p.1.1 : group));
          leak2 ::= (p <-- Read ddh_samp ;; Ret (p.1.2 : group))
                      ].

Lemma DHKE1 (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan TUnit) :
  DHKEReal outA outB leak1 leak2 ok1 ok2 ~=
  DHKERealHybrid true outA outB leak1 leak2 ok1 ok2.
  rewrite /DHKEReal /RealParty /FAuth.
  setoid_rewrite New_in_pars.
  setoid_rewrite pars_pars; simpl.
  simpl.
  swap_tac 0 3.
  setoid_rewrite New_in_pars.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 6; setoid_rewrite pars_pars; simpl.
  swap_tac 0 8; setoid_rewrite pars_pars; simpl.
  setoid_rewrite (NewNew group q).
  setoid_rewrite (NewNew group q) at 2.
  swap_tac 0 6.
  under_new swap_at 0 0 1.
  setoid_rewrite pars_fold.
  setoid_rewrite (NewNew group q).
  setoid_rewrite (NewNew group q) at 2.
  swap_tac 0 3.
  under_new swap_at 0 0 1.
  setoid_rewrite pars_fold.
  etransitivity.
  apply EqNew => c _ _.
  apply EqNew => c0 _ _.
  apply EqNew => c1 _ _.
  apply EqNew => c2 _ _.
  rewrite /copy; simp_all.
  repeat ltac:(do_inline; simp_all).
  apply EqRefl.
  (* elim c0 *)
  setoid_rewrite (NewNew group q).
  setoid_rewrite (NewNew group q) at 2.
  swap_tac 0 1.
  under_new rewrite new_pars_remove.
  apply EqRefl.
  repeat set_tac.
  
  setoid_rewrite (NewNew group q).
  setoid_rewrite (NewNew group q).
  swap_tac 0 2.
  under_new rewrite new_pars_remove.
  apply EqRefl.
  repeat set_tac.
  

  symmetry.
  etransitivity.
  rewrite /DHKERealHybrid /DDH0.
  under_new rewrite New_in_pars.
  under_new rewrite New_in_pars.
  under_new rewrite pars_pars; simpl.
  etransitivity.
  apply EqNew => c _ _ .
  apply EqNew => c0 _ _ .
  apply EqNew => c1 _ _ .
  repeat ltac:(do_inline; simp_all).
  apply EqRefl.
  (* elim c *)
  setoid_rewrite NewNew.
  setoid_rewrite NewNew at 2.
  swap_tac 0 2.
  under_new rewrite new_pars_remove.
  apply EqRefl.
  repeat set_tac.
  apply EqRefl.
  
  apply EqNew => c _ _.
  apply EqNew => c0 _ _.


  swap_tac 0 (Out leak1).
  swap_at 0 0 1.
  swap_tac 1 (Out c0).
  rewrite pars_undep //=.

  swap_tac 0 (Out leak2).
  swap_tac 1 (Out c).
  rewrite pars_undep //=.


  align.
  apply EqOut.
  r_swap 0 1.
  apply EqBind_r => x.
  r_swap 0 1.
  apply EqBind_r => _.
  apply EqBind_r => y.
  rewrite gexp_gexp.
  rewrite qmulC //=.

  apply EqOut.
  apply EqBind_r => x.
  r_swap 0 1.
  apply EqBind_r => _.
  apply EqBind_r => y.
  rewrite gexp_gexp //=.
Qed.

Lemma DHKE2 (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan TUnit) :
  DHKERealHybrid false outA outB leak1 leak2 ok1 ok2 ~=
  DHKESimIdeal outA outB leak1 leak2 ok1 ok2.


rewrite /DHKERealHybrid //=.
etransitivity; rewrite /DDH1.
apply EqNew => ddh_samp _ _.
rewrite New_in_pars; apply EqNew => x _ _.
rewrite New_in_pars; apply EqNew => y _ _.
rewrite New_in_pars; apply EqNew => z _ _.
rewrite pars_pars //=.
repeat ltac:(do_inline; simp_all).
apply EqRefl.
setoid_rewrite (NewNew (group ** group ** group)).
setoid_rewrite (NewNew (group ** group ** group)).
setoid_rewrite (NewNew (group ** group ** group)).
swap_tac 0 3.
under_new rewrite new_pars_remove.
apply EqRefl.
repeat set_tac.
symmetry.
rewrite /DHKESimIdeal.
etransitivity.
rewrite /KEIdeal.
apply EqNew => okA _ _.
apply EqNew => okB _ _.
rewrite New_in_pars; apply EqNew => x _ _.
rewrite pars_pars //=.
swap_tac 0 3.
rewrite /DHKESim pars_pars //=.
rewrite /copy.
repeat ltac:(do_inline; simp_all).
apply EqRefl.
setoid_rewrite NewNew.
setoid_rewrite NewNew at 2.
under_new rewrite new_pars_remove.
apply EqRefl.
repeat set_tac.
rewrite NewNew.
under_new rewrite new_pars_remove.
apply EqRefl.
repeat set_tac.

symmetry; etransitivity.
apply EqNew => c' _ _.
apply EqNew => c _ _.
apply EqNew => c1 _ _.
swap_tac 0 (Out outA).
swap_tac 1 2.
rewrite pars_undep //=.
swap_tac 1 3.
rewrite pars_undep //=.
swap_tac 0 (Out outB).
swap_tac 1 3.
rewrite pars_undep //=.
swap_tac 1 3.
rewrite pars_undep //=.
swap_tac 0 (Out leak1).
swap_at 0 0 1.
rewrite pars_undep //=.
swap_at 0 0 1.
swap_tac 1 2.
rewrite pars_undep //=.
swap_tac 0 (Out leak2).
swap_tac 1 3.
rewrite pars_undep //=.
swap_at 0 0 1.
swap_tac 1 3.
rewrite pars_undep //=.
apply EqRefl.

etransitivity.
setoid_rewrite NewNew at 2.
swap_tac 0 6.
swap_tac 1 3.
under_new rewrite pars_fold.
apply EqRefl.
rewrite NewNew.
swap_tac 0 5.
under_new rewrite pars_fold.
apply EqRefl.
apply EqRefl.

apply EqNew => c _ _.
align.
apply EqOut; r_swap 0 1; done.
apply EqOut; r_swap 0 1; done.
Qed.


Lemma DHKE_security (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan TUnit) :
  (forall ddh_samp, DDH0 ddh_samp ~= DDH1 ddh_samp) -> 
  DHKEReal outA outB leak1 leak2 ok1 ok2 ~=
  DHKESimIdeal outA outB leak1 leak2 ok1 ok2.
  intros.
  rewrite DHKE1.
  rewrite -DHKE2.
  rewrite /DHKERealHybrid.
  apply EqNew => ddh_samp _ _.
  align.
Qed.

(**** END DHKE OTP *****)



(**** BEGIN OTP *****)


  Definition Alice (key cin cout : chan group) :=
    pars [::
            cout ::= (
                     k <-- Read key ;;
                     i <-- Read cin ;;
                     Ret (gmul k i))].

  Definition Bob (key cin cout : chan group) :=
    pars [::
            cout ::= (
                     k <-- Read key ;;
                     i <-- Read cin ;;
                     Ret (gmul (ginv k) i))].

  Definition OTPReal (key_exchange : chan TUnit -> chan TUnit -> chan group -> chan group -> rset) (cin leak cout : chan group) ok okA okB :=
    send <- new group ;;
    recv <- new group ;;
    keyA <- new group ;;
    keyB <- new group ;;
    pars [::
            key_exchange okA okB keyA keyB;
            Alice keyA cin send;
            FAuth send recv leak ok;
            Bob keyB recv cout].

  Definition OTPIdeal (cin cout : chan group) (cin_timing : chan TUnit) (okI : chan TUnit) :=
    pars [::
            cout ::= (_ <-- Read okI;; Read cin);
            cin_timing ::= (_ <-- Read cin ;; Ret vtt)
         ].

  Definition OTPSim (cin_timing : chan TUnit) (leak : chan group) (okI okR okA okB : chan TUnit) :=
    pars [::
        okI ::= (_ <-- Read okR;; _ <-- Read okA;; _ <-- Read okB ;; Ret vtt);
        leak ::= (_ <-- Read cin_timing ;; _ <-- Read okA;; unif_group )].


  Theorem OTPSecure cin leak cout okR okA okB : OTPReal KEIdeal cin leak cout okR okA okB ~=
                                            (t <- new TUnit ;;
                                             okI <- new TUnit ;;
                                             OTPIdeal cin cout t okI
                                                      ||| OTPSim t leak okI okR okA okB).
    rewrite /OTPReal.
    rewrite /KEIdeal.
    setoid_rewrite New_in_pars.
    setoid_rewrite pars_pars; simpl.
    rewrite /Alice /Bob.
    
    (* Simplify, eliminate channels *)
    swap_tac 0 3.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 4.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 6.
    setoid_rewrite pars_pars; simpl.
    etransitivity.
    repeat (apply EqNew; intro => _ _).
    rewrite /copy.
    repeat ltac:(do_inline; simp_all).
    apply EqRefl.
    setoid_rewrite NewNew at 4.
    swap_tac 0 3.
    under_new rewrite new_pars_remove; [apply EqRefl |intros; repeat set_tac].
    setoid_rewrite NewNew at 3.
    swap_tac 0 1.
    under_new rewrite new_pars_remove; [apply EqRefl |intros; repeat set_tac].
    setoid_rewrite NewNew at 2.
    under_new rewrite new_pars_remove; [apply EqRefl |intros; repeat set_tac].
    rewrite NewNew.
    swap_tac 0 2.
    etransitivity.
    repeat (apply EqNew; intro => _ _).
    swap_tac 0 1.
    swap_tac 0 3.
    rewrite pars_inline //=.
    apply EqRefl.
    swap_tac 0 1.
    under_new rewrite new_pars_remove; [apply EqRefl |intros; repeat set_tac].
    
    (* reason about output *)
    etransitivity.
    apply EqNew => key _ _.
    edit_tac 1.
    r_swap 0 1.
    r_swap 1 4.
    rewrite EqReadSame.
    apply EqBind_r => k.
    apply EqBind_r => ok1.
    apply EqBind_r => m.
    apply EqBind_r => ok2.
    apply EqBind_r => ok3.
    rewrite gmulA.
    rewrite (gmulC _ (gexp ident k)) gmulK gmul1 //=.
    apply EqRxnRefl.
    swap_tac 0 1.
    swap_tac 1 2.
    rewrite pars_undep //=.
    swap_tac 0 2.
    simp_at 0.
    swap_at 0 0 1.
    apply EqRefl.
    rewrite pars_fold.

    (* now simplify ideal world *)
    symmetry.
    swap_tac 1 2.
    under_new rewrite pars_fold.
    apply EqRefl.
    swap_tac 0 2.
    rewrite pars_fold.
    align.
    apply EqOut.
    rewrite /unif_group.
    simp_rxn.
    symmetry.
    r_swap 0 2.
    r_swap 1 2.
    apply EqBind_r; intro m.
    apply EqBind_r => _.
    etransitivity.
    apply EqBind_r; intro.
    rewrite gmulC //=.
    apply EqRxnRefl.
    assert (H := unif_group_bij m).
    rewrite /unif_group in H.
    rewrite -H.
    symmetry; simp_rxn.
    apply EqBind_r; intro.
    rewrite gmulC //=.

    apply EqOut.
    simp_rxn.
    r_swap 0 1.
    apply EqBind_r => _.
    symmetry; r_swap 0 2.
    apply EqBind_r => _.
    r_swap 0 1.
    apply EqBind_r => _.
    rewrite EqBindRet //=.
Qed.


(*** COMPOSITION ***)

  
Lemma OTP_comp1 cin leak cout okR okA okB leak1_ke leak2_ke :
       (forall ddh_samp : chan ((group ** group) ** group),
        DDH0 ddh_samp ~= DDH1 ddh_samp) ->
  OTPReal (fun okA okB keyA keyB => DHKEReal keyA keyB leak1_ke leak2_ke okA okB) cin leak cout okR okA okB ~=
  OTPReal (fun okA okB keyA keyB => DHKESimIdeal keyA keyB leak1_ke leak2_ke okA okB) cin leak cout okR okA okB.
  intros.
  rewrite /OTPReal.
  repeat (apply EqNew; intro => _ _).
  rewrite DHKE_security.
  done.
  apply H.
Qed.

Lemma OTP_comp2 cin leak cout okR okA okB leak1_ke leak2_ke :
  OTPReal (fun okA okB keyA keyB => DHKESimIdeal keyA keyB leak1_ke leak2_ke okA okB) cin leak cout okR okA okB ~=
  okA_sim <- new TUnit ;;
  okB_sim <- new TUnit ;;
  pars [::
          OTPReal KEIdeal cin leak cout okR okA_sim okB_sim;
          DHKESim okA okB okA_sim okB_sim leak1_ke leak2_ke].
  rewrite /OTPReal.
  rewrite /DHKESimIdeal.
  repeat setoid_rewrite New_in_pars.
  rotate_news.
  rotate_news.
  rotate_news.
  rotate_news.
  apply EqNew => okA_sim _ _.
  apply EqNew => okB_sim _ _.
  rotate_news.
  repeat (apply EqNew; intro => _ _).
  rewrite !pars_pars //=.
  align.
Qed.

Lemma OTP_comp3 cin leak cout okR okA okB leak1_ke leak2_ke :
  OTPReal (fun okA okB keyA keyB => DHKESimIdeal keyA keyB leak1_ke leak2_ke okA okB) cin leak cout okR okA okB ~=
  okA_sim <- new TUnit ;;
  okB_sim <- new TUnit ;;
  pars [::
        (t <- new TUnit ;; okI <- new TUnit ;; OTPIdeal cin cout t okI
                                                      ||| OTPSim t leak okI okR okA_sim okB_sim);
          DHKESim okA okB okA_sim okB_sim leak1_ke leak2_ke].
  rewrite OTP_comp2.
  apply EqNew; intro => _ _.
  apply EqNew; intro => _ _.
  rewrite OTPSecure.
  done.
Qed.

Lemma OTP_comp cin leak cout okR okA okB leak1_ke leak2_ke :
       (forall ddh_samp : chan ((group ** group) ** group),
        DDH0 ddh_samp ~= DDH1 ddh_samp) ->
  OTPReal (fun okA okB keyA keyB => DHKEReal keyA keyB leak1_ke leak2_ke okA okB) cin leak cout okR okA okB ~=
  okA_sim <- new TUnit ;;
  okB_sim <- new TUnit ;;
  pars [::
        (t <- new TUnit ;; okI <- new TUnit ;; OTPIdeal cin cout t okI
                                                      ||| OTPSim t leak okI okR okA_sim okB_sim);
          DHKESim okA okB okA_sim okB_sim leak1_ke leak2_ke].
  intro.
  rewrite OTP_comp1 //= OTP_comp3.
  done.
Qed.
    


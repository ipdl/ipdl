
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Ipdl.Approx.  
Require Import Sim Typ Lib.Perm Lib.SeqOps Permutation.


(* We axiomitize groups in a manner useful for the proof *)
Module Type DHKEParams.

  Parameter (group sk : finType) (Hgroup : Inhabited group) (Hsk:  Inhabited sk).

  Parameter (gmul : group -> group -> group).
  Parameter (ginv : group -> group).
  Parameter (gmulA : forall x y z, gmul (gmul x y) z = gmul x (gmul y z)).
  Parameter (gmulC : forall x y, gmul x y = gmul y x).
  Parameter (ident : group).
  Parameter (gmulK : forall x, gmul x (ginv x) = ident).
  Parameter (gmul1 : forall x, gmul x ident = x).

  Parameter (glog : group -> sk).
  Parameter (gexp : group -> sk -> group).
  Parameter (glogK : forall x, glog (gexp ident x) = x).
  Parameter (sk_mul : sk -> sk -> sk).
  Parameter (gexp_gexp : forall x y g, gexp (gexp g x) y = gexp g (sk_mul x y)).
  Parameter (sk_mulC : forall x y, sk_mul x y = sk_mul y x).
  Parameter (gen_sk : Dist sk).

  Parameter (gexpK : forall x, gexp ident (glog x) = x).
  Parameter (gmul_inj : forall g, injective (fun x => gmul x g)).

  Definition unif_group := dbind gen_sk (fun x => DRet (gexp ident x)).
  Parameter (Hunif : uniform unif_group).
End DHKEParams.


Module KeyExchange (Import P : DHKEParams).

Section DHKE.
Context {chan : Type -> Type}.

(* The DDH assumption *)
Definition DDH0 (out : chan (group * group * group)) : ipdl :=
  x <- new sk ;;
  y <- new sk ;;
  pars [::
          x ::= Samp gen_sk;
          y ::= Samp gen_sk;
          out ::=
          (x <-- Read x;; y <-- Read y ;;
           Ret ( gexp ident x, gexp ident y, gexp (gexp ident x) y))].

Definition DDH1 (out : chan (group * group * group)) : ipdl :=
  x <- new sk ;;
  y <- new sk ;;
  z <- new sk ;;
  pars [::
          x ::= Samp gen_sk;
          y ::= Samp gen_sk;
          z ::= Samp gen_sk;
          out ::=
          (x <-- Read x;; y <-- Read y ;; z <-- Read z ;;
           Ret ( gexp ident x, gexp ident y, gexp ident z))].
          
Definition FAuth {t} (cin cout : chan t) (leak : chan t) (ok : chan unit) :=
  pars [::
          leak ::= copy cin;
          cout ::= (_ <-- Read ok ;; copy cin)
       ].

Definition DHKE_RealParty (send recv out : chan group) :=
  x <- new sk ;;
  pars [::
          x ::= Samp gen_sk;
          send ::= (x <-- Read x ;; Ret (gexp ident x));
          out ::=  (x <-- Read x ;; h <-- Read recv ;; Ret (gexp h x)) ].

(* 
   In this version of Diffie-Hellman key exchange,
   Alice and Bob send their DH public keys to each other 
   over authenticated (but still public) channels. 
   They then agree on a secret key in the usual way.
 
   Note here that Alice and Bob have symmetric code --  
   this is a simplification of handshake protocols such as 
   TLS, where the server responds to the client, and both
   run different software. 
*)


Definition DHKEReal (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan unit) :=
  send1 <- new group ;;
  send2 <- new group ;;
  recv1 <- new group ;;
  recv2 <- new group ;;
  pars [::
          DHKE_RealParty send1 recv2 outA;
          DHKE_RealParty send2 recv1 outB;
          FAuth send1 recv1 leak1 ok1;
          FAuth send2 recv2 leak2 ok2
                ].

Definition DHKEIdeal (okA okB : chan unit) (outA outB : chan group) :=
  x <- new sk ;; 
  pars [::
          x ::= Samp gen_sk;
          outA ::= (_ <-- Read okA ;; x <-- Read x ;; Ret (gexp ident x));
          outB ::= (_ <-- Read okB ;; x <-- Read x ;; Ret (gexp ident x))
                                                     ].

Definition DHKESim (ok1 ok2 okA okB : chan unit) (leak1 leak2 : chan group) :=
  pars [::
          okA ::= copy ok2;
          okB ::= copy ok1;
          leak1 ::= (x <-- Samp gen_sk;; Ret (gexp ident x));
          leak2 ::= (x <-- Samp gen_sk;; Ret (gexp ident x))
                   ].

Definition DHKESimIdeal (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan unit) :=
  okA <- new unit ;;
  okB <- new unit ;;
  pars [::
          DHKEIdeal okA okB outA outB;
       DHKESim ok1 ok2 okA okB leak1 leak2
               ].

(* Begin proof *)

Definition DHKERealHybrid (b : bool) (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan unit) :=
  ddh_samp <- new group * group * group ;;
  pars [::
          if b then DDH0 ddh_samp else DDH1 ddh_samp;
          outA ::= (_ <-- Read ok2;; p <-- Read ddh_samp;; Ret (p.2));
          outB ::= (_ <-- Read ok1;; p <-- Read ddh_samp;; Ret (p.2));
          leak1 ::= (p <-- Read ddh_samp ;; Ret (p.1.1));
          leak2 ::= (p <-- Read ddh_samp ;; Ret (p.1.2))
                      ].

Instance inhab_group : Inhabited group := Hgroup.
Instance inhab_sk : Inhabited sk := Hsk.

Lemma DHKE1 (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan unit) :
  DHKEReal outA outB leak1 leak2 ok1 ok2 =p
  DHKERealHybrid true outA outB leak1 leak2 ok1 ok2.
  rewrite /DHKEReal /DHKE_RealParty /FAuth.
  setoid_rewrite New_in_pars.
  setoid_rewrite pars_pars; simpl.
  simpl.
  swap_tac 0 3.
  setoid_rewrite New_in_pars.
  setoid_rewrite pars_pars; simpl.
  swap_tac 0 6; setoid_rewrite pars_pars; simpl.
  swap_tac 0 8; setoid_rewrite pars_pars; simpl.
  setoid_rewrite (EqNewExch group sk).
  setoid_rewrite (EqNewExch group sk) at 2.
  swap_tac 0 6.
  under_new swap_at 0 0 1.
  simpl.
  setoid_rewrite pars_fold.
  setoid_rewrite (EqNewExch group sk).
  setoid_rewrite (EqNewExch group sk) at 2.
  swap_tac 0 3.
  under_new swap_at 0 0 1.
  simpl.
  setoid_rewrite pars_fold.
  etransitivity.
  Intro => c.
  Intro => c0.
  Intro => c1.
  Intro => c2.
  rewrite /copy; simp_all.
  do_inline.
  repeat ltac:(do_inline; simp_all).
  apply EqRefl.
  (* elim c0 *)
  simpl.
  setoid_rewrite (EqNewExch group sk).
  setoid_rewrite (EqNewExch group sk) at 2.
  swap_tac 0 1.
  Check new_pars_remove.
  under_new rewrite new_pars_remove.
  apply EqRefl.
  repeat set_tac.
  
  setoid_rewrite (EqNewExch group sk).
  setoid_rewrite (EqNewExch group sk).
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
  Intro => c.
  Intro => c0.
  Intro => c1.
  repeat ltac:(do_inline; simp_all).
  apply EqRefl.
  (* elim c *)
  setoid_rewrite EqNewExch.
  setoid_rewrite EqNewExch at 2.
  swap_tac 0 2.
  under_new rewrite new_pars_remove.
  apply EqRefl.
  apply EqRefl.

  
  apply EqCongNew => c.
  apply EqCongNew => c0.


  swap_tac 0 (Out leak1).
  swap_at 0 0 1.
  swap_tac 1 (Out c0).
  rewrite -pars_mkdep //=.

  swap_tac 0 (Out leak2).
  swap_tac 1 (Out c).
  rewrite -pars_mkdep //=.


  align.
  apply EqCongReact.
  r_swap 0 1.
  apply EqBind_r => x.
  r_swap 0 1.
  apply EqBind_r => _.
  apply EqBind_r => y.
  rewrite !gexp_gexp.
  rewrite sk_mulC //=.

  apply EqCongReact.
  apply EqBind_r => x.
  r_swap 0 1.
  apply EqBind_r => _.
  apply EqBind_r => y.
  rewrite !gexp_gexp.
  rewrite sk_mulC //=.
Qed.

Lemma DHKE2 (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan unit) :
  DHKERealHybrid false outA outB leak1 leak2 ok1 ok2 =p
  DHKESimIdeal outA outB leak1 leak2 ok1 ok2.

rewrite /DHKERealHybrid //=.
etransitivity; rewrite /DDH1.
apply EqCongNew => ddh_samp.
rewrite New_in_pars; apply EqCongNew => x.
rewrite New_in_pars; apply EqCongNew => y.
rewrite New_in_pars; apply EqCongNew => z.
rewrite pars_pars //=.
repeat ltac:(do_inline; simp_all).
apply EqRefl.
setoid_rewrite (EqNewExch (group * group * group)).
setoid_rewrite (EqNewExch (group * group * group)).
setoid_rewrite (EqNewExch (group * group * group)).
swap_tac 0 3.
under_new rewrite new_pars_remove.
apply EqRefl.
simpl.
symmetry.
rewrite /DHKESimIdeal.
etransitivity.
rewrite /DHKEIdeal.
apply EqCongNew => okA .
apply EqCongNew => okB .
rewrite New_in_pars; apply EqCongNew => x.
rewrite pars_pars //=.
swap_tac 0 3.
rewrite /DHKESim pars_pars //=.
rewrite /copy.
repeat ltac:(do_inline; simp_all).
apply EqRefl.
setoid_rewrite EqNewExch.
setoid_rewrite EqNewExch at 2.
under_new rewrite new_pars_remove.
apply EqRefl.
simpl.
rewrite EqNewExch.
under_new rewrite new_pars_remove.
apply EqRefl.
simpl.

symmetry; etransitivity.
apply EqCongNew => c'.
apply EqCongNew => c.
apply EqCongNew => c1.
swap_tac 0 (Out outA).
swap_tac 1 2.
rewrite -pars_mkdep //=.
swap_tac 1 3.
rewrite -pars_mkdep //=.
swap_tac 0 (Out outB).
swap_tac 1 3.
rewrite -pars_mkdep //=.
swap_tac 1 3.
rewrite -pars_mkdep //=.
swap_tac 0 (Out leak1).
swap_at 0 0 1.
rewrite -pars_mkdep //=.
swap_at 0 0 1.
swap_tac 1 2.
rewrite -pars_mkdep //=.
swap_tac 0 (Out leak2).
swap_tac 1 3.
rewrite -pars_mkdep //=.
swap_at 0 0 1.
swap_tac 1 3.
rewrite -pars_mkdep //=.
apply EqRefl.

etransitivity.
setoid_rewrite EqNewExch at 2.
swap_tac 0 6.
swap_tac 1 3.
under_new rewrite pars_fold.
apply EqRefl.
rewrite EqNewExch.
swap_tac 0 5.
under_new rewrite pars_fold.
apply EqRefl.
apply EqRefl.

apply EqCongNew => c.
align.
apply EqCongReact; r_swap 0 1; done.
apply EqCongReact; r_swap 0 1; done.
Qed.


(* This error term represents a simple polynomial-time 
   reduction over the DDH hardness assumption. *)



Lemma DHKE_security (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan unit) e :
  (forall ddh_samp, DDH0 ddh_samp =a_(e) DDH1 ddh_samp) -> 
  DHKEReal outA outB leak1 leak2 ok1 ok2 =a_(comp_err e 4)
  DHKESimIdeal outA outB leak1 leak2 ok1 ok2.
  intros.
  rewrite DHKE1.
  rewrite -DHKE2.
  rewrite /DHKERealHybrid.
  apply AEq_new => ddh_samp.
  arewrite (H ddh_samp).
  done.
  rewrite add_err0 //=.
Qed.

(* Typing sanity check *)

Definition DHKE_chans (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan unit) := [:: tag outA; tag outB; tag leak1; tag leak2].

Lemma DHKEReal_t (outA outB leak1 leak2 : chan group) (ok1 ok2 : chan unit) : ipdl_t (DHKE_chans outA outB leak1 leak2 ok1 ok2) (DHKEReal outA outB leak1 leak2 ok1 ok2).
  rewrite /DHKE_chans /DHKEReal /DHKE_RealParty /FAuth.
  repeat type_tac.
  perm_match.
Qed.

Lemma DHKESimIdeal_t outA outB leak1 leak2 ok1 ok2 :
  ipdl_t (DHKE_chans outA outB leak1 leak2 ok1 ok2)
         (DHKESimIdeal outA outB leak1 leak2 ok1 ok2).
  rewrite /DHKE_chans /DHKESimIdeal /DHKEIdeal /DHKESim.
  repeat type_tac.
  perm_match.
Qed.

End DHKE.
  
End KeyExchange.

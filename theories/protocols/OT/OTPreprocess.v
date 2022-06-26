(* Preprocessing OT example,
  as in https://www.cs.umd.edu/~jkatz/gradcrypto2/f13/lecture5.pdf .

   In preprocessing OT, we show that the sender and receiver
can leverage an initial OT on two uniform bitstrings to perform an OT later on. This is advantageous, because the 'online' part can be done very fast (it only requires xor), while the 'offline' part requires expensive cryptography.

 The protocol is proven semi-honest secure, in the case when 
the receiver is corrupt. 

 *)



Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Pars Big.
Require Import OTIdeal Lib.Set Typ Lib.SeqOps.
Require Import Permutation.
Check Perm_swap.

Open Scope bool_scope.

Lemma new_pars_undep {chan} {t1 t2} (c2 : chan t2) (rs : chan t1 -> seq ipdl) r r' :
  (forall (t : Type) (c0 : chan t), can_read c0 r -> reads_from c0 r') ->
  (c1 <- new t1 ;; pars [:: Out c2 (_ <-- Read c1 ;; r'), Out c1 r & rs c1]) =p
  (c1 <- new t1 ;; pars [:: Out c2 (r'), Out c1 r & rs c1]) .
  intros.
  apply EqCongNew => c1.
  symmetry.
  apply pars_mkdep; rewrite //=.
Qed.
                                                                             
Section OTPre.
  Context {chan : Type -> Type}.
  (* OT Channels *)
  Context (L : nat) (m : chan (L.-bv * L.-bv)) (i : chan bool) (o : chan L.-bv).

  (* We assume that B, the receiver in the top-level OT protocol, is semi-honest. *)

  Context (leakC : chan bool) (leak_base_o : chan L.-bv) (leaky : chan (L.-bv * L.-bv)).

  Definition OTPreA (base_m : chan (L.-bv * L.-bv)) (y : chan (L.-bv * L.-bv)) (z : chan bool) :=
    k <- new (L.-bv * L.-bv) ;;
    pars [::
            k ::= (Samp Unif);
            base_m ::= (copy k);
            y ::= (
                  m01 <-- Read m ;;
                  k01 <-- Read k ;;
                  z <-- Read z ;;
                  Ret ([pair i => (m01 # i) +t (k01 # (i (+) z)) ] )) ].

               
  Definition OTPreB (base_i : chan bool) (base_o : chan L.-bv) (y : chan (L.-bv * L.-bv)) (z : chan bool) :=
    c <- new bool ;;
    pars [::
            c ::= (Samp Unif) ;
            leakC ::= (copy c) ;
            base_i ::= (copy c) ;
            leak_base_o ::= (copy base_o) ;
            z ::= (
                  i <-- Read i ;;
                  c <-- Read c ;;
                  Ret (i (+) c) );
            leaky ::= (copy y); 
            o ::= (
                  b <-- Read i ;;
                  y01 <-- Read y ;;
                  k_c <-- Read base_o ;;
                  Ret (((y01 # b) +t k_c)) ) ].

            
(* ******     *)
  
  Definition OTPre_Sim (leako : chan L.-bv) 
    :=
  j <- new L.-bv ;;
  pars [::
          Out leaky (
            j <-- Read j ;;
            i <-- Read i ;;
            o <-- Read leako ;;
            x <-- Samp Unif ;;
            Ret (
                if i then (x, o +t j) else (o +t j, x) ) );
          Out leakC (Samp Unif) ;
          Out j (Samp Unif) ;
          Out leak_base_o (copy j) 
          ].

  Ltac perm_swap_l n m :=
    match goal with
      | [ |- Permutation ?xs _] => 
        rewrite (Perm_swap n m xs); rewrite /swap //= /lset //= end.

  Lemma OTPre_sim_t leako :
    ipdl_t [:: tag leaky; tag leakC; tag leak_base_o] (OTPre_Sim leako).
    rewrite /OTPre_Sim.
    repeat type_tac.
    perm_swap_l 0 1.
    perm_swap_l 1 2.
  Qed.

  Definition OTPre :=
    y <- new (L.-bv * L.-bv) ;;
    z <- new bool ;;
    base_i <- new bool ;;
    base_o <- new L.-bv ;;
    base_m <- new (L.-bv * L.-bv) ;;
    pars [::
            OTPreA base_m y z;
            OTPreB base_i base_o y z;
            OTIdeal _ base_i base_m base_o ].

  Lemma OTPre_eq :
    OTPre =p
             (leako <- new L.-bv ;;
              pars [::
                      OTIdeal _ i m o;
                      OTIdeal _ i m leako;
                      OTPre_Sim leako]).
    unfold OTPre.
    etransitivity.
    rewrite /OTPreA.
    setoid_rewrite newPars.
    setoid_rewrite pars_pars; simpl.
    rewrite /OTPreB.
    swap_tac 0 3.
    setoid_rewrite newPars.
    setoid_rewrite pars_pars; simpl.
    rewrite /OTIdeal.
    setoid_rewrite (EqNewExch (L.-bv * L.-bv) (L.-bv * L.-bv)).
    setoid_rewrite (EqNewExch (L.-bv * L.-bv) bool) at 2.
    swap_tac 0 10.
    under_new swap_at 0 0 1.
    simpl.
    swap_tac 1 7.
    setoid_rewrite pars_fold.
    swap_tac 0 1.
    swap_tac 0 2.
    setoid_rewrite (EqNewExch L.-bv (L.-bv * L.-bv)).
    setoid_rewrite (EqNewExch L.-bv bool).
    under_new rewrite new_pars_inline; [ apply EqRefl | done].
    under_new simp_at 0.
    simpl.
    swap_tac 0 5.
    under_new swap_at 0 0 2.
    simpl.
    setoid_rewrite pars_fold.
    under_new simp_at 0.
    under_new swap_at 0 0 1.
    simpl.
    setoid_rewrite (EqNewExch bool (L.-bv * L.-bv)).
    setoid_rewrite (EqNewExch bool bool).
    under_new rewrite new_pars_inline; [ apply EqRefl | done].
    simpl.
    swap_tac 0 4.
    under_new swap_at 0 0 1.
    simpl.
    setoid_rewrite pars_fold.
    setoid_rewrite (EqNewExch (L.-bv * L.-bv) bool).
    setoid_rewrite (EqNewExch (L.-bv * L.-bv) (L.-bv * L.-bv)).
    setoid_rewrite (EqNewExch (L.-bv * L.-bv) bool).
    swap_tac 0 2.
    swap_tac 1 5.
    under_new rewrite new_pars_inline; [ apply EqRefl | done].
    under_new simp_at 0.
    simpl.
    swap_tac 0 3.
    under_new swap_at 0 0 3.
    simpl.
    setoid_rewrite pars_fold.
    under_new simp_at 0.
    setoid_rewrite (EqNewExch bool (L.-bv * L.-bv)).
    setoid_rewrite (EqNewExch bool bool).
    swap_tac 1 4.
    under_new swap_at 0 0 2.
    under_new rewrite new_pars_inline; [ apply EqRefl | done].
    under_new simp_at 0.
    simpl.
    swap_tac 0 2.
    under_new swap_at 0 0 2.
    simpl.
    setoid_rewrite pars_fold.
    under_new simp_at 0.
    simpl.
    swap_tac 0 1.
    apply EqCongNew => c .
    apply EqCongNew => d .
    edit_tac 0.
    (* Simplifying o *)
        r_swap 1 6.
        rewrite EqReadSame.
        apply EqBind_r => x_i.
        r_swap 1 3.
        rewrite /copy.
        simp_rxn.
        rewrite EqReadSame.
        apply EqBind_r => x_d.
        apply EqBind_r => x_m.
        rewrite EqReadSame.
        apply EqBind_r => x_c.
        instantiate (1 := fun _ =>
                       Ret (if x_i then x_m.2 else x_m.1)).
        simpl.
        destruct (x_i), x_d; simpl; rewrite xortA xortK xort0; done.
        apply EqRefl.
        apply _.
        apply _.
   simpl; swap_tac 1 5.
   under_new swap_at 0 0 1.
   under_new rewrite new_pars_undep; rewrite //=.
   apply EqRefl.
   rewrite EqNewExch.
   swap_tac 1 4.
   under_new swap_at 0 0 2.
   under_new rewrite new_pars_undep; rewrite //=.
   apply EqRefl.
   (* Rerandomize c1 *)
   etransitivity.
        apply EqCongNew => c .
        swap_tac 0 1.
        swap_tac 1 4.
        etransitivity.
        apply EqCongNew => c1 .
        rewrite pars_mkdep //=.
        apply pars_cons_cong.
        instantiate ( 1 := 
                       Out c1 (b <-- Read c ;;
                               x <-- Samp Unif  ;;
                               y <-- Samp Unif ;;
                               Ret (if b then (y, x) else (x, y) ))).
        apply EqCongReact.
        apply EqBind_r => x.
        destruct x.
        etransitivity.
        rewrite EqSampBind.
        apply EqBind_r => x. 
        rewrite EqSampBind.
        apply EqBind_r => y. 
        rewrite EqSampRet //=.
        apply EqRxnRefl.
        r_swap 0 1.
        apply EqBind_r => x. 
        apply EqBind_r => y. 
        done.

        etransitivity.
        rewrite EqSampBind.
        apply EqBind_r => x. 
        rewrite EqSampBind.
        apply EqBind_r => y. 
        rewrite EqSampRet //=.
        apply EqRxnRefl.
        apply EqBind_r => x. 
        apply EqBind_r => y. 
        done.
        done.

        under_new swap_at 0 0 1.
        setoid_rewrite <- pars_fold at 1.
        under_new swap_at 0 0 2.
        simpl; setoid_rewrite <- pars_fold at 1.
        swap_tac 0 1.
        swap_tac 0 5.
        under_new swap_at 0 0 1.
        setoid_rewrite (EqNewExch (L.-bv * L.-bv) L.-bv) at 1.
        setoid_rewrite (EqNewExch (L.-bv * L.-bv) L.-bv) at 1.
        unfold copy.
        under_new simp_at 0.
        under_new rewrite new_pars_inline; [ apply EqRefl | done].
        under_new simp_at 0.
        simpl;swap_tac 0 7.
        under_new swap_at 0 0 3.
        simpl; setoid_rewrite pars_fold at 1.
        under_new simp_at 0.

        (* now inline the new defs *)
        etransitivity.
        apply EqCongNew => c0 .
        apply EqCongNew => c1 .
        swap_tac 0 6.
        edit_tac 0.
        apply EqBind_r => x.
        apply EqBind_r => y.
        rewrite EqReadSame.
        apply EqBind_r => b.
        instantiate (1 := fun _ => Ret y).
        simpl.
        destruct b; simpl; done.
        swap_tac 1 2.
        swap_at 0 0 2.
        rewrite -pars_mkdep //=.
        swap_tac 1 4. 
        rewrite -pars_mkdep //=.
        apply EqRefl.
        simpl; swap_tac 0 6.
        setoid_rewrite pars_fold at 1.

        (* Now rerandomize leaky *)
        apply EqCongNew => c0 .
        edit_tac 0.
        r_swap 0 5.
        r_swap 0 5.
        r_swap 0 5.
        r_swap 0 5.
        r_swap 0 5.
        r_swap 0 3.
        r_swap 1 2.
        rewrite EqReadSame.
        apply EqBind_r => xc.
        apply EqBind_r => xc0.
        apply EqBind_r => xi.
        apply EqBind_r => xm.
        unfold mkpair; simpl.
        instantiate (1 := fun xm => 
                       x <-- Samp (@Unif [finType of L.-bv] _)  ;;
                       Ret (if xi then _ else _ )).
        simpl.
        destruct xc.
        rewrite addbT negbK.
        destruct xi; simpl.
        symmetry.

        instantiate (1 := (x, xm.2 +t xc0)).

        rewrite (EqBind_r_samp_bijection _ _ _ _ (fun (x : L.-bv) => xm.1 +t x)) //=.
        apply uniform_Unif.
        apply xort_inj_l.


        instantiate (1 := (xm.1 +t xc0, x)).
        rewrite (EqBind_r_samp_bijection _ _ _ _ (fun (x : L.-bv) => xm.2 +t x)) //=.
        apply EqBind_r; intro.
        rewrite -xortA xortK (xortC (tzero _)) xort0 //=.
        apply uniform_Unif.
        apply xort_inj_l.

        destruct xi; simpl.

        symmetry.
        rewrite (EqBind_r_samp_bijection _ _ _ _ (fun (x : L.-bv) => xm.1 +t x)) //=.
        apply uniform_Unif.
        apply xort_inj_l.

        symmetry.
        rewrite (EqBind_r_samp_bijection _ _ _ _ (fun (x : L.-bv) => xm.2 +t x)) //=.
        apply uniform_Unif.
        apply xort_inj_l.

        swap_tac 1 3.
        rewrite -pars_mkdep //=.
        apply EqRefl.
        rewrite EqNewExch.
        swap_tac 0 2.
        setoid_rewrite pars_fold.

   (**  Now working on ideal world **)
   symmetry.
   unfold OTIdeal, OTPre_Sim.
   swap_tac 0 2.
   setoid_rewrite newPars.
   setoid_rewrite pars_pars; simpl.
   setoid_rewrite (EqNewExch L.-bv L.-bv).
   under_new swap_at 0 0 2.
   simpl; swap_tac 1 4.
   setoid_rewrite pars_fold.
   under_new simp_at 0.
   apply EqCongNew => c .
   symmetry; swap_tac 0 1; symmetry.

   (* Now matching up *)
   apply pars_cons_cong.
   apply EqCongReact.
   r_swap 1 3.
   rewrite EqReadSame.
   r_swap 0 2.
   apply EqBind_r => xc.
   apply EqBind_r => xi.
   apply EqBind_r => xm.
   apply EqBind_r => b.
   destruct xi; simpl.
   rewrite xortC; done.
   rewrite xortC; done.
   swap_tac 0 2; apply pars_cons_cong.
   symmetry; apply EqCongReact; rewrite EqBindRet; done.
   swap_tac 0 1; apply pars_cons_cong.
   done.
   swap_tac 0 1; apply pars_cons_cong.
   done.
   done.
   apply _.
 Qed.

Lemma OTPre_t : ipdl_t [:: tag o; tag leak_base_o; tag leaky; tag leakC] OTPre.
  rewrite /OTPre /OTPreA /OTPreB /OTIdeal.
  repeat type_tac.
  perm_match.
Qed.
                          


  End OTPre.

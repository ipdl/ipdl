Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Permutation Lib.SeqOps.
Require Import Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Base Ipdl.Big Pars Lib.Set Typ Approx Lib.Dist.

(* This file proves that the construction
   m_i -> m_i xor F(k, i)

  can be used to realize a n-use secure channel from an
  n-use authenticated one. *)

(* The assumption on PRFs says that the values F(k, i)
   are indistinguishable from iid uniform, if the key k
   is not leaked. *)

Definition PRF0 {chan} {n} {a b} gen (f : a.-bv -> 'I_n -> b.-bv) (o : n.-tuple (chan (b.-bv))) :=
  k <- new a.-bv ;;
  pars [::
          k ::= Samp gen;
          \||_(i < n) ((o ## i) ::= (k <-- Read k ;; Ret (f k i)))].

Definition PRF1 {chan} {n} {b} (o : n.-tuple (chan (b.-bv))) :=
  pars [::
          \||_(i < n) ((o ## i) ::= Samp Unif)].

(* Similar to our CPA example, we have a network that 
   is parametrized by a leakage function (here, f). 
   In the authenticated case, the leakage function is
   the identity, while in the secure channel case,
   the leakage function returns (). Ohter leakage functions
   are certainly possible. *)

Definition Net {chan} {n} {t} {t'} (f : t -> t') (rcv send : n.-tuple (chan t)) (leak : n.-tuple (chan t')) (ok : n.-tuple (chan unit)) :=
  pars [::
          \||_(i < n) ((leak ## i) ::= (m <-- Read (rcv ## i) ;; Ret (f m)));
          \||_(i < n) ((send ## i) ::= (m <-- Read (rcv ## i) ;; _ <-- Read (ok ## i);; Ret m)) ].


Section OTP_PRF.
  Context {chan : Type -> Type}.
  Context (n a b : nat).
  Context (f : a.-bv -> 'I_n -> b.-bv) (gen : Dist a.-bv).
  Context (l : nat).
  Context e (Hf : forall (o : n.-tuple (chan b.-bv)), PRF0 gen f o =a_(l, e) PRF1 o).

  (* The definition of alice and bob are the same, since both perform the same operation (xor'ing with F(k, i). *)
  Definition OTP_prf_party
             (k : chan (a.-bv))
             (m : n.-tuple (chan (b.-bv)))
             (o : n.-tuple (chan (b.-bv))) := 
    pars [::
            \||_(i < n) ((o ## i) ::= (k <-- Read k ;; m <-- Read (m ## i) ;; Ret (m +t (f k i))))].

  Definition OTP_prf_K (k : chan (a.-bv)) := k ::= Samp gen.

  Definition OTP_prf_real (m o leak : n.-tuple (chan b.-bv)) (ok : n.-tuple (chan unit)) :=
    k <- new a.-bv ;;
    send <- newvec n @ b.-bv ;; 
    recv <- newvec n @ b.-bv ;;
    pars [::
            OTP_prf_K k;
            OTP_prf_party k m send;
            Net id send recv leak ok; (* Authenticated channel *)
            OTP_prf_party k recv o].
         

  (* In the ideal game, input gets copied to output, and the leakage channel returns (). *)
  Definition OTP_prf_ideal (m o : n.-tuple (chan b.-bv)) (leak ok : n.-tuple (chan unit)) :=
    pars [::
            \||_(i < n) ((leak ## i) ::= (_ <-- Read (m ## i);; Ret tt));
            \||_(i < n) ((o ## i) ::= (_ <-- Read (ok ## i) ;; copy (m ## i)))].
  (* The simulator generates uniform random leakages. *)
  Definition OTP_prf_sim (leakR : n.-tuple (chan b.-bv)) (okR leakI okI : n.-tuple (chan unit)) :=
    pars [::
            \||_(i < n) ((leakR ## i) ::= (_ <-- Read (leakI ## i) ;; Samp Unif));
            \||_(i < n) ((okI ## i) ::= copy (okR ## i))].
                                    
  (* Begin proof *)
  Definition OTP_prf_hybrid m (o : n.-tuple (chan b.-bv)) leak ok :=
    v <- newvec n @ b.-bv ;;
    send <- newvec n @ b.-bv ;; 
    recv <- newvec n @ b.-bv ;;
    pars [::
            PRF0 gen f v ;
            Outvec send (fun i => m <-- Read (m ## i) ;; v <-- Read (v ## i) ;; Ret (m +t v));
            Net id send recv leak ok;
            Outvec o (fun i => m <-- Read (recv ## i) ;; v <-- Read (v ## i) ;; Ret (m +t v))].


  (* This error term has the reduction embedded within it.
     Since the reduction is polytime-computable (just by
     inspection), we have that the real world and ideal world 
     are negligibly close. *)
            

  Theorem OTP_prf_security m o leak ok :
    OTP_prf_real m o leak ok =a_(l, comp_err e (n*4))
                                (leakI <- newvec n @ unit ;;
                                okI <- newvec n @ unit ;;
                                pars [::
                                        OTP_prf_ideal m o leakI okI;
                                        OTP_prf_sim leak ok leakI okI]).

    (* do hybrid *)
    etrans.
    instantiate (1 := OTP_prf_hybrid m o leak ok).
    symmetry.
    rewrite /OTP_prf_hybrid /PRF0.
    setoid_rewrite newPars.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 2.
    etransitivity.
    Intro => v; Intro => send; Intro => recv; Intro => c.
    swap_Outvec_at 0 0 1.
    rewrite pars_big_inline //=; simp_all.
    swap_tac 0 4.
    swap_Outvec_at 0 0 1.
    rewrite pars_big_inline //=; simp_all.
    apply EqRefl.
    simpl.
    setoid_rewrite (newvec_newvec) at 1.
    setoid_rewrite (newvec_newvec) at 2.
    setoid_rewrite New_newvec at 1.
    swap_tac 0 1.
    setoid_rewrite pars_big_remove.
    rewrite /OTP_prf_real.

    setoid_rewrite New_newvec at 1.
    setoid_rewrite New_newvec at 1.
    Intro => k.
    Intro => send.
    Intro => recv.
    swap_tac 0 1.
    swap_tac 1 3.
    align.
    rewrite /OTP_prf_party /Outvec.
    rewrite pars1.
    done.
    rewrite /OTP_prf_party pars1 //=.
    apply _.

    atrans.
    rewrite /OTP_prf_hybrid.
    apply AEq_newvec => v.
    apply AEq_newvec => send.
    apply AEq_newvec => recv.
    arewrite (Hf v).
    apply AEq_zero; apply EqRefl.
    done.

    etrans.
    Intro => vs.
    Intro => send.
    Intro => recv.
    rewrite /PRF1 /Net.
    setoid_rewrite pars1; simpl.
    swap_tac 0 2.
    rewrite pars_pars; simpl.

    swap_tac 1 2.
    rewrite pars_big_inline; last by done.
    simp_all.
    swap_tac 0 2.
    rewrite pars_big_inline; last by done.
    simp_all.
    swap_tac 0 4.
    swap_tac 1 4.
    rewrite pars_big_inline; last by done. 
    simp_all.

    etransitivity.
    focus_tac 0.
    apply Eq_Outvec => j.
    apply EqBind_r => x.
    r_swap 1 2.
    rewrite EqReadSame.
    apply EqBind_r => v.
    apply EqBind_r => y.
    rewrite xortA xortK xort0.
    apply EqRxnRefl.

    swap_Outvec_at 0 0 1.
    swap_tac 1 3.
    rewrite -pars_big_mkdep; last by done.
    done.

    simpl.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 3.
    setoid_rewrite pars_big_remove.
    swap_tac 0 3.
    setoid_rewrite pars_big_remove.
    etrans.
    etransitivity.
    Intro => x.
    swap_Outvec_at 0 0 1.
    apply EqRefl.
    simpl.
    swap_tac 1 2.
    rewrite pars_big_fold.
    done.

    symmetry.
    swap_tac 0 2.
    setoid_rewrite pars_pars; simpl.
    swap_tac 0 2.
    setoid_rewrite pars_big_fold.
    swap_tac 0 1.
    swap_tac 1 2.
    setoid_rewrite pars_big_fold.
    apply AEq_zero.
    align.
    apply EqProt_big_r => j _ _.
    apply EqCongReact.
    simp_rxn.
    symmetry; r_swap 0 1.
    apply EqBind_r => x.
    symmetry.
    apply EqSampBijection.
    apply xort_inj_l.
    apply uniform_Unif.
    apply Eq_Outvec => j.
    rewrite /copy.
    simp_rxn.
    r_swap 0 1; done.
    rewrite !add_err0.
    rewrite !addn0.
    rewrite -!mulnDl.
    rewrite muln1.
    rewrite addnn -muln2.
    rewrite -mulnSr addnC -mulnSr //=.
Qed.


  (* Some sanity checks on the typing *)
  Lemma OTP_prf_real_t m o leak ok :
    ipdl_t (tags o ++ tags leak) (OTP_prf_real m o leak ok).
    rewrite /OTP_prf_real /OTP_prf_K /Net /OTP_prf_party.
    repeat type_tac.
    rewrite !map_tag_enum.
    rewrite !catA.
    setoid_rewrite (cons_catE (tag c)) at 1.
    setoid_rewrite (cons_catE (tag c)) at 3.
    rewrite !catA.
    perm_tac.
 Qed.

  Lemma OTP_prf_sim_t leak ok leakI okI:
    ipdl_t (tags leak ++ tags okI) (OTP_prf_sim leak ok leakI okI).
    rewrite /OTP_prf_sim.
    repeat type_tac.
    rewrite !map_tag_enum.
    done.
  Qed.

End OTP_PRF.

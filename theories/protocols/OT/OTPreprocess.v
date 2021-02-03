
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Pars Big.
Require Import OTIdeal Typing Lib.Set.

Open Scope bool_scope.

Lemma new_pars_undep {t1 t2} (c2 : chan t2) (rs : chan t1 -> seq rset) r r' :
    Forall (In (rxn_inputs r')) (rxn_inputs r) ->
  (c1 <- new t1 ;; pars [:: Out c2 (_ <-- Read c1 ;; r'), Out c1 r & rs c1]) =0
  (c1 <- new t1 ;; pars [:: Out c2 (r'), Out c1 r & rs c1]) .
  intros.
  apply EqNew => c1 _ _ .
  apply pars_undep.
  done.
Qed.
                                                                             
Section OTPre.
  (* OT Channels *)
  Context (L : nat) (m : chan (L ** L)) (i : chan TBool) (o : chan L).

  (* Leakage channels for B *)
  Context (leakC : chan TBool) (leak_base_o : chan L) (leaky : chan (L ** L)).

  Definition chans_ok := 
             Uniq [:: m; leaky] /\
             Uniq [:: o; leak_base_o] /\
             Uniq [:: leakC; i].

  Definition OTPreA (base_m : chan (L ** L)) (y : chan (L ** L)) (z : chan TBool) :=
    k <- new (L ** L) ;;
    pars [::
            Out k (Unif _);
            Out base_m (copy k);
            Out y (
                  m01 <-- Read m ;;
                  k01 <-- Read k ;;
                  z <-- Read z ;;
                  Ret ([pair i => (m01 # i) +t (k01 # (i (+) z)) ] : L ** L )) ].

               
  Definition OTPreB (base_i : chan TBool) (base_o : chan L) (y : chan (L ** L)) (z : chan TBool) :=
    c <- new TBool ;;
    pars [::
            Out c (Unif _) ;
            Out leakC (copy c) ;
            Out base_i (copy c) ;
            Out leak_base_o (copy base_o) ;
            Out z (
                  i <-- Read i ;;
                  c <-- Read c ;;
                  Ret (i (+) c : TBool) );
            Out leaky (copy y); 
            Out o (
                  b <-- Read i ;;
                  y01 <-- Read y ;;
                  k_c <-- Read base_o ;;
                  Ret (((y01 # b) +t k_c) : L) ) ].

            
(* ******     *)
  
  Definition OTPre_Sim (leako : chan L) 
    :=
  j <- new L ;;
  pars [::
          Out leaky (
            j <-- Read j ;;
            i <-- Read i ;;
            o <-- Read leako ;;
            x <-- Unif L ;;
            Ret (
                if i then {{ x, o +t j : L }} else {{ o +t j : L, x }} ) );
          Out leakC (Unif _) ;
          Out j (Unif _) ;
          Out leak_base_o (copy j) 
          ].

  Lemma OTPre_sim_t leako :
    chans_ok ->
    Uniq [:: leakC; i] ->
    Uniq [:: leako; o; leak_base_o ] ->
    (OTPre_Sim leako) ::: [:: mkChan i; mkChan leako ] --> [:: mkChan leaky; mkChan leakC; mkChan leak_base_o ].
    rewrite /chans_ok.
    intros; simpl in *.
    repeat type_tac.
    move: H15.
    instantiate (1 := [:: leak_base_o; leako ]).
    repeat type_tac. 
    repeat type_tac. 
    repeat type_tac. 
  Qed.

  Definition OTPre :=
    y <- new (L ** L) ;;
    z <- new TBool ;;
    base_i <- new TBool ;;
    base_o <- new L ;;
    base_m <- new (L ** L) ;;
    pars [::
            OTPreA base_m y z;
            OTPreB base_i base_o y z;
            OTIdeal _ base_i base_m base_o ].

  Lemma OTPre_eq :
    OTPre =0
             (leako <- new L ;;
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
    setoid_rewrite (NewNew (L ** L) (L ** L)).
    setoid_rewrite (NewNew (L ** L) TBool) at 2.
    swap_tac 0 10.
    under_new swap_at 0 0 1.
    swap_tac 1 7.
    setoid_rewrite pars_fold.
    swap_tac 0 1.
    swap_tac 0 2.
    setoid_rewrite (NewNew L (L ** L)).
    setoid_rewrite (NewNew L TBool).
    under_new rewrite new_pars_inline; [ apply EqRefl | done].
    under_new simp_at 0.
    swap_tac 0 5.
    under_new swap_at 0 0 2.
    setoid_rewrite pars_fold.
    under_new simp_at 0.
    under_new swap_at 0 0 1.
    setoid_rewrite (NewNew TBool (L ** L)).
    setoid_rewrite (NewNew TBool TBool).
    under_new rewrite new_pars_inline; [ apply EqRefl | done].
    swap_tac 0 4.
    under_new swap_at 0 0 1.
    setoid_rewrite pars_fold.
    setoid_rewrite (NewNew (L ** L) TBool).
    setoid_rewrite (NewNew (L ** L) (L ** L)).
    setoid_rewrite (NewNew (L ** L) TBool).
    swap_tac 0 2.
    swap_tac 1 5.
    under_new rewrite new_pars_inline; [ apply EqRefl | done].
    under_new simp_at 0.
    swap_tac 0 3.
    under_new swap_at 0 0 3.
    setoid_rewrite pars_fold.
    under_new simp_at 0.
    setoid_rewrite (NewNew TBool (L ** L)).
    setoid_rewrite (NewNew TBool TBool).
    swap_tac 1 4.
    under_new swap_at 0 0 2.
    under_new rewrite new_pars_inline; [ apply EqRefl | done].
    under_new simp_at 0.
    swap_tac 0 2.
    under_new swap_at 0 0 2.
    setoid_rewrite pars_fold.
    under_new simp_at 0.
    swap_tac 0 1.
    apply EqNew => c _ _.
    apply EqNew => d _ _.
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
                       Ret (if x_i then x_m.`2 else x_m.`1)).
        simpl.
        destruct (x_i), x_d; simpl; rewrite xortA xortK xort0; done.
        apply EqRefl.
        apply _.
        apply _.
   swap_tac 1 5.
   under_new swap_at 0 0 1.
   under_new rewrite new_pars_undep; [ apply EqRefl | rewrite //= ].
   rewrite NewNew.
   swap_tac 1 4.
   under_new swap_at 0 0 2.
   under_new rewrite new_pars_undep; [ apply EqRefl | rewrite //= ].
   (* Rerandomize c1 *)
   etransitivity.
        apply EqNew => c _ _.
        swap_tac 0 1.
        swap_tac 1 4.
        etransitivity.
        apply EqNew => c1 _ _.
        rewrite -pars_undep; last first.
        simpl; done.
        apply pars_cons_cong.
        instantiate ( 1 := 
                       Out c1 (b <-- Read c ;;
                               x <-- Unif L ;;
                               y <-- Unif L ;;
                               Ret (if b then {{ y, x }} else {{ x, y }} ))).
        apply EqOut.
        apply EqBind_r => x.
        destruct x.
        r_swap 0 1.
        done.
        done.
        done.

        under_new swap_at 0 0 1.
        setoid_rewrite <- pars_fold at 1.
        under_new swap_at 0 0 2.
        setoid_rewrite <- pars_fold at 1.
        swap_tac 0 1.
        swap_tac 0 5.
        under_new swap_at 0 0 1.
        setoid_rewrite (NewNew (L ** L) L) at 1.
        setoid_rewrite (NewNew (L ** L) L) at 1.
        unfold copy.
        under_new simp_at 0.
        under_new rewrite new_pars_inline; [ apply EqRefl | done].
        under_new simp_at 0.
        swap_tac 0 7.
        under_new swap_at 0 0 3.
        setoid_rewrite pars_fold at 1.
        under_new simp_at 0.

        (* now inline the new defs *)
        etransitivity.
        apply EqNew => c0 _ _.
        apply EqNew => c1 _ _.
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
        rewrite pars_undep; last first.
            simpl; done.
        swap_tac 1 4. 
        rewrite pars_undep; last first.
            simpl; done.
        apply EqRefl.
        swap_tac 0 6.
        setoid_rewrite pars_fold at 1.

        (* Now rerandomize leaky *)
        apply EqNew => c0 _ _.
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
                       x <-- Unif L ;;
                       Ret (if xi then _ else _ )).
        simpl.
        destruct xc.
        rewrite addbT negbK.
        destruct xi; simpl.
        symmetry.
        instantiate (1 := (x, xm.2 +t xc0)).
        by rewrite (EqBind_r_samp_bijection _ _ _ (fun (x : L) => xm.1 +t x : L)) //= ; apply xort_inj_l.
        instantiate (1 := (xm.1 +t xc0, x)).
        symmetry.
        by rewrite (EqBind_r_samp_bijection _ _ _ (fun (x : L) => xm.2 +t x : L)) //= ; apply xort_inj_l.
        destruct xi; simpl.
        symmetry.
        by rewrite (EqBind_r_samp_bijection _ _ _ (fun (x : L) => xm.1 +t x : L)) //= ; apply xort_inj_l.
        symmetry.
        by rewrite (EqBind_r_samp_bijection _ _ _ (fun (x : L) => xm.2 +t x : L)) //= ; apply xort_inj_l.
        swap_tac 1 3.
        rewrite pars_undep; last first.
        simpl; done.
        apply EqRefl.
        rewrite NewNew.
        swap_tac 0 2.
        setoid_rewrite pars_fold.

   (****  Now working on ideal world ****)
   symmetry.
   unfold OTIdeal, OTPre_Sim.
   swap_tac 0 2.
   setoid_rewrite newPars.
   setoid_rewrite pars_pars; simpl.
   setoid_rewrite (NewNew L L).
   under_new swap_at 0 0 2.
   swap_tac 1 4.
   setoid_rewrite pars_fold.
   under_new simp_at 0.
   apply EqNew => c _ _.
   symmetry; swap_tac 0 1; symmetry.

   (* Now matching up *)
   apply pars_cons_cong.
   apply EqOut.
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
   symmetry; apply EqOut; rewrite EqBindRet; done.
   swap_tac 0 1; apply pars_cons_cong.
   done.
   swap_tac 0 1; apply pars_cons_cong.
   done.
   done.
   apply _.
 Qed.

  (*

  Lemma OTPreA_t base_m y z :
    chans_ok ->
    Uniq [:: y; base_m; m] ->
    (OTPreA base_m y z) ::: [:: mkChan z; mkChan m] --> [:: mkChan base_m; mkChan y].
    intros.
    unfold chans_ok in *.
    simpl in *.
    repeat type_tac.
  Qed.

  Lemma OTPreB_t base_i base_o y z :
    chans_ok ->
    Uniq [:: base_o; leak_base_o; o] ->
    Uniq [:: y; leaky] -> 
    Uniq [:: z; i; base_i; leakC] ->
    (OTPreB base_i base_o y z) ::: [:: mkChan i; mkChan y; mkChan base_o] --> [:: mkChan leakC; mkChan base_i; mkChan leak_base_o; mkChan z; mkChan leaky; mkChan o].
    unfold chans_ok.
    intros; simpl in *.
    repeat type_tac.
  Qed.


  Lemma OTPre_t :
    chans_ok ->
    Uniq [:: o; leak_base_o] ->
    Uniq [:: i; leakC] ->
    OTPre ::: [:: mkChan i; mkChan m] --> [:: mkChan o; mkChan leaky; mkChan leakC; mkChan leak_base_o].
    intros; simpl in *.
    econstructor; intros.
    econstructor; intros.
    econstructor; intros.
    econstructor; intros.
    econstructor; intros.
    eapply par_t.
    apply OTPreA_t.
    simpl.
    done.
    simpl; unfold chans_ok in *; repeat type_tac.
    eapply par_t.
    apply OTPreB_t.
    done.
    simpl; unfold chans_ok in *; repeat type_tac.
    simpl; unfold chans_ok in *; repeat type_tac.
    simpl; unfold chans_ok in *; repeat type_tac.
    eapply par_t.
    repeat type_tac.
    repeat type_tac.
    repeat type_tac.
    done.
    done.
    unfold chans_ok in *; repeat type_tac.
    done.
    done.
    unfold chans_ok in *; repeat type_tac.
    done.
    done.
    instantiate (1 := fun x => _); simpl.
    handle_evar_set_eq.
    unfold chans_ok in *; repeat type_tac.
    instantiate (1 := fun x => _); simpl.
    handle_evar_set_eq.
    unfold chans_ok in *; repeat type_tac.
    instantiate (1 := fun x => _); simpl.
    handle_evar_set_eq.
    unfold chans_ok in *; repeat type_tac.
    instantiate (1 := fun x => _); simpl.
    handle_evar_set_eq.
    unfold chans_ok in *; repeat type_tac.
    instantiate (1 := fun x => _); simpl.
    handle_evar_set_eq.
    unfold chans_ok in *; repeat type_tac.
    instantiate (1 := fun x => _); simpl.
    handle_evar_set_eq.
    unfold chans_ok in *; repeat type_tac.
    instantiate (1 := fun x => _); simpl.
    handle_evar_set_eq.
    unfold chans_ok in *; repeat type_tac.
    instantiate (1 := fun x => _); simpl.
    handle_evar_set_eq.
    unfold chans_ok in *; repeat type_tac.
    repeat type_tac.
    unfold chans_ok in *; repeat type_tac.
    unfold chans_ok in *; repeat type_tac.
 Qed.

*)

  End OTPre.

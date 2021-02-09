Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Typing Lib.Set Lib.OrdLems.  

Definition thead_inhab {n} `{Inhabited 'I_n} {A} (v : n.-tuple A) : A.
  destruct n.
  destruct H; done.
  apply (thead v).
Defined.


Definition tlast_inhab {n} `{Inhabited 'I_n} {A} (v : n.-tuple A) : A.
  destruct n.
  destruct H; done.
  apply (tnth v ord_max).
Defined.

Definition ord0_inhab {n} `{Inhabited 'I_n} : 'I_n.
   destruct n.
   destruct H; done.
   apply ord0.
Defined.

Lemma val_ord0_inhab {n} `{Inhabited 'I_n} : val ord0_inhab = 0.
    rewrite /ord0_inhab.
    destruct n.
    simpl.
    destruct H.
    done.
    done.
Qed.

(*
   out[0] = in[0]
   out[n+1] = f(in[n+1], out[n])
*)

Definition cfold_body {n} {t t' : type} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t')  (init : t -> t') (ys : (n.+1).-tuple (chan t')) (i : 'I_(n.+1)) : rxn t'.
  destruct (ordP i).
  apply (x <-- Read (thead xs) ;; Ret (init x)).
  apply (x <-- Read (tnth xs i) ;; y <-- Read (tnth ys (widen_ord (leqnSn n) j)) ;; Ret (f y x)).
Defined.

Definition cfold {n} {t t' : type} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t')  (init : t -> t') (ys : (n.+1).-tuple (chan t')) :=
  \||_(i < n.+1) Out (tnth ys i) (cfold_body xs f init ys i).

Definition read_all {n} {t : type} (xs : (n.+1).-tuple (chan t)) :=
  cfold xs (fun _ _ => vtt) (fun _ => vtt).

Lemma cfold2_det_copy {n} {t t' : type} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t')  (init : t -> t') (ys1 ys2 : (n.+1).-tuple (chan t')) :
  pars [::
          cfold xs f init ys1; 
          cfold xs f init ys2 
                ] ~=
  pars [::
          cfold xs f init ys1; 
          copy_tup ys1 ys2].
  swap_tac 0 1.
  symmetry; swap_tac 0 1.
  apply pars_big_hybrid2.
  intros.
  rewrite /cfold_body.
  destruct (ordP k).
  subst.
  swap_tac 0 1. swap_tac 1 2.
  rewrite pars_inline_from_big.
  rewrite /cfold_body.
  simpl.
  align.
  apply EqOut; simp_rxn; done.
  done.
  done.

  subst.
  swap_tac 0 1.
  swap_tac 1 2.
  rewrite pars_inline_from_big //=.
  rewrite {1}/cfold_body //=.
  simp_at 0.
  have -> :
          (Ordinal (n:=n.+1) (m:=j.+1) (lift_subproof (n:=n.+1) 0 j)) = lift ord0 j.
  done.
  have -> : (widen_ord (m:=n.+1) (leqnSn n)
                       (Ordinal (n:=n) (m:=j)
                                (ltSS (lift_subproof (n:=n.+1) 0 j)))) =
            widen_ord (leqnSn n) j.
    apply/eqP; rewrite eqE //=.
  symmetry.
  swap_tac 0 1.
  swap_at 0 0 1.
  rewrite pars_inline_from_big //=.
  swap_at 0 0 1.
  apply pars_cons_cong.
  apply EqOut.
  rewrite /copy; simp_rxn; done.
  swap_tac 0 1.
  done.
Qed.

Lemma cfold_pointsTo {n} {t t' : type} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t')  (init : t -> t') (ys : (n.+1).-tuple (chan t')) (i : 'I_(n.+1)) :
  PointsTo _ (cfold xs f init ys) (tnth ys i)
           (
             match ordP i with
             | Ord0 _ _ => (x <-- Read (tnth xs i) ;; Ret (init x))
             | OrdS _ j _ =>
               (x <-- Read (tnth xs i) ;; y <-- Read (tnth ys (widen_ord (leqnSn n) j)) ;; Ret (f y x)) end).
  eapply pointsTo_big_ord.
  instantiate (1 := i).
  rewrite /cfold_body.

  destruct (ordP i).
  subst.
  econstructor.

  subst.
  econstructor.
Qed.


Lemma tupleP_r {A} {n} (v : (n.+1).-tuple A) : exists (h : A) (t : n.-tuple A),
    v = [tuple of rcons t h].
  exists (tnth v ord_max).
  exists (mktuple (fun j => tnth v (widen_ord (leqnSn n) j))).
  apply eq_from_tnth => j.
  destruct (ordP_r j).
  subst.
  rewrite /tnth.
  rewrite nth_rcons.
  simpl.
  rewrite size_map //=.
  rewrite size_enum_ord ltnn eq_refl //=.
  subst.
  rewrite /tnth.
  rewrite nth_rcons.
  simpl.
  rewrite size_map size_enum_ord.
  have -> : j < n by destruct j.
  erewrite nth_map.
  instantiate (1 := j).
  rewrite -val_ord_tuple.
  have -> : nth j (val (ord_tuple n)) j = j.
  have h := (tnth_ord_tuple j).
  rewrite /tnth in h.
  rewrite -{3}h.
  apply set_nth_default.
  rewrite val_ord_tuple size_enum_ord.
  destruct j; done.
  done.
  rewrite size_enum_ord.
  destruct j; done.
Qed.

Lemma ltSS (i j : nat) :
  (i.+1 < j.+1) = (i < j).
  done.
Qed.

Lemma cfoldS_r {n} {t t' : type} (xs : (n.+1).-tuple (chan t)) x (f : t' -> t -> t') init (ys : (n.+1).-tuple (chan t')) y :
  cfold [tuple of rcons xs x] f init [tuple of rcons ys y] ~=
  pars [::
          cfold xs f init ys;
          Out y (
                x <-- Read x ;;
                y <-- Read (tnth ys ord_max) ;;
                Ret (f y x))].
  rewrite /cfold.
  rewrite bigpar_ord_recr.
  rewrite -pars2.
  swap_tac 0 1.
  apply pars_cons_cong.
  apply EqProt_big_r; intros.
  apply eq_EqRefl.
  have -> :
    (tnth [tuple of rcons ys y] (widen_ord (m:=n.+2) (leqnSn n.+1) x0)) =
    tnth ys x0.
  rewrite /tnth.
  rewrite nth_rcons.
  simpl.
  rewrite size_tuple.
  have -> : x0 < n.+1.
  destruct x0; done.
  apply set_nth_default.
  rewrite size_tuple.
  have -> //= : x0 < n.+1.
  destruct x0; done.
  congr (_ _ _).
  rewrite /cfold_body.
  destruct (ordP x0).
  subst.
  rewrite //=.
  have -> : thead [tuple of rcons xs x] = thead xs.
     rewrite /thead /tnth nth_rcons //=.
     rewrite size_tuple //=.
     apply set_nth_default.
     rewrite size_tuple //=.
  done.
  subst.
  rewrite //=.
  rewrite /tnth nth_rcons //=.
  rewrite size_tuple.
  rewrite ltSS.
  have -> : j < n by destruct j.

  have -> : (nth
       (tnth_default [tuple of rcons xs x]
          (Ordinal (n:=n.+2) (m:=j.+1)
                   (widen_ord_proof (m:=n.+2) (lift ord0 j) (leqnSn n.+1)))) xs j.+1)
              = nth (tnth_default xs (lift ord0 j)) xs j.+1.
    apply set_nth_default.
    rewrite size_tuple ltSS; by destruct j.
    have -> :
      (nth
       (tnth_default [tuple of rcons ys y]
          (widen_ord (m:=n.+2) (leqnSn n.+1)
             (Ordinal (n:=n.+1) (m:=j)
                (OrdLems.ltSS
                   (widen_ord_proof (m:=n.+2) (lift ord0 j) (leqnSn n.+1)))))) (rcons ys y) j)
      =
      nth (tnth_default ys (widen_ord (leqnSn n) j)) ys j.
    rewrite nth_rcons.
    rewrite size_tuple.
    have -> : j < n.+1.
    eapply leq_trans.
    instantiate (1 := n).
    by destruct j.
    done.
  apply set_nth_default.
  rewrite size_tuple.
    eapply leq_trans.
    instantiate (1 := n).
    by destruct j.
    done.
    done.
  apply pars_cons_cong.
  rewrite /tnth.
  rewrite nth_rcons.
  simpl.
  rewrite size_tuple ltnn eq_refl.
  rewrite /cfold_body //=.
  rewrite /tnth nth_rcons //= size_tuple ltnn eq_refl //=.
  rewrite nth_rcons size_tuple.
  rewrite ltnS //= leqnn.
  have -> :
    (nth
          (tnth_default [tuple of rcons ys y]
             (widen_ord (m:=n.+2) (leqnSn n.+1)
                        (Ordinal (n:=n.+1) (m:=n) (OrdLems.ltSS (ltnSn n.+1))))) ys n) =
    (nth (tnth_default ys ord_max) ys n).
  apply set_nth_default.
  rewrite size_tuple ltnS leqnn //=.
  done.
  done.
Qed.

Lemma new_cfold_remove {n} {t t' : type} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t') init rs :
  (forall j, In (pars rs) (mkChan (tnth xs j))) ->
  ys <- newvec n.+1 @ t' ;;
  pars [::
          cfold xs f init ys & rs] ~= pars rs.
  intros.
  induction n.
  simpl.
  rewrite /cfold.
  etransitivity.
  apply EqNew => c _ _.
  rewrite big_ord_recl big_ord0 -eq_par0.
  rewrite /cfold_body //=.
  apply EqRefl.
  apply new_pars_remove.
  intros.
  simpl in H0.
  set_tac.
  apply H.


  rewrite newvecS_r.
  destruct (tupleP_r xs).
  destruct H0.
  subst.
  etransitivity.
  apply EqNew => c _ _.
  apply EqNew_vec => tup _ _.
  rewrite cfoldS_r.
  rewrite pars_pars //=.
  swap_tac 0 1; rewrite SeqOps.insert_0.
  apply EqRefl.
  rewrite -New_newvec.
  under_new rewrite new_pars_remove; last first; [ intro; repeat set_tac | apply EqRefl].
  left.
  eapply In_big.
  done.
  right.
  done.
  rewrite mem_index_enum //=.
  right.
  move: (H ord_max).
  rewrite /tnth nth_rcons //=.
  rewrite size_tuple ltnn eq_refl //=.
  apply IHn.
  intros.
  have -> : tnth x0 j = tnth [tuple of rcons x0 x] (widen_ord (leqnSn n.+1) j).
  rewrite /tnth nth_rcons //=.
  rewrite size_tuple.
  have -> : j < n.+1 by destruct j.
  apply set_nth_default.
  rewrite size_tuple; by destruct j.

  apply H.
Qed.

Lemma tnth_rcons_ord_max {n} {A} (xs : n.-tuple A) x :
  tnth [tuple of rcons xs x] ord_max = x.
  rewrite /tnth nth_rcons //=.
  rewrite size_tuple ltnn eq_refl //=.
Qed.

Lemma tnth_rcons_widen_ord {n} {A} (xs : n.-tuple A) x (i : 'I_n) :
  tnth [tuple of rcons xs x] (widen_ord (leqnSn n) i) = tnth xs i.
  rewrite /tnth nth_rcons //=.
  rewrite size_tuple.
  have -> : i < n by destruct i.
  apply set_nth_default.
  rewrite size_tuple; destruct i; done.
Qed.

Lemma pars_undep_cfold_input {t t' t'' : type} {n} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t') init ys (a : chan t'') r (i : 'I_(n.+1)) rs :
  pars [::
          Out a (_ <-- Read (tnth xs i) ;; _ <-- Read (tnth ys ord_max) ;; r),
          cfold xs f init ys & rs ] ~=
  pars [::
          Out a (_ <-- Read (tnth ys ord_max) ;; r),
          cfold xs f init ys & rs ].
  rewrite (pars_split 2) //= take0 drop0.
  symmetry; rewrite (pars_split 2) //= take0 drop0; symmetry.
  apply EqCong; last by done.
  etransitivity.
    edit_tac 0.
    r_swap 0 1.
    done.
  move: r.
  induction n; intros.
  rewrite pars_inline_from_big.
  rewrite {1}/cfold_body //=.
  symmetry.
  rewrite pars_inline_from_big.
  rewrite {1}/cfold_body //=.
  apply pars_cons_cong.
  apply EqOut.
  simp_rxn.
  symmetry; simp_rxn; symmetry.
  have -> : i = ord0.
    apply/eqP; rewrite eqE //=.
    destruct i.
    destruct m; done.
  rewrite EqReadSame.
  done.
  done.
  done.
  done.
  done.
  done.

  destruct (tupleP_r xs) as [xs_last [xs' H]]; subst.
  destruct (tupleP_r ys) as [ys_last [ys' H]]; subst.
  rewrite !tnth_rcons_ord_max.
  rewrite !cfoldS_r.
  swap_tac 0 1.
  rewrite pars_pars //=.
  symmetry.
    swap_tac 0 1.
    rewrite pars_pars //=.
  symmetry.
  inline_tac (Out a) (Out ys_last).
  simp_all.
  symmetry.
    inline_tac (Out a) (Out ys_last).
    etransitivity.
    edit_tac 0.
    simp_rxn; done.
  symmetry.
  destruct (ordP_r i); subst.
  rewrite tnth_rcons_ord_max.
  align.
  apply EqOut.
  r_swap 1 2.
  rewrite EqReadSame //=.

  rewrite tnth_rcons_widen_ord.
  etransitivity.
  edit_tac 0.
    r_swap 0 1.
    r_swap 1 2.
  done.

  swap_tac 1 2.
  rewrite (pars_split 2); simpl.
  rewrite IHn.
  rewrite -pars_cat //=.
  align.
  apply EqOut.
  r_swap 0 1.
  done.
Qed.
  

(*
Lemma In_xs_cfold {t t' : type} (xs : seq (chan t)) f init (o : chan t') x :
  In xs x -> In (cfold xs f init o) (mkChan x).
  move: f init o.
  induction xs; intros.
  rewrite //=.
  rewrite //=.
  intros.
  repeat set_tac.
  left.
  apply IHxs.
  done.
Qed.

Lemma Not_In_xs_cfold {t t' t'' : type} (xs : seq (chan t)) (f : t' -> t -> t') init (o : chan t') (x : chan t'') :
  ~ In (cfold xs f init o) (mkChan x) -> (~ In (map mkChan xs) (mkChan x)) /\ (mkChan x <> mkChan o).
  move: f init o.
  induction xs; intros.
  rewrite //=.
  repeat type_tac.
  repeat type_tac.
  move/IHxs: H1.
  repeat type_tac.
Qed.

Lemma cfold_t {t t' : type} (xs : seq (chan t)) f init (o : chan t') :
  ~ In (map mkChan xs) (mkChan o) ->
  (cfold xs f init o) ::: (map mkChan xs) --> [:: mkChan o].
  move: f init o.
  induction xs; intros.
  simpl.
  repeat type_tac.
  econstructor.
  repeat type_tac.
  apply IHxs.
  repeat type_tac.
  
  move/Not_In_xs_cfold: H3; repeat type_tac.
  move/Not_In_xs_cfold: H3; repeat type_tac.
  move/Not_In_xs_cfold: H3; repeat type_tac.
  repeat type_tac. 
  move/Not_In_xs_cfold: H4; repeat type_tac; intro; subst; done.
  move/Not_In_xs_cfold: H4; repeat type_tac; intro; subst; done.
  move/Not_In_xs_cfold: H4; repeat type_tac; intro; subst; done.
  intros; repeat type_tac.
Qed.

          
*)


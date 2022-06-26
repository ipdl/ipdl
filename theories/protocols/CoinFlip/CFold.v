Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Lib.OrdLems Typ.  

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

Section CFoldDefs.
  Context {chan : Type -> Type}.

Definition cfold_body {n} {t t'} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t')  (init : t -> t') (ys : (n.+1).-tuple (chan t')) (i : 'I_(n.+1)) : @rxn chan t'.
  destruct (ordP i).
  apply (x <-- Read (thead xs) ;; Ret (init x)).
  apply (x <-- Read (tnth xs i) ;; y <-- Read (tnth ys (widen_ord (leqnSn n) j)) ;; Ret (f y x)).
Defined.

Definition cfold {n} {t t'} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t')  (init : t -> t') (ys : (n.+1).-tuple (chan t')) :=
  \||_(i < n.+1) Out (tnth ys i) (cfold_body xs f init ys i).

Definition read_all {n} {t} (xs : (n.+1).-tuple (chan t)) :=
  cfold xs (fun _ _ => tt) (fun _ => tt).

Lemma cfold2_det_copy {n} {t t'} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t')  (init : t -> t') (ys1 ys2 : (n.+1).-tuple (chan t')) :
  pars [::
          cfold xs f init ys1; 
          cfold xs f init ys2 
                ] =p
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
  apply EqCongReact; simp_rxn; done.
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
  apply EqCongReact.
  rewrite /copy; simp_rxn; done.
  swap_tac 0 1.
  done.
Qed.

Lemma cfold_pointsTo {n} {t t'} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t')  (init : t -> t') (ys : (n.+1).-tuple (chan t')) (i : 'I_(n.+1)) :
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

Lemma bump0 i : bump 0 i = i.+1.
  done.
Qed.

Lemma cfold_DependsOn {n} {t t'} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t') (init : t -> t') (ys : (n.+1).-tuple (chan t')) (i j : 'I_(n.+1)) :
  j <= i ->
  DependsOn _ _ (cfold xs f init ys) (ys ## i) (xs ## j).
  move: j.
  induction i using ord_indP.
  intros.
  have: j = ord0.
  apply/eqP; rewrite eqE //=.
  rewrite leqn0 in H.
  done.
  intro; subst.
  eleft.
  apply cfold_pointsTo.
  simpl.
  left; done.
  intros.
  destruct n.
  destruct i; done.

  destruct (ordP j); subst.
  simpl in H; rewrite bump0 in H.
  eright; last first.
  apply IHi.
  done.
  eleft.
  apply cfold_pointsTo.
  simpl.
  right.
  intro; left.
  congr (_ _).
  congr (_ _).
  apply/eqP; rewrite eqE //=.

  case: (eqVneq i j); intro; subst.
  eleft.
  apply cfold_pointsTo.
  simpl.
  left; done.


  eright.
  eleft.
  eapply cfold_pointsTo.
  simpl.
  right; intro; left; done.
  have -> : widen_ord (m:=n.+2) (leqnSn n.+1)
                      (Ordinal (n:=n.+1) (m:=i) (ltSS (lift_subproof (n:=n.+2) 0 i))) =
             widen_ord (leqnSn n.+1) i.
  apply/eqP; rewrite eqE //=.
  apply IHi.
  simpl in *.
  rewrite !bump0 in H.
  rewrite bump0.
  rewrite ltn_neqAle.
  rewrite eq_sym i0 //=.
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

Lemma cfoldS_r {n} {t t'} (xs : (n.+1).-tuple (chan t)) x (f : t' -> t -> t') init (ys : (n.+1).-tuple (chan t')) y :
  cfold [tuple of rcons xs x] f init [tuple of rcons ys y] =p
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

Lemma new_cfold_remove {n} {t t'} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t') init rs :
  ys <- newvec n.+1 @ t' ;;
  pars [::
          cfold xs f init ys & rs] =p pars rs.
  intros.
  rewrite /cfold.
  Check pars_big_remove.
  rewrite /cfold_body.
  rewrite pars_big_remove_dep_vec //=.
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

Lemma pars_undep_cfold_input {t t' t''} {n} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t') init ys (a : chan t'') r (i : 'I_(n.+1)) rs :
  pars [::
          Out a (_ <-- Read (tnth xs i) ;; _ <-- Read (tnth ys ord_max) ;; r),
          cfold xs f init ys & rs ] =p
  pars [::
          Out a (_ <-- Read (tnth ys ord_max) ;; r),
          cfold xs f init ys & rs ].
  apply pars_DependsOn_undep.
  apply DependsOn_par_l.
  apply cfold_DependsOn.
  destruct i.
  simpl.
  done.
Qed.

Lemma cfold_t {n} {t t'} (xs : (n.+1).-tuple (chan t)) (f : t' -> t -> t') init ys :
  ipdl_t (tags ys) (cfold xs f init ys).
  rewrite /cfold.
  repeat type_tac.
  rewrite map_tag_enum //=.
Qed.
End CFoldDefs.

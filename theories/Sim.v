
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Lib.Set Ipdl.Approx.  


(*
Inductive tlist_elm :=
| TChan : Type -> tlist_elm
| TVec : nat -> Type -> tlist_elm.                       

Definition tlist := list tlist_elm.
Fixpoint chans_of (t : tlist) : Type :=
  match t with
    | nil => unit
    | (TChan t0) :: ts => chan t0 * chans_of ts
    | (TVec n t0) :: ts => (n.-tuple (chan t0)) * chans_of ts
  end.

Fixpoint new_chans_of {t : tlist} (k : chans_of t -> ipdl) {struct t} : ipdl.
  destruct t.
  apply (k tt).
  simpl in k.
  destruct t.
  apply (New T (fun c => new_chans_of t0 (fun v => k (c, v)))).
  apply (newvec n T (fun v => new_chans_of t0 (fun v2 => k (v, v2)))).
Defined.

Instance NewLike_new_chans_of t : NewLike (@new_chans_of t).
    constructor.
    intros.
    induction t.
    done.
    simpl.
    destruct a.
    rewrite newComp.
    Intro => c.
    done.
    rewrite newComp.
    Intro => c.
    done.

    intros.
    induction t.
    apply H.
    destruct a.
    simpl; Intro => c.
    apply IHt.
    done.
    simpl; Intro => c.
    apply IHt.
    done.

    intros; induction t.
    simpl.
    done.
    simpl.
    destruct a.
    rewrite EqNewExch.
    Intro => x.
    apply IHt.
    rewrite -new_new.
    Intro => x.
    apply IHt.
Qed.

Fixpoint ENew_chans_of {t : tlist} (e : chans_of t -> err) {struct t} : err.
  destruct t.
  apply (e tt).
  destruct t.
  apply (ENew (fun c => ENew_chans_of t0 (fun v => e (c, v)))).
  apply (ENew_vec (fun v => ENew_chans_of t0 (fun v2 => e (v, v2)))).
Defined.

Lemma EqENew_vec {n} {t} (k1 k2 : n.-tuple (chan t) -> err) :
  (forall v, k1 v =e k2 v) -> ENew_vec k1 =e ENew_vec k2.
  induction n; simpl in *; intros.
  done.
  apply EqENew => c.
  apply IHn.
  done.
Qed.

Require Import Setoid Relation_Definitions Morphisms.

Add Parametric Morphism n t : (@ENew_vec n t)
  with signature (pointwise_relation _ EqErr ==> EqErr) as enew_vec_rel.                              
  intros; simpl in *; rewrite /pointwise_relation in H.
  apply EqENew_vec; done.
Qed.
                                

Add Parametric Morphism t : (@ENew_chans_of t)
  with signature (pointwise_relation _ EqErr ==> EqErr) as enew_chans_rel.                              
  intros; simpl in *.
  rewrite /pointwise_relation in H.
  induction t; rewrite //=.
  destruct a.
  apply EqENew => z.
  apply IHt.
  done.
  apply EqENew_vec.
  intros; apply IHt.
  done.
Qed.

Lemma AEq_new_chans_of t (k1 k2 : chans_of t -> ipdl) e :
  (forall v, k1 v =a_(e v) k2 v) ->
  (new_chans_of k1) =a_(ENew_chans_of e) (new_chans_of k2).
    induction t; intros.
    apply H.
    destruct a; simpl in *.
    apply AEq_new => c.
    apply IHt.
    done.
    apply AEq_newvec; intros.
    apply IHt.
    done.
Qed.

Lemma new_chans_of_commute {t1 t2} (k : chans_of t1 -> chans_of t2 -> ipdl) :
  new_chans_of (fun v1 => new_chans_of (fun v2 => k v1 v2)) =p
  new_chans_of (fun v1 => new_chans_of (fun v2 => k v2 v1)).
  move: t1 k; induction t2.
  rewrite //=.
  intros; simpl; destruct a; simpl in *.
  rewrite new_new.
  Intro => c.
  rewrite IHt2.
  done.
  rewrite new_newvec.
  Intro => v.
  rewrite IHt2.
  done.
Qed.

Definition simulates (e_int real_adv_int ideal_adv_int : tlist) (r : chans_of e_int -> chans_of real_adv_int -> ipdl) (i : chans_of e_int -> chans_of ideal_adv_int -> ipdl) e :=
  { Sim : _ | 
    forall c_ext c_adv,
      r c_ext c_adv =a_(e c_ext c_adv) (new_chans_of (fun c_i => pars [:: i c_ext c_i; Sim c_adv c_i])) }.

Definition sim_tr_err {ext rl mid} (sim : chans_of rl -> chans_of mid -> ipdl) (err1 : chans_of ext -> chans_of rl -> err) (err2 : chans_of ext -> chans_of mid -> err)  := 
                                                            (fun c_ext c_adv => EPlus (err1 c_ext c_adv)
    (ENew_chans_of (fun v : chans_of mid => EComp (err2 c_ext v) (sim c_adv v)))).

Lemma simulates_trans ext rl mid idl (R : chans_of ext -> chans_of rl -> ipdl) (Hyb : chans_of ext -> chans_of mid -> ipdl) (I : chans_of ext -> chans_of idl -> ipdl) err1 err2 
  (h : simulates _ _ _ R Hyb err1) : simulates _ _ _ Hyb I err2 -> simulates _ _ _ R I
                                                                 (sim_tr_err (proj1_sig h) err1 err2).
  intros.
  destruct h as [S1 H1].
  destruct X as [S2 H2].
  exists (fun c_adv c_i => new_chans_of (fun v_mid => pars [:: S1 c_adv v_mid; S2 v_mid c_i])).
  intros.
  eapply AEq_err_eq.
  atrans.
  apply H1.
  atrans.
  apply AEq_new_chans_of => v.
  arewrite (H2 c_ext v).
  apply AEq_zero.
  rewrite newPars.
  apply EqRefl.
  apply EqERefl.
  apply AEq_zero.
  setoid_rewrite pars_pars; simpl.
  rewrite new_chans_of_commute.
  apply newCong => c_idl.
  symmetry.
  swap_tac 0 1.
  rewrite newPars.
  apply newCong => vmid.
  rewrite pars_pars //=.
  align.
  done.
  done.
  rewrite adde0.
  setoid_rewrite adde0.
  setoid_rewrite pars1.
  simpl.
  done.
Qed.


*)

Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Base Ipdl.Big Pars Lib.Set.

Lemma mkChan_separated_chan (a : Chan) (t : type) : exists c : chan t, mkChan c <> a.
    destruct a as [t1 a].
    destruct (type_eq_dec t1 t); subst.
    destruct (chan_separated t a).
    exists x.
    intro h; inversion h.
    have: a = x.
    apply Eqdep.EqdepTheory.inj_pair2; done.
    congruence.
    destruct (exists_chan t).
    exists x.
    intro h; inversion h; congruence.
Qed.

Definition OTIdeal (L : type) (i : chan TBool) (m : chan (L ** L))
           (o : chan L) :=
  Out o (
        x_i <-- Read i ;;
        x_m <-- Read m ;;
        Ret (if x_i then x_m.`2 else x_m.`1)).

Definition OT14Ideal (L : type) (i : chan (TBool ** TBool))
           (m : chan ((L ** L) ** (L ** L)))
           (o : chan L) :=
  Out o (
        x <-- Read i ;;
        y <-- Read m ;;
        Ret (((y # x.1) # x.2))).

Definition withOT14 (L : type) (P : chan (TBool ** TBool) -> chan ((L ** L) ** (L ** L)) -> chan L -> rset) :=
  i <- new (TBool ** TBool) ;;
  m <- new ((L ** L) ** (L ** L)) ;;
  o <- new L ;;
  pars [:: OT14Ideal _ i m o; P i m o ].

Lemma withOT14_irrel (L : type) r :
  withOT14 L (fun _ _ _ => r) ~= r.
  rewrite /withOT14.
  setoid_rewrite pars_cons.
  setoid_rewrite <- newComp.
  setoid_rewrite <- newComp.
  setoid_rewrite <- newComp.
  rewrite pars1.
  apply Absorb.
  repeat set_tac.
  destruct (mkChan_separated_chan a (TBool ** TBool)) as [c Hc].
  destruct (mkChan_separated_chan a ((L ** L) ** (L ** L))) as [d Hd].
  specialize (H _ Hc _ Hd).
  destruct (mkChan_separated_chan a L).
  specialize (H _ H0).
  destruct H; done.
  intros; repeat set_tac.
  destruct (mkChan_separated_chan c (TBool ** TBool)) as [d Hd]; specialize (H _ Hd).
  destruct (mkChan_separated_chan c ((L ** L) ** (L ** L))) as [e He]; specialize (H _ He).
  destruct (mkChan_separated_chan c L) as [f Hf]; specialize (H _ Hf).
  repeat set_tac.
Qed.

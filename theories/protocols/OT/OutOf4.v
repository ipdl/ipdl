
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Pars Lib.Set.
Require Import OTIdeal.

Require Import Setoid Relation_Definitions Morphisms.
Close Scope bool_scope.

  Lemma samp_pair {chan} {t'} {t : finType} `{unif t} `{Inhabited t'} `{Inhabited t} (x : chan t') (c d : chan t) :
    pars [::
            Out c (_ <-- Read x ;; Samp (Unif));
         Out d (_ <-- Read x ;; Samp Unif)] =p
    e <- new (t * t) ;;
    pars [::
            Out e (_ <-- Read x ;; Samp Unif) ;
            Out c (_ <-- Read x ;; x <-- Read e ;; Ret (x.1));
            Out d (_ <-- Read x ;; x <-- Read e ;; Ret (x.2))].
    symmetry.
    simpl.
    etransitivity.
    Intro => e.
    edit_tac 0.
    rewrite /Unif_pair.
    setoid_rewrite EqSampBind.
    setoid_rewrite EqSampBind.
    instantiate (1 :=
                   x0 <-- (_ <-- Read x ;; Samp Unif) ;;
                   y <-- (_ <-- Read x ;; Samp Unif) ;;
                   Ret (x0, y)).
         symmetry; simp_rxn.
         r_swap 1 2.
         rewrite EqReadSame.
         setoid_rewrite EqSampRet.
         done.
    rewrite -pars_fold.
    Intro => c'.
    swap_at 0 0 1.
    rewrite -pars_fold.
    Intro => d'.
    do_inline; simp_all.
    do_inline; simp_all.
    
    simpl.
    swap_tac 0 3.
    rewrite -pars_mkdep //=; last by firstorder.
    swap_tac 0 4.
    swap_at 0 0 1.
    swap_tac 1 2.
    rewrite -pars_mkdep //=; last by firstorder.
    apply EqRefl.
    rewrite EqNewExch.
    setoid_rewrite EqNewExch at 2.
    swap_tac 0 3.
    setoid_rewrite new_pars_remove.
    swap_tac 0 2.
    setoid_rewrite pars_fold.
    swap_tac 0 2.
    rewrite pars_fold.
    align.
    apply EqCongReact; simp_rxn; r_swap 1 2; rewrite EqReadSame; setoid_rewrite EqBindRet; done.
    apply EqCongReact; simp_rxn; r_swap 1 2; rewrite EqReadSame; setoid_rewrite EqBindRet; done.
Qed.

  Lemma rerandomP {chan : Type -> Type} {L : nat} b (i : chan (bool * bool)%type) (c1 c2 : chan L.-bv) :
    pars [::
            Out c1 (_ <-- Read i ;; Samp Unif);
            Out c2 (_ <-- Read i ;; Samp Unif)
         ]
    =p
       c1' <- new L.-bv ;;
       c2' <- new L.-bv ;;
       pars [::
               Out c1' (Samp Unif);
               Out c2' (Samp Unif);
               Out c1 (i <-- Read i ;; x <-- Read c1' ;; y <-- Read c2' ;; Ret (if  (if b then i.1 else i.2) then x else y));
               Out c2 (i <-- Read i ;; x <-- Read c1' ;; y <-- Read c2' ;; Ret (if (if b then i.1 else i.2) then y else x))
                   ].
    rewrite samp_pair.
    etransitivity.
    Intro => e.
    edit_tac 0.
    instantiate (1 := 
                   (i <-- Read i ;; x <-- Samp Unif ;; y <-- Samp Unif ;;
                    Ret (if (if b then i.1 else i.2) then (x, y) else (y, x )))).
         apply EqBind_r => x.
         destruct x as [x0 x1]; simpl.
         destruct b.
         destruct x0.
         rewrite /Unif_pair EqSampBind; setoid_rewrite EqSampBind; setoid_rewrite EqSampRet; done.
         rewrite /Unif_pair EqSampBind; setoid_rewrite EqSampBind; setoid_rewrite EqSampRet.
         r_swap 0 1.
         done.
         destruct x1.
         rewrite /Unif_pair EqSampBind; setoid_rewrite EqSampBind; setoid_rewrite EqSampRet; done.
         rewrite /Unif_pair EqSampBind; setoid_rewrite EqSampBind; setoid_rewrite EqSampRet.
         r_swap 0 1.
         done.
    swap_at 0 0 1.
    rewrite -pars_fold.
    Intro => c1'.
    swap_at 0 0 2.
    rewrite -pars_fold.
    Intro => c2'.
    do_inline; simp_all.
    do_inline; simp_all.
    apply EqRefl.
    setoid_rewrite EqNewExch at 1.
    setoid_rewrite EqNewExch at 2.
    setoid_rewrite new_pars_remove.
    Intro => c1'.
    Intro => c2'.
    align.
        apply EqCongReact.
        r_swap 0 2.
        r_swap 1 3.
        rewrite EqReadSame.
        r_swap 1 2.
        apply EqBind_r => x.
        apply EqBind_r => y.
        apply EqBind_r => z.
        destruct x as [x0 x1]; destruct b; [ destruct x0 | destruct x1]; rewrite //=.

        apply EqCongReact.
        r_swap 0 2.
        r_swap 1 3.
        rewrite EqReadSame.
        r_swap 1 2.
        apply EqBind_r => x.
        apply EqBind_r => y.
        apply EqBind_r => z.
        destruct x as [x0 x1]; destruct b; [ destruct x0 | destruct x1]; rewrite //=.
Qed.

  Lemma rerandomP_rs {chan : Type -> Type} {L : nat} b (i : chan (bool * bool)%type) (c1 c2 : chan L.-bv) rs :
    pars [::
            Out c1 (_ <-- Read i ;; Samp Unif),
            Out c2 (_ <-- Read i ;; Samp Unif) & rs
         ]
    =p
       c1' <- new L.-bv ;;
       c2' <- new L.-bv ;;
       pars [::
               Out c1' (Samp Unif), 
               Out c2' (Samp Unif), 
               Out c1 (i <-- Read i ;; x <-- Read c1' ;; y <-- Read c2' ;; Ret (if  (if b then i.1 else i.2) then x else y)),
               Out c2 (i <-- Read i ;; x <-- Read c1' ;; y <-- Read c2' ;; Ret (if (if b then i.1 else i.2) then y else x)) & rs
                   ].
    rewrite (pars_split 2); simpl; rewrite take0 drop0.
    rewrite rerandomP.
    rewrite newComp.
    Intro => c.
    rewrite newComp.
    Intro => c'.
    rewrite -pars_cat //=.
Qed.

Lemma ot14_xort_subproof {t} (a b c : t.-tuple bool) :
    ((((a +t b) +t c) +t a) +t b)
              =
              (c +t (a +t a) +t (b +t b)).
  rewrite (xortC _ c).
  rewrite !xortA.
  congr (_ _).
  congr (_ _).
  rewrite (xortC b).
  rewrite xortA //=.
Qed.

Ltac rxn_intros_combine_reads :=
  lazymatch goal with
  | [ |- @EqRxn _ _ ?r1 _ ] =>
    lazymatch r1 with
    | @Bind _ _ _ ?c ?k =>
      lazymatch c with
      | Read ?ch =>
        find_read_in_rxn (k witness) ch
                         ltac:(fun p =>
                            lazymatch p with
                            | Some ?j => r_swap 1 (j.+1); rewrite EqReadSame; apply EqBind_r; intro; rxn_intros_combine_reads
                            | None => apply EqBind_r; intro; rxn_intros_combine_reads
                                                               end
                         )
      | _ => apply EqBind_r; intro; rxn_intros_combine_reads
      end                                      
    | _ => idtac
 end end.

      
Section OneOutOf4.
  Context (L : nat).
  Context {chan : Type -> Type}.
  Context (ot_i1 ot_i2 ot_i3 : chan bool).
  Context (ot_o1 ot_o2 ot_o3 : chan L.-bv).

  Context (ot14_m : chan ((L.-bv * L.-bv) * (L.-bv * L.-bv))).
  Context (ot14_i : chan (bool * bool)).
  Context (ot14_o : chan L.-bv).

  (* Leakage channels for bob *)
  Context (leak_ot_o1 leak_ot_o2 leak_ot_o3 : chan L.-bv).
  Context (leak_send : chan ((L.-bv * L.-bv) * (L.-bv * L.-bv))).

  Definition One4_sender (ot_m1 ot_m2 ot_m3 : chan (L.-bv * L.-bv)) (ready : chan unit) (send : chan ((L.-bv * L.-bv) * (L.-bv * L.-bv)))  :=
    s0 <- new L.-bv ;;
    s1 <- new L.-bv;;
    s2 <- new L.-bv;;
    s3 <- new L.-bv;;
    s4 <- new L.-bv;;
    s5 <- new L.-bv;;
    pars [::
            Out s0 (_ <-- Read ready;; Samp Unif);
            Out s1 (_ <-- Read ready;; Samp Unif);
            Out s2 (_ <-- Read ready;; Samp Unif);
            Out s3 (_ <-- Read ready;; Samp Unif);
            Out s4 (_ <-- Read ready;; Samp Unif);
            Out s5 (_ <-- Read ready;; Samp Unif);

            Out send (
                  m <-- Read ot14_m ;;
                  s0 <-- Read s0 ;; 
                  s1 <-- Read s1 ;; 
                  s2 <-- Read s2 ;; 
                  s3 <-- Read s3 ;; 
                  s4 <-- Read s4 ;; 
                  s5 <-- Read s5 ;; 
                  Ret (
                  let '((m0, m1), (m2, m3)) := m in
                  ( (s0 +t s2 +t m0,
                     s0 +t s3 +t m1),
                    (s1 +t s4 +t m2, s1 +t s5 +t m3))));
         Out ot_m1 (
               a <-- Read s0 ;;
               b <-- Read s1 ;;
               Ret (a, b) );
         Out ot_m2 (
               a <-- Read s2 ;;
               b <-- Read s3 ;;
               Ret (a, b) );
         Out ot_m3 (
               a <-- Read s4 ;;
               b <-- Read s5 ;;
               Ret (a, b) ) ].
               
  Definition One4_recv (ready : chan unit) (ot_i1 ot_i2 ot_i3 : chan bool) (ot_o1 ot_o2 ot_o3 : chan L.-bv) (send : chan ((L.-bv * L.-bv) * (L.-bv * L.-bv))) :=
    pars [::
            Out ready (_ <-- Read ot14_i ;; Ret tt);
            Out ot_i1 (
                  i <-- Read ot14_i ;; Ret (i.1));
            Out ot_i2 (
                  i <-- Read ot14_i ;; Ret (i.2));
            Out ot_i3 (
                  i <-- Read ot14_i ;; Ret (i.2));
            Out leak_send (copy send);
            Out leak_ot_o1 (copy ot_o1);
            Out leak_ot_o2 (copy ot_o2);
            Out leak_ot_o3 (copy ot_o3);
            Out ot14_o (
                  t <-- Read ot14_i ;;
                  a <-- Read send ;;
                  T0 <-- Read ot_o1 ;;
                  T1 <-- Read ot_o2 ;;
                  T2 <-- Read ot_o3 ;;
                  Ret (
                      let '((a0, a1), (a2, a3)) := a in
                      match t.1, t.2 with
                        | false, false => a0 +t T0 +t T1
                        | false, true => a1 +t T0 +t T1
                        | true, false => a2 +t T0 +t T2
                        | true, true => a3 +t T0 +t T2 
                                                    end))].

  Definition OT14_real_simpl :=
    c <- new L.-bv ;;
    c0 <- new L.-bv ;;
    c1 <- new L.-bv ;;
    c2 <- new L.-bv ;;
    c3 <- new L.-bv ;;
    c4 <- new L.-bv ;;
    [pars [:: Out ot14_o
              (x <-- Read ot14_i;; x_m <-- Read ot14_m;; Ret ((x_m # x.1) # x.2 : L.-bv));
            Out c2 (_ <-- Read ot14_i;; Samp Unif);
            Out c3 (_ <-- Read ot14_i;; Samp Unif);
            Out leak_send
              (x <-- Read ot14_m;;
               x0 <-- Read c;;
               x1 <-- Read c0;;
               x2 <-- Read c1;;
               x3 <-- Read c2;;
               x4 <-- Read c3;;
               x5 <-- Read c4;;
               Ret
                 (let
                  '(m0, m1, (m2, m3)) := x in
                   ( ( (x0 +t x2) +t m0, (x0 +t x3) +t m1),
                     ( (x1 +t x4) +t m2, (x1 +t x5) +t m3))));
            Out leak_ot_o3
              (x <-- Read c3;;
               x0 <-- Read c4;;
               x1 <-- Read ot14_i;; Ret (if x1 .2 then x0 else x));
            Out leak_ot_o2
              (x <-- Read c1;;
               x0 <-- Read c2;;
               x1 <-- Read ot14_i;; Ret (if x1 .2 then x0 else x));
            Out leak_ot_o1
              (x <-- Read c;;
               x0 <-- Read c0;;
               x1 <-- Read ot14_i;; Ret (if x1 .1 then x0 else x));
            Out c1 (_ <-- Read ot14_i;; Samp Unif);
            Out c4 (_ <-- Read ot14_i;; Samp Unif);
            Out c (_ <-- Read ot14_i;; Samp Unif);
            Out c0 (_ <-- Read ot14_i;; Samp Unif) ]].

  Definition OT14_real :=
    ot_i1 <- new bool ;;
    ot_i2 <- new bool ;;
    ot_i3 <- new bool ;;
    ot_m1 <- new (L.-bv * L.-bv) ;;
    ot_m2 <- new (L.-bv * L.-bv) ;;
    ot_m3 <- new (L.-bv * L.-bv) ;;
    ot_o1 <- new L.-bv ;;
    ot_o2 <- new L.-bv ;;
    ot_o3 <- new L.-bv ;;
    send <- new ((L.-bv * L.-bv) * (L.-bv * L.-bv)) ;;
    ready <- new unit ;;
    pars [::
            OTIdeal _ ot_i1 ot_m1 ot_o1;
            OTIdeal _ ot_i2 ot_m2 ot_o2;
            OTIdeal _ ot_i3 ot_m3 ot_o3;
            One4_sender ot_m1 ot_m2 ot_m3 ready send;
            One4_recv ready ot_i1 ot_i2 ot_i3 ot_o1 ot_o2 ot_o3 send ].
            
  Lemma ot14_simp : OT14_real =p OT14_real_simpl.
    etransitivity.
    repeat ltac:(apply EqCongNew; intro).
    rewrite /OTIdeal.
    rewrite /One4_sender.
    swap_tac 0 3.
    setoid_rewrite New_in_pars at 1.
    setoid_rewrite New_in_pars at 1.
    setoid_rewrite New_in_pars at 1.
    setoid_rewrite New_in_pars at 1.
    setoid_rewrite New_in_pars at 1.
    setoid_rewrite New_in_pars at 1.
    apply EqCongNew => s0.
    apply EqCongNew => s1.
    apply EqCongNew => s2.
    apply EqCongNew => s3.
    apply EqCongNew => s4.
    apply EqCongNew => s5.
    rewrite pars_pars; simpl.
    swap_tac 0 13.
    rewrite pars_pars; simpl.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    do_inline; simp_all.
    progress ltac:(do_inline; simp_all).
    progress ltac:(do_inline; simp_all).
    progress ltac:(do_inline; simp_all).
    progress ltac:(do_inline; simp_all).
    progress ltac:(do_inline; simp_all).
    progress ltac:(do_inline; simp_all).
    apply EqRefl.
    (* now we elim all the useless channels *)
    simpl.
    repeat setoid_rewrite (EqNewExch unit).
    under_new rewrite new_pars_remove; last first; apply EqRefl.
    simpl.
    repeat setoid_rewrite (EqNewExch ((L.-bv * L.-bv) * (L.-bv * L.-bv))).
    swap_tac 0 13.
    under_new rewrite new_pars_remove; last first; apply EqRefl.
    simpl.
    repeat setoid_rewrite (EqNewExch bool) at 3.
    swap_tac 0 1.
    under_new rewrite new_pars_remove; last first; apply EqRefl.
    repeat setoid_rewrite (EqNewExch bool) at 2.
    under_new rewrite new_pars_remove; last first; apply EqRefl.
    simpl.
    repeat setoid_rewrite (EqNewExch bool) at 1.
    swap_tac 0 10.
    under_new rewrite new_pars_remove; last first; apply EqRefl.
    simpl.
    repeat setoid_rewrite (EqNewExch (L.-bv * L.-bv)) at 3.
    swap_tac 0 12.
    under_new rewrite new_pars_remove; last first; apply EqRefl.
    simpl.
    repeat setoid_rewrite (EqNewExch (L.-bv * L.-bv)) at 2.
    swap_tac 0 10.
    under_new rewrite new_pars_remove; last first; apply EqRefl.
    simpl.
    repeat setoid_rewrite (EqNewExch (L.-bv * L.-bv)).
    swap_tac 0 8.
    under_new rewrite new_pars_remove; last first; apply EqRefl.

    simpl.
    swap_tac 0 10.
    setoid_rewrite (EqNewExch L.-bv) at 2.
    setoid_rewrite (EqNewExch L.-bv) at 3.
    setoid_rewrite (EqNewExch L.-bv) at 4.
    setoid_rewrite (EqNewExch L.-bv) at 5.
    setoid_rewrite (EqNewExch L.-bv) at 6.
    setoid_rewrite (EqNewExch L.-bv) at 7.
    setoid_rewrite (EqNewExch L.-bv) at 8.
    under_new rewrite new_pars_remove; last first; apply EqRefl.

    simpl.
    swap_tac 0 11.
    setoid_rewrite (EqNewExch L.-bv) at 1.
    setoid_rewrite (EqNewExch L.-bv) at 2.
    setoid_rewrite (EqNewExch L.-bv) at 3.
    setoid_rewrite (EqNewExch L.-bv) at 4.
    setoid_rewrite (EqNewExch L.-bv) at 5.
    setoid_rewrite (EqNewExch L.-bv) at 6.
    setoid_rewrite (EqNewExch L.-bv) at 7.
    under_new rewrite new_pars_remove; last first; apply EqRefl.

    simpl.
    swap_tac 0 9.
    setoid_rewrite (EqNewExch L.-bv) at 1.
    setoid_rewrite (EqNewExch L.-bv) at 2.
    setoid_rewrite (EqNewExch L.-bv) at 3.
    setoid_rewrite (EqNewExch L.-bv) at 4.
    setoid_rewrite (EqNewExch L.-bv) at 5.
    setoid_rewrite (EqNewExch L.-bv) at 6.
    under_new rewrite new_pars_remove; last first; apply EqRefl.

    (* Now do some final simpl *)
    etransitivity.
    repeat ltac:(apply EqCongNew; intro).
    edit_tac 7.
    etransitivity.
    rxn_intros_combine_reads.
    apply EqRxnRefl.
    etransitivity.
    rxn_intros_combine_reads.
    apply EqRxnRefl.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    apply EqBind_r; intros x_i.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    apply EqBind_r; intros x_m.
    instantiate (1 :=
                   fun x_m => _).
    simpl.
    instantiate (1 := Ret ((x_m # x_i.1) # x_i.2)).
    destruct x_m as [[m0 m1] [m2 m3]].
    simpl.
    destruct x_i as [i1 i2]; simpl.
    destruct i1, i2; simpl.

    rewrite ot14_xort_subproof !xortK !xort0 //=.
    rewrite ot14_xort_subproof !xortK !xort0 //=.
    rewrite ot14_xort_subproof !xortK !xort0 //=.
    rewrite ot14_xort_subproof !xortK !xort0 //=.

    swap_tac 0 7.
    swap_tac 1 10.
    rewrite -pars_mkdep //=; last by firstorder.
    swap_tac 1 9.
    rewrite -pars_mkdep //=; last by firstorder.
    swap_at 0 0 1.
    swap_tac 1 10.
    rewrite -pars_mkdep //=; last by firstorder.
    swap_at 0 0 1.
    swap_tac 1 2.
    rewrite -pars_mkdep //=; last by firstorder.
    swap_at 0 0 1.
    swap_tac 1 8.
    rewrite -pars_mkdep //=; last by firstorder.
    swap_at 0 0 1.
    swap_tac 1 7.
    rewrite -pars_mkdep //=; last by firstorder.
    apply EqRefl.
    apply EqRefl.
Qed.

  Definition mkpair4 {t} (f : bool -> bool -> t) : (t * t) * (t * t) :=
    ((f false false, f false true), (f true false, f true true)).

  Definition cflip {t} (p : t * t) (b : bool) : t * t :=
    if b then p else (p.2, p.1).

  Lemma bind_samp_xor {n : nat} {t} (a : n.-tuple bool) (k : n.-bv -> @rxn chan t) :
    EqRxn _ (x <-- Samp (Unif) ;; k x) (x <-- Samp Unif ;; k (x +t a)).
    apply EqBind_r_samp_bijection.
    apply is_unif.
    apply xort_inj_r.
  Qed.

  Definition OT14_real_rerandomize :=
    c <- new L.-bv;;
  c0 <- new L.-bv;;
  c1 <- new L.-bv;;
  [pars [:: Out leak_send
              (x <-- Read ot14_i;;
               x0 <-- Read c1;;
               x1 <-- Read c0;;
               x2 <-- Read c;;
               x3 <-- Read ot14_m;;
               x4 <-- Samp Unif;;
               x5 <-- Samp Unif;;
               x6 <-- Samp Unif;; 
               Ret
                 (let o := (x3 # x .1) # x .2 in
                  let o0 := if x .2 && x .1 then o else tzero _ in
                  let o1 := if ~~ x .2 && x .1 then o else tzero _ in
                  let o2 := if x .2 && ~~ x .1 then o else tzero _ in
                  let o3 := if ~~ x .2 && ~~ x .1 then o else tzero _ in
                  ( ( ((x2, x4) # x .1 +t (x0, x6) # x .2) +t o3 : L.-bv,
                    ((x2, x4) # x .1 +t (x6, x0) # x .2) +t o2 : L.-bv),
                  (((x4, x2) # x .1 +t (x1, x5) # x .2) +t o1 : L.-bv,
                  ((x4, x2) # x .1 +t (x5, x1) # x .2) +t o0 : L.-bv))));
            Out leak_ot_o1 (_ <-- Read ot14_i;; Read c);
            Out leak_ot_o3 (_ <-- Read ot14_i;; Read c0);
            Out leak_ot_o2 (_ <-- Read ot14_i;; y <-- Read c1;; Ret y);
            Out c1 (Samp Unif); Out c (Samp Unif);             Out ot14_o
              (x <-- Read ot14_i;; x0 <-- Read ot14_m;; Ret ((x0 # x.1) # x.2 : L.-bv));
            Out c0 (Samp Unif) ] ]. 


Lemma ot_simpl_rerandomize : OT14_real_simpl =p OT14_real_rerandomize.
    etransitivity.
    repeat ltac:(apply EqCongNew; intro).
    swap_tac 0 9.
    swap_tac 1 10.
    etransitivity.
    rewrite (rerandomP_rs true).
    repeat ltac:(apply EqCongNew; intro).
    repeat ltac:(do_inline; simp_all).
    edit_tac 8.
        r_swap 1 3.
        rewrite EqReadSame.
        r_swap 1 5.
        rewrite EqReadSame.
        apply EqBind_r => i.
        r_swap 1 2.
        rewrite !EqReadSame.
        apply EqBind_r => x.
        rewrite !EqReadSame.
        apply EqBind_r => y.
        instantiate (1 := fun y => Ret y).
        destruct i; simpl.
        destruct b; done.
   swap_tac 0 4.
   swap_tac 1 10.
    rewrite (rerandomP_rs false).
    repeat ltac:(apply EqCongNew; intro).
    repeat ltac:(do_inline; simp_all).
    edit_tac 8.
        r_swap 1 3.
        rewrite EqReadSame.
        r_swap 1 5.
        rewrite EqReadSame.
        apply EqBind_r => i.
        r_swap 1 2.
        rewrite !EqReadSame.
        apply EqBind_r => x.
        rewrite !EqReadSame.
        apply EqBind_r => y.
        instantiate (1 := fun y => Ret y).
        destruct i; simpl.
        destruct b0; done.
  swap_tac 0 11.
  swap_tac 1 14.
    rewrite (rerandomP_rs false).
    repeat ltac:(apply EqCongNew; intro).
    repeat ltac:(do_inline; simp_all).
    edit_tac 11.
        r_swap 1 3.
        rewrite EqReadSame.
        r_swap 1 5.
        rewrite EqReadSame.
        apply EqBind_r => i.
        r_swap 1 2.
        rewrite !EqReadSame.
        apply EqBind_r => x.
        rewrite !EqReadSame.
        apply EqBind_r => y.
        instantiate (1 := fun y => Ret y).
        destruct i; simpl.
        destruct b0; done.
  apply EqRefl.
  apply EqRefl.
  (* Now elim useless channels *)
  setoid_rewrite (EqNewExch L.-bv) at 1.
  setoid_rewrite (EqNewExch L.-bv) at 2.
  setoid_rewrite (EqNewExch L.-bv) at 3.
  setoid_rewrite (EqNewExch L.-bv) at 4.
  setoid_rewrite (EqNewExch L.-bv) at 5.
  setoid_rewrite (EqNewExch L.-bv) at 6.
  setoid_rewrite (EqNewExch L.-bv) at 7.
  setoid_rewrite (EqNewExch L.-bv) at 8.
  setoid_rewrite (EqNewExch L.-bv) at 9.
  setoid_rewrite (EqNewExch L.-bv) at 10.
  setoid_rewrite (EqNewExch L.-bv) at 11.
  swap_tac 0 6.
  under_new rewrite new_pars_remove; last first.
  apply EqRefl.

  
  setoid_rewrite (EqNewExch L.-bv) at 1.
  setoid_rewrite (EqNewExch L.-bv) at 2.
  setoid_rewrite (EqNewExch L.-bv) at 3.
  setoid_rewrite (EqNewExch L.-bv) at 4.
  setoid_rewrite (EqNewExch L.-bv) at 5.
  setoid_rewrite (EqNewExch L.-bv) at 6.
  setoid_rewrite (EqNewExch L.-bv) at 7.
  setoid_rewrite (EqNewExch L.-bv) at 8.
  setoid_rewrite (EqNewExch L.-bv) at 9.
  setoid_rewrite (EqNewExch L.-bv) at 10.
  swap_tac 0 6.
  under_new rewrite new_pars_remove; last first.
  apply EqRefl.
  

  setoid_rewrite (EqNewExch L.-bv) at 1.
  setoid_rewrite (EqNewExch L.-bv) at 2.
  setoid_rewrite (EqNewExch L.-bv) at 3.
  setoid_rewrite (EqNewExch L.-bv) at 4.
  setoid_rewrite (EqNewExch L.-bv) at 5.
  setoid_rewrite (EqNewExch L.-bv) at 6.
  setoid_rewrite (EqNewExch L.-bv) at 7.
  setoid_rewrite (EqNewExch L.-bv) at 8.
  setoid_rewrite (EqNewExch L.-bv) at 9.
  under_new rewrite new_pars_remove; last first.
  apply EqRefl.

  setoid_rewrite (EqNewExch L.-bv) at 1.
  setoid_rewrite (EqNewExch L.-bv) at 2.
  setoid_rewrite (EqNewExch L.-bv) at 3.
  setoid_rewrite (EqNewExch L.-bv) at 4.
  setoid_rewrite (EqNewExch L.-bv) at 5.
  setoid_rewrite (EqNewExch L.-bv) at 6.
  setoid_rewrite (EqNewExch L.-bv) at 7.
  setoid_rewrite (EqNewExch L.-bv) at 8.
  under_new rewrite new_pars_remove; last first.
  apply EqRefl.

  setoid_rewrite (EqNewExch L.-bv) at 1.
  setoid_rewrite (EqNewExch L.-bv) at 2.
  setoid_rewrite (EqNewExch L.-bv) at 3.
  setoid_rewrite (EqNewExch L.-bv) at 4.
  setoid_rewrite (EqNewExch L.-bv) at 5.
  setoid_rewrite (EqNewExch L.-bv) at 6.
  setoid_rewrite (EqNewExch L.-bv) at 7.
  under_new rewrite new_pars_remove; last first.
  apply EqRefl.
  
  setoid_rewrite (EqNewExch L.-bv) at 1.
  setoid_rewrite (EqNewExch L.-bv) at 2.
  setoid_rewrite (EqNewExch L.-bv) at 3.
  setoid_rewrite (EqNewExch L.-bv) at 4.
  setoid_rewrite (EqNewExch L.-bv) at 5.
  setoid_rewrite (EqNewExch L.-bv) at 6.
  under_new rewrite new_pars_remove; last first.
  apply EqRefl.


  (* Now undep the leaks *)
  etransitivity.
  repeat ltac:(apply EqCongNew; intro).
  swap_at 4 0 1.
  (* leak_ok_o3 *)
  swap_tac 0 4.
  swap_tac 1 7.
  rewrite -pars_mkdep //=.

  (* leak_ok_o2 *)
  swap_tac 0 5.
  swap_at 0 0 1.
  swap_tac 1 4.
  rewrite -pars_mkdep //=.

  (* leak_ot_o1 *)
  swap_tac 0 6.
  swap_at 0 0 1.
  swap_tac 1 2.
  rewrite -pars_mkdep //=.
  edit_tac 3.

    r_swap 1 3.
    r_swap 2 6.
    r_swap 3 9.
    r_swap 4 12.
    r_swap 5 15.
    rewrite !EqReadSame.
    apply EqBind_r => i.
    r_swap 1 2.
    rewrite !EqReadSame.
    apply EqBind_r => x.
    rewrite !EqReadSame.
    apply EqBind_r => y.
    r_swap 1 2.
    rewrite !EqReadSame.
    apply EqBind_r => z.
    rewrite !EqReadSame.
    apply EqBind_r => w.
    r_swap 1 2.
    rewrite !EqReadSame.
    apply EqBind_r => a.
    rewrite !EqReadSame.
    apply EqRxnRefl.
  apply EqRefl.

  (* Now fold in the samps *)
  simpl.
  setoid_rewrite (EqNewExch L.-bv) at 5.
  swap_tac 0 3.
  under_new swap_at 0 0 1.
  simpl.
  swap_tac 1 2.
  under_new rewrite pars_fold; [ apply EqRefl ].

  simpl.
  under_new swap_at 0 0 3.
  simpl.
  swap_tac 1 3.
  setoid_rewrite (EqNewExch L.-bv) at 3.
  setoid_rewrite (EqNewExch L.-bv) at 4.
  under_new rewrite pars_fold; [ apply EqRefl ].

  simpl.
  under_new swap_at 0 0 5.
  simpl.
  setoid_rewrite (EqNewExch L.-bv) at 1.
  setoid_rewrite (EqNewExch L.-bv) at 2.
  setoid_rewrite (EqNewExch L.-bv) at 3.
  swap_tac 1 2.
  under_new rewrite pars_fold; [ apply EqRefl ].

  (* Now simplify leak_send *)
  simpl.
  etransitivity.
  apply EqCongNew; intro.
  apply EqCongNew; intro.
  apply EqCongNew; intro.
  edit_tac 0.
    r_swap 0 3.
    r_swap 1 4.
    r_swap 2 5.
    r_swap 3 6.
    r_swap 4 7.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    instantiate (1 := fun x3 =>
                   x4 <-- Samp Unif ;;
                   x5 <-- Samp Unif ;;
                   x6 <-- Samp Unif ;;
                   Ret (
                       let o := (x3 # x.1) # x.2 in
                       let o0 := if x.2 && x.1 then o else tzero _ in
                       let o1 := if (~~ x.2) && x.1 then o else tzero _ in
                       let o2 := if (x.2) && (~~ x.1) then o else tzero _ in
                       let o3 := if (~~ x.2) && (~~ x.1) then o else tzero _ in
                       ( (
                              (x2, x4) # x.1 +t (x0, x6) # x.2 +t o3,
                              (x2, x4) # x.1 +t (x6, x0) # x.2 +t o2 ),
                         ( 
                              (x4, x2) # x.1 +t (x1, x5) # x.2 +t o1,
                              (x4, x2) # x.1 +t (x5, x1) # x.2 +t o0 )
                            ))).
    simpl.
    destruct x3 as [[m0 m1] [m2 m3]]; simpl.
    destruct x as [ [ | ] [ | ]]; simpl.

    rewrite (bind_samp_xor m1).
    apply EqBind_r => x.
    rewrite (bind_samp_xor m2).
    apply EqBind_r => y.
    rewrite (bind_samp_xor (m1 +t m0)).
    apply EqBind_r => z.
    rewrite (xortC _ x0).
    rewrite !xortA !xortK !xort0.
    rewrite (xortC m1) xortA xortK xort0.
    rewrite (xortC x0) //=.

    rewrite (bind_samp_xor m0).
    apply EqBind_r => x.
    rewrite (bind_samp_xor m3).
    apply EqBind_r => y.
    rewrite (bind_samp_xor (m0 +t m1)).
    apply EqBind_r => z.
    rewrite (xortC _ x0).
    rewrite !xortA !xortK !xort0.
    rewrite (xortC m0) xortA xortK xort0.
    rewrite (xortC x0) //=.

    rewrite (bind_samp_xor m3).
    apply EqBind_r => x.
    rewrite (bind_samp_xor (m3 +t m2)).
    apply EqBind_r => y.
    rewrite (bind_samp_xor m0).
    apply EqBind_r => z.
    rewrite !xortA !xortK !xort0.
    rewrite (xortC m3) xortA xortK xort0.
    rewrite (xortC m3) xortA xortK xort0 //=.

    rewrite (bind_samp_xor m2).
    apply EqBind_r => x.
    rewrite (bind_samp_xor (m3 +t m2)).
    apply EqBind_r => y.
    rewrite (bind_samp_xor m1).
    apply EqBind_r => z.
    rewrite !xortA !xortK !xort0.
    rewrite (xortC m3) xortA xortK xort0.
    rewrite (xortC m2) xortA xortK xort0 //=.
    rewrite (xortC m2) xortA xortK xort0 //=.
    apply EqRefl.

    rewrite /OT14_real_rerandomize.
    apply EqCongNew => c.
    apply EqCongNew => c1.
    apply EqCongNew => c2.
    align.
    apply EqCongReact; apply EqBind_r; intro; rewrite EqBindRet //=.
    apply EqCongReact; apply EqBind_r; intro; rewrite EqBindRet //=.
 Qed.

Definition OT14_sim (out : chan L.-bv) :=
c <- new L.-bv;;
c0 <- new L.-bv;;
c1 <- new L.-bv;;
[pars [:: Out leak_send
          (
            o <-- Read out ;;
            x <-- Read ot14_i;;
             x0 <-- Read c1;;
             x1 <-- Read c0;;
             x2 <-- Read c;;
             x4 <-- Samp Unif;;
             x5 <-- Samp Unif;;
             x6 <-- Samp Unif;;
             Ret
               (
                let o0 := if x .2 && x .1 then o else tzero L in
                let o1 := if ~~ x .2 && x .1 then o else tzero L in
                let o2 := if x .2 && ~~ x .1 then o else tzero L in
                let o3 := if ~~ x .2 && ~~ x .1 then o else tzero L in
                ((((x2, x4) # x .1 +t (x0, x6) # x .2) +t o3,
                  ((x2, x4) # x .1 +t (x6, x0) # x .2) +t o2),
                (((x4, x2) # x .1 +t (x1, x5) # x .2) +t o1,
                ((x4, x2) # x .1 +t (x5, x1) # x .2) +t o0))));
          Out leak_ot_o1 (_ <-- Read ot14_i;; Read c);
          Out leak_ot_o3 (_ <-- Read ot14_i;; Read c0);
          Out leak_ot_o2 (_ <-- Read ot14_i;; y <-- Read c1;; Ret y);
          Out c1 (Samp Unif); Out c (Samp Unif); 
          Out c0 (Samp Unif) ] ].

Lemma OT14_real_simE :
  OT14_real_rerandomize =p
                           o <- new L.-bv ;;
                           pars [::
                                   OT14Ideal _ ot14_i ot14_m ot14_o;
                                   OT14Ideal _ ot14_i ot14_m o;
                                   OT14_sim o ].
  symmetry.
  rewrite /OT14Ideal.
  rewrite /OT14_sim.
  swap_tac 0 2.
  repeat setoid_rewrite newPars.
  repeat setoid_rewrite pars_pars; simpl.
  etransitivity.
  repeat ltac:(apply EqCongNew; intro).
  do_inline; simp_all.
  apply EqRefl.
  setoid_rewrite (EqNewExch L.-bv) at 1.
  setoid_rewrite (EqNewExch L.-bv) at 2.
  setoid_rewrite (EqNewExch L.-bv) at 3.
  swap_tac 0 7.
  under_new rewrite new_pars_remove. apply EqRefl.
  rewrite /OT14_real_rerandomize.
  apply EqCongNew => c.
  apply EqCongNew => c0.
  apply EqCongNew => c1.
  swap_tac 0 6.
  apply pars_cons_cong.
  apply EqCongReact.
  r_swap 1 2.
  rewrite EqReadSame.
  apply EqBind_r; intro.
  r_swap 0 1.
  apply EqBind_r; intro.
  r_swap 0 1.
  apply EqBind_r; intro.
  r_swap 0 1.
  apply EqBind_r; intro.
  apply EqBind_r; intro.
  apply EqBind_r; intro.
  apply EqBind_r; intro.
  apply EqBind_r; intro.
  destruct x as [ [|] [|] ]; done.
  align.
  apply _.
  apply _.
  apply _.
Qed.

Definition OT14_sim_ideal :=
                           o <- new L.-bv ;;
                           pars [::
                                   OT14Ideal _ ot14_i ot14_m ot14_o;
                                   OT14Ideal _ ot14_i ot14_m o;
                                   OT14_sim o ].
  

Theorem OT14_security :
  OT14_real =p OT14_sim_ideal.
  rewrite ot14_simp.
  rewrite ot_simpl_rerandomize.
  rewrite OT14_real_simE.
  done.
Qed.

Require Import Permutation Typ Lib.SeqOps.

Definition ot14_chans := 
[:: tag ot14_o; tag leak_ot_o1; tag leak_ot_o2; tag leak_ot_o3; tag leak_send].

Lemma OT14_t : ipdl_t ot14_chans OT14_real. 
  rewrite /OT14_real /OTIdeal.
  rewrite /One4_sender /One4_recv.
  repeat type_tac.
  perm_match_step; rewrite insert_0.
  perm_match_step.
  perm_match_step.
  simpl in *.
  perm_match.
Qed.

Lemma OT14_sim_t o : ipdl_t [:: tag leak_send; tag leak_ot_o1; tag leak_ot_o3; tag leak_ot_o2] (OT14_sim o).
  rewrite /OT14_sim.
  repeat type_tac.
  perm_match.
Qed.

Lemma OT14_sim_ideal_t : ipdl_t ot14_chans OT14_sim_ideal.
  rewrite /OT14_sim_ideal.
  rewrite /OT14Ideal.
  repeat type_tac.
  apply OT14_sim_t.
  rewrite /ot14_chans.
  perm_match.
Qed.

End OneOutOf4.

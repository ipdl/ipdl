
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Pars Lib.Set.
Require Import OTIdeal.


Lemma rxn_inputs_unif t : rxn_inputs (Unif t) = nil.
  induction t; rewrite //=.
  rewrite IHt1 IHt2 //=.
Qed.

  Lemma samp_pair {t'} {t} (x : chan t') (c d : chan t) :
    pars [::
            Out c (_ <-- Read x ;; Unif t);
         Out d (_ <-- Read x ;; Unif t)] =0
                            e <- new (t ** t) ;;
    pars [::
            Out e (_ <-- Read x ;; Unif (t ** t)) ;
            Out c (_ <-- Read x ;; x <-- Read e ;; Ret (x.`1));
            Out d (_ <-- Read x ;; x <-- Read e ;; Ret (x.`2))].
    symmetry.
    simpl.
    etransitivity.
    apply EqNew => e _ _.
    edit_tac 0.
    instantiate (1 :=
                   x0 <-- (_ <-- Read x ;; Unif t) ;;
                   y <-- (_ <-- Read x ;; Unif t) ;;
                   Ret {{ x0, y }} ).
         symmetry; simp_rxn.
         r_swap 1 2; rewrite EqReadSame //=.
    rewrite -pars_fold.
    apply EqNew => c' _ _.
    swap_at 0 0 1.
    rewrite -pars_fold.
    apply EqNew => d' _ _.
    do_inline; simp_all.
    do_inline; simp_all.
    
    simpl.
    swap_tac 0 3.
    rewrite pars_undep //=; last first.
       apply Forall_forall; rewrite //=; repeat set_tac.
       rewrite rxn_inputs_unif in H; done.
    swap_tac 0 4.
    swap_at 0 0 1.
    swap_tac 1 2.
    rewrite pars_undep //=; last first.
       apply Forall_forall; rewrite //=; repeat set_tac.
       rewrite rxn_inputs_unif in H; done.
    apply EqRefl.
    rewrite NewNew.
    setoid_rewrite NewNew at 2.
    swap_tac 0 3.
    under_new rewrite new_pars_remove; last first; [ intro; repeat set_tac | apply EqRefl ].
    swap_tac 0 2.
    setoid_rewrite pars_fold.
    swap_tac 0 2.
    rewrite pars_fold.
    align.
    apply EqOut; simp_rxn; r_swap 1 2; rewrite EqReadSame; simp_rxn; done.
    apply EqOut; simp_rxn; r_swap 1 2; rewrite EqReadSame; simp_rxn; done.
Qed.

  Lemma rerandomP {L : nat} b (i : chan (TBool ** TBool)) (c1 c2 : chan L) :
    pars [::
            Out c1 (_ <-- Read i ;; Unif L);
            Out c2 (_ <-- Read i ;; Unif L)
         ]
    =0
       c1' <- new L ;;
       c2' <- new L ;;
       pars [::
               Out c1' (Unif L); 
               Out c2' (Unif L); 
               Out c1 (i <-- Read i ;; x <-- Read c1' ;; y <-- Read c2' ;; Ret (if  (if b then i.`1 else i.`2) then x else y));
               Out c2 (i <-- Read i ;; x <-- Read c1' ;; y <-- Read c2' ;; Ret (if (if b then i.`1 else i.`2) then y else x))
                   ].
    rewrite samp_pair.
    etransitivity.
    apply EqNew => e _ _.
    edit_tac 0.
    instantiate (1 := 
                   (i <-- Read i ;; x <-- Unif L ;; y <-- Unif L ;;
                    Ret (if (if b then i.1 else i.2) then {{ x, y }} else {{ y, x }}))).
         apply EqBind_r => x.
         destruct x as [x0 x1]; simpl.
         destruct b.
         destruct x0.
         done.
         r_swap 0 1.
         done.
         destruct x1.
         done.
         r_swap 0 1.
         done.
    swap_at 0 0 1.
    rewrite -pars_fold.
    apply EqNew => c1' _ _.
    swap_at 0 0 2.
    rewrite -pars_fold.
    apply EqNew => c2' _ _.
    do_inline; simp_all.
    do_inline; simp_all.
    apply EqRefl.
    setoid_rewrite NewNew at 1.
    setoid_rewrite NewNew at 2.
    under_new rewrite new_pars_remove; last first; [ intro; repeat set_tac | apply EqRefl].
    apply EqNew => c1' _ _.
    apply EqNew => c2' _ _.
    align.
        apply EqOut.
        r_swap 0 2.
        r_swap 1 3.
        rewrite EqReadSame.
        r_swap 1 2.
        apply EqBind_r => x.
        apply EqBind_r => y.
        apply EqBind_r => z.
        destruct x as [x0 x1]; destruct b; [ destruct x0 | destruct x1]; rewrite //=.

        apply EqOut.
        r_swap 0 2.
        r_swap 1 3.
        rewrite EqReadSame.
        r_swap 1 2.
        apply EqBind_r => x.
        apply EqBind_r => y.
        apply EqBind_r => z.
        destruct x as [x0 x1]; destruct b; [ destruct x0 | destruct x1]; rewrite //=.
Qed.

  Lemma rerandomP_rs {L : nat} b (i : chan (TBool ** TBool)) (c1 c2 : chan L) rs :
    pars [::
            Out c1 (_ <-- Read i ;; Unif L),
            Out c2 (_ <-- Read i ;; Unif L) & rs
         ]
    =0
       c1' <- new L ;;
       c2' <- new L ;;
       pars [::
               Out c1' (Unif L), 
               Out c2' (Unif L), 
               Out c1 (i <-- Read i ;; x <-- Read c1' ;; y <-- Read c2' ;; Ret (if  (if b then i.`1 else i.`2) then x else y)),
               Out c2 (i <-- Read i ;; x <-- Read c1' ;; y <-- Read c2' ;; Ret (if (if b then i.`1 else i.`2) then y else x)) & rs
                   ].
    rewrite (pars_split 2); simpl; rewrite take0 drop0.
    rewrite rerandomP.
    rewrite newComp.
    apply EqNew; intro => _ _.
    rewrite newComp.
    apply EqNew; intro => _ _.
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
  | [ |- @EqRxn _ ?r1 _ ] =>
    lazymatch r1 with
    | @Bind _ _ ?c ?k =>
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
  Context (ot_i1 ot_i2 ot_i3 : chan TBool).
  Context (ot_o1 ot_o2 ot_o3 : chan L).

  Context (ot14_m : chan ((L ** L) ** (L ** L))).
  Context (ot14_i : chan (TBool ** TBool)).
  Context (ot14_o : chan L).

  (* Leakage channels for bob *)
  Context (leak_ot_o1 leak_ot_o2 leak_ot_o3 : chan L).
  Context (leak_send : chan ((L ** L) ** (L ** L))).

  Definition One4_sender (ot_m1 ot_m2 ot_m3 : chan (L ** L)) (ready : chan TUnit) (send : chan ((L ** L) ** (L ** L)))  :=
    s0 <- new L ;;
    s1 <- new L ;;
    s2 <- new L ;;
    s3 <- new L ;;
    s4 <- new L ;;
    s5 <- new L ;;
    pars [::
            Out s0 (_ <-- Read ready;; Unif L);
            Out s1 (_ <-- Read ready;; Unif L);
            Out s2 (_ <-- Read ready;; Unif L);
            Out s3 (_ <-- Read ready;; Unif L);
            Out s4 (_ <-- Read ready;; Unif L);
            Out s5 (_ <-- Read ready;; Unif L);

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
                      {{
                          {{
                              s0 +t s2 +t m0 : L,
                                               s0 +t s3 +t m1 : L}},
                          {{ s1 +t s4 +t m2 : L, s1 +t s5 +t m3 : L }} }}));
         Out ot_m1 (
               a <-- Read s0 ;;
               b <-- Read s1 ;;
               Ret {{ a, b}} );
         Out ot_m2 (
               a <-- Read s2 ;;
               b <-- Read s3 ;;
               Ret {{ a, b}} );
         Out ot_m3 (
               a <-- Read s4 ;;
               b <-- Read s5 ;;
               Ret {{ a, b}} ) ].
               
  Definition One4_recv (ready : chan TUnit) (ot_i1 ot_i2 ot_i3 : chan TBool) (ot_o1 ot_o2 ot_o3 : chan L) (send : chan ((L ** L) ** (L ** L))) :=
    pars [::
            Out ready (_ <-- Read ot14_i ;; Ret vtt);
            Out ot_i1 (
                  i <-- Read ot14_i ;; Ret (i.`1));
            Out ot_i2 (
                  i <-- Read ot14_i ;; Ret (i.`2));
            Out ot_i3 (
                  i <-- Read ot14_i ;; Ret (i.`2));
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
                        | true, true => a3 +t T0 +t T2 : L
                                                    end))].

  Definition OT14_real_simpl :=
    c <- new L ;;
    c0 <- new L ;;
    c1 <- new L ;;
    c2 <- new L ;;
    c3 <- new L ;;
    c4 <- new L ;;
    [pars [:: Out ot14_o
              (x <-- Read ot14_i;; x_m <-- Read ot14_m;; Ret ((x_m # x.1) # x.2 : L));
            Out c2 (_ <-- Read ot14_i;; Unif L); 
            Out c3 (_ <-- Read ot14_i;; Unif L);
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
                   {{{{(x0 +t x2) +t m0 : L, (x0 +t x3) +t m1 : L}},
                   {{(x1 +t x4) +t m2 : L, (x1 +t x5) +t m3 : L}}}}));
            Out leak_ot_o3
              (x <-- Read c3;;
               x0 <-- Read c4;;
               x1 <-- Read ot14_i;; Ret (if x1 .`2 then x0 else x));
            Out leak_ot_o2
              (x <-- Read c1;;
               x0 <-- Read c2;;
               x1 <-- Read ot14_i;; Ret (if x1 .`2 then x0 else x));
            Out leak_ot_o1
              (x <-- Read c;;
               x0 <-- Read c0;;
               x1 <-- Read ot14_i;; Ret (if x1 .`1 then x0 else x));
            Out c1 (_ <-- Read ot14_i;; Unif L);
            Out c4 (_ <-- Read ot14_i;; Unif L);
            Out c (_ <-- Read ot14_i;; Unif L);
            Out c0 (_ <-- Read ot14_i;; Unif L) ]].

  Definition OT14_real :=
    ot_i1 <- new TBool ;;
    ot_i2 <- new TBool ;;
    ot_i3 <- new TBool ;;
    ot_m1 <- new (L ** L) ;;
    ot_m2 <- new (L ** L) ;;
    ot_m3 <- new (L ** L) ;;
    ot_o1 <- new L ;;
    ot_o2 <- new L ;;
    ot_o3 <- new L ;;
    send <- new ((L ** L) ** (L ** L)) ;;
    ready <- new TUnit ;;
    pars [::
            OTIdeal _ ot_i1 ot_m1 ot_o1;
            OTIdeal _ ot_i2 ot_m2 ot_o2;
            OTIdeal _ ot_i3 ot_m3 ot_o3;
            One4_sender ot_m1 ot_m2 ot_m3 ready send;
            One4_recv ready ot_i1 ot_i2 ot_i3 ot_o1 ot_o2 ot_o3 send ].
            
  Lemma ot14_simp : OT14_real =0 OT14_real_simpl.
    etransitivity.
    repeat ltac:(apply EqNew; intro => _ _).
    rewrite /OTIdeal.
    rewrite /One4_sender.
    swap_tac 0 3.
    setoid_rewrite New_in_pars at 1.
    setoid_rewrite New_in_pars at 1.
    setoid_rewrite New_in_pars at 1.
    setoid_rewrite New_in_pars at 1.
    setoid_rewrite New_in_pars at 1.
    setoid_rewrite New_in_pars at 1.
    apply EqNew => s0 _ _.
    apply EqNew => s1 _ _.
    apply EqNew => s2 _ _.
    apply EqNew => s3 _ _.
    apply EqNew => s4 _ _.
    apply EqNew => s5 _ _.
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
    repeat setoid_rewrite (NewNew TUnit).
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].
    repeat setoid_rewrite (NewNew ((L ** L) ** (L ** L))).
    swap_tac 0 13.
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].
    repeat setoid_rewrite (NewNew TBool) at 3.
    swap_tac 0 1.
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].
    repeat setoid_rewrite (NewNew TBool) at 2.
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].
    repeat setoid_rewrite (NewNew TBool) at 1.
    swap_tac 0 10.
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].
    repeat setoid_rewrite (NewNew (L ** L)) at 3.
    swap_tac 0 12.
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].
    repeat setoid_rewrite (NewNew (L ** L)) at 2.
    swap_tac 0 10.
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].
    repeat setoid_rewrite (NewNew (L ** L)).
    swap_tac 0 8.
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].

    swap_tac 0 10.
    setoid_rewrite (NewNew L) at 2.
    setoid_rewrite (NewNew L) at 3.
    setoid_rewrite (NewNew L) at 4.
    setoid_rewrite (NewNew L) at 5.
    setoid_rewrite (NewNew L) at 6.
    setoid_rewrite (NewNew L) at 7.
    setoid_rewrite (NewNew L) at 8.
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].

    swap_tac 0 11.
    setoid_rewrite (NewNew L) at 1.
    setoid_rewrite (NewNew L) at 2.
    setoid_rewrite (NewNew L) at 3.
    setoid_rewrite (NewNew L) at 4.
    setoid_rewrite (NewNew L) at 5.
    setoid_rewrite (NewNew L) at 6.
    setoid_rewrite (NewNew L) at 7.
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].

    swap_tac 0 9.
    setoid_rewrite (NewNew L) at 1.
    setoid_rewrite (NewNew L) at 2.
    setoid_rewrite (NewNew L) at 3.
    setoid_rewrite (NewNew L) at 4.
    setoid_rewrite (NewNew L) at 5.
    setoid_rewrite (NewNew L) at 6.
    under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].

    (* Now do some final simpl *)
    etransitivity.
    repeat ltac:(apply EqNew; intro; move => _ _).
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
    instantiate (1 := Ret ((x_m # x_i.1) # x_i.2 : L)).
    destruct x_m as [[m0 m1] [m2 m3]].
    simpl.
    destruct x_i as [i1 i2]; simpl.
    destruct i1, i2; simpl.

    rewrite ot14_xort_subproof !xortK !xort0 //=.
    rewrite ot14_xort_subproof !xortK !xort0 //=.
    rewrite ot14_xort_subproof !xortK !xort0 //=.
    rewrite ot14_xort_subproof !xortK !xort0 //=.

    undep_tac (Out ot14_o) (Out c); last by repeat ltac:(constructor; set_tac).
    undep_tac (Out ot14_o) (Out c0); last by repeat ltac:(constructor; set_tac).
    swap_at 0 0 1.
    undep_tac (Out ot14_o) (Out c3); last by repeat ltac:(constructor; set_tac).
    swap_at 0 0 1.
    undep_tac (Out ot14_o) (Out c4); last by repeat ltac:(constructor; set_tac).
    swap_at 0 0 1.
    undep_tac (Out ot14_o) (Out c1); last by repeat ltac:(constructor; set_tac).
    swap_at 0 0 1.
    undep_tac (Out ot14_o) (Out c2); last by repeat ltac:(constructor; set_tac).

    apply EqRefl.
    apply EqRefl.
Qed.

               
  Definition mkpair4 {t : type} (f : bool -> bool -> t) : (t ** t) ** (t ** t) :=
    ((f false false, f false true), (f true false, f true true)).

  Definition cflip {t : type} (p : t ** t) (b : bool) : t ** t :=
    if b then p else (p.2, p.1).

  Lemma bind_samp_xor {n : nat} {t} (a : n.-tuple bool) (k : n -> rxn t ) :
    EqRxn _ (x <-- Samp (uniform n : Dist n) ;; k x) (x <-- Samp (uniform n : Dist n) ;; k (x +t a)).
    apply EqBind_r_samp_bijection.
    apply xort_inj_r.
  Qed.

  Definition OT14_real_rerandomize :=
    c <- new L;;
  c0 <- new L;;
  c1 <- new L;;
  [pars [:: Out leak_send
              (x <-- Read ot14_i;;
               x0 <-- Read c1;;
               x1 <-- Read c0;;
               x2 <-- Read c;;
               x3 <-- Read ot14_m;;
               x4 <-- Unif L;;
               x5 <-- Unif L;;
               x6 <-- Unif L;;
               Ret
                 (let o := (x3 # x .`1) # x .`2 in
                  let o0 := if x .`2 && x .`1 then o else tzero L in
                  let o1 := if ~~ x .`2 && x .`1 then o else tzero L in
                  let o2 := if x .`2 && ~~ x .`1 then o else tzero L in
                  let o3 := if ~~ x .`2 && ~~ x .`1 then o else tzero L in
                  {{{{((x2, x4) # x .`1 +t (x0, x6) # x .`2) +t o3 : L,
                    ((x2, x4) # x .`1 +t (x6, x0) # x .`2) +t o2 : L}},
                  {{((x4, x2) # x .`1 +t (x1, x5) # x .`2) +t o1 : L,
                  ((x4, x2) # x .`1 +t (x5, x1) # x .`2) +t o0 : L}}}}));
            Out leak_ot_o1 (_ <-- Read ot14_i;; Read c);
            Out leak_ot_o3 (_ <-- Read ot14_i;; Read c0);
            Out leak_ot_o2 (_ <-- Read ot14_i;; y <-- Read c1;; Ret y);
            Out c1 (Samp (uniform L : Dist L)); Out c (Samp (uniform L : Dist L));
            Out ot14_o
              (x <-- Read ot14_i;; x0 <-- Read ot14_m;; Ret ((x0 # x.1) # x.2 : L));
            Out c0 (Samp (uniform L : Dist L))] ].


Lemma ot_simpl_rerandomize : OT14_real_simpl =0 OT14_real_rerandomize.
    etransitivity.
    repeat ltac:(apply EqNew; intro => _ _).
    swap_tac 0 9.
    swap_tac 1 10.
    etransitivity.
    rewrite (rerandomP_rs true).
    repeat ltac:(apply EqNew; intro => _ _).
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
        destruct s; done.
   swap_tac 0 4.
   swap_tac 1 10.
    rewrite (rerandomP_rs false).
    repeat ltac:(apply EqNew; intro => _ _).
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
        destruct s0; done.
  swap_tac 0 11.
  swap_tac 1 14.
    rewrite (rerandomP_rs false).
    repeat ltac:(apply EqNew; intro => _ _).
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
        destruct s0; done.
  apply EqRefl.
  apply EqRefl.
  (* Now elim useless channels *)
  setoid_rewrite (NewNew L) at 1.
  setoid_rewrite (NewNew L) at 2.
  setoid_rewrite (NewNew L) at 3.
  setoid_rewrite (NewNew L) at 4.
  setoid_rewrite (NewNew L) at 5.
  setoid_rewrite (NewNew L) at 6.
  setoid_rewrite (NewNew L) at 7.
  setoid_rewrite (NewNew L) at 8.
  setoid_rewrite (NewNew L) at 9.
  setoid_rewrite (NewNew L) at 10.
  setoid_rewrite (NewNew L) at 11.
  swap_tac 0 6.
  under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].

  
  setoid_rewrite (NewNew L) at 1.
  setoid_rewrite (NewNew L) at 2.
  setoid_rewrite (NewNew L) at 3.
  setoid_rewrite (NewNew L) at 4.
  setoid_rewrite (NewNew L) at 5.
  setoid_rewrite (NewNew L) at 6.
  setoid_rewrite (NewNew L) at 7.
  setoid_rewrite (NewNew L) at 8.
  setoid_rewrite (NewNew L) at 9.
  setoid_rewrite (NewNew L) at 10.
  swap_tac 0 6.
  under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].

  setoid_rewrite (NewNew L) at 1.
  setoid_rewrite (NewNew L) at 2.
  setoid_rewrite (NewNew L) at 3.
  setoid_rewrite (NewNew L) at 4.
  setoid_rewrite (NewNew L) at 5.
  setoid_rewrite (NewNew L) at 6.
  setoid_rewrite (NewNew L) at 7.
  setoid_rewrite (NewNew L) at 8.
  setoid_rewrite (NewNew L) at 9.
  under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].

  setoid_rewrite (NewNew L) at 1.
  setoid_rewrite (NewNew L) at 2.
  setoid_rewrite (NewNew L) at 3.
  setoid_rewrite (NewNew L) at 4.
  setoid_rewrite (NewNew L) at 5.
  setoid_rewrite (NewNew L) at 6.
  setoid_rewrite (NewNew L) at 7.
  setoid_rewrite (NewNew L) at 8.
  under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].

  setoid_rewrite (NewNew L) at 1.
  setoid_rewrite (NewNew L) at 2.
  setoid_rewrite (NewNew L) at 3.
  setoid_rewrite (NewNew L) at 4.
  setoid_rewrite (NewNew L) at 5.
  setoid_rewrite (NewNew L) at 6.
  setoid_rewrite (NewNew L) at 7.
  under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].
  
  setoid_rewrite (NewNew L) at 1.
  setoid_rewrite (NewNew L) at 2.
  setoid_rewrite (NewNew L) at 3.
  setoid_rewrite (NewNew L) at 4.
  setoid_rewrite (NewNew L) at 5.
  setoid_rewrite (NewNew L) at 6.
  under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].


  (* Now undep the leaks *)
  etransitivity.
  repeat ltac:(apply EqNew; intro => _ _ ).
  swap_at 4 0 1.
  undep_tac leak_ot_o3 (Out c1).
  swap_at 5 0 1.
  undep_tac leak_ot_o2 (Out c3).
  swap_at 6 0 1.
  undep_tac leak_ot_o1 (Out c).

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
  setoid_rewrite (NewNew L) at 5.
  swap_tac 0 3.
  under_new swap_at 0 0 1.
  swap_tac 1 2.
  under_new rewrite pars_fold; [ apply EqRefl ].

  under_new swap_at 0 0 3.
  swap_tac 1 3.
  setoid_rewrite (NewNew L) at 3.
  setoid_rewrite (NewNew L) at 4.
  under_new rewrite pars_fold; [ apply EqRefl ].

  under_new swap_at 0 0 5.
  setoid_rewrite (NewNew L) at 1.
  setoid_rewrite (NewNew L) at 2.
  setoid_rewrite (NewNew L) at 3.
  swap_tac 1 2.
  under_new rewrite pars_fold; [ apply EqRefl ].

  (* Now simplify leak_send *)
  etransitivity.
  apply EqNew; intro => _ _.
  apply EqNew; intro => _ _.
  apply EqNew; intro => _ _.
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
                   x4 <-- Unif L ;;
                   x5 <-- Unif L ;;
                   x6 <-- Unif L ;;
                   Ret (
                       let o := (x3 # x.`1) # x.`2 in
                       let o0 := if x.`2 && x.`1 then o else tzero _ in
                       let o1 := if (~~ x.`2) && x.`1 then o else tzero _ in
                       let o2 := if (x.`2) && (~~ x.`1) then o else tzero _ in
                       let o3 := if (~~ x.`2) && (~~ x.`1) then o else tzero _ in
                       {{ {{
                              (x2, x4) # x.`1 +t (x0, x6) # x.`2 +t o3 : L,
                              (x2, x4) # x.`1 +t (x6, x0) # x.`2 +t o2 : L }},
                          {{
                              (x4, x2) # x.`1 +t (x1, x5) # x.`2 +t o1 : L,
                              (x4, x2) # x.`1 +t (x5, x1) # x.`2 +t o0 : L }}
                            }})).
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
    apply EqNew => c _ _.
    apply EqNew => c1 _ _.
    apply EqNew => c2 _ _.
    align.
    apply EqOut; apply EqBind_r; intro; rewrite EqBindRet //=.
    apply EqOut; apply EqBind_r; intro; rewrite EqBindRet //=.
 Qed.

Definition OT14_sim (out : chan L) :=
c <- new L;;
c0 <- new L;;
c1 <- new L;;
[pars [:: Out leak_send
          (
            o <-- Read out ;;
            x <-- Read ot14_i;;
             x0 <-- Read c1;;
             x1 <-- Read c0;;
             x2 <-- Read c;;
             x4 <-- Unif L;;
             x5 <-- Unif L;;
             x6 <-- Unif L;;
             Ret
               (
                let o0 := if x .`2 && x .`1 then o else tzero L in
                let o1 := if ~~ x .`2 && x .`1 then o else tzero L in
                let o2 := if x .`2 && ~~ x .`1 then o else tzero L in
                let o3 := if ~~ x .`2 && ~~ x .`1 then o else tzero L in
                {{{{((x2, x4) # x .`1 +t (x0, x6) # x .`2) +t o3 : L,
                  ((x2, x4) # x .`1 +t (x6, x0) # x .`2) +t o2 : L}},
                {{((x4, x2) # x .`1 +t (x1, x5) # x .`2) +t o1 : L,
                ((x4, x2) # x .`1 +t (x5, x1) # x .`2) +t o0 : L}}}}));
          Out leak_ot_o1 (_ <-- Read ot14_i;; Read c);
          Out leak_ot_o3 (_ <-- Read ot14_i;; Read c0);
          Out leak_ot_o2 (_ <-- Read ot14_i;; y <-- Read c1;; Ret y);
          Out c1 (Samp (uniform L : Dist L)); Out c (Samp (uniform L : Dist L));
          Out c0 (Samp (uniform L : Dist L))] ].

Lemma OT14_real_simE :
  OT14_real_rerandomize =0
                           o <- new L ;;
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
  repeat ltac:(apply EqNew; intro => _ _).
  do_inline; simp_all.
  apply EqRefl.
  setoid_rewrite (NewNew L) at 1.
  setoid_rewrite (NewNew L) at 2.
  setoid_rewrite (NewNew L) at 3.
  swap_tac 0 7.
  under_new rewrite new_pars_remove; last first; [repeat set_tac | apply EqRefl].
  rewrite /OT14_real_rerandomize.
  apply EqNew => c _ _ .
  apply EqNew => c0 _ _ .
  apply EqNew => c1 _ _ .
  swap_tac 0 6.
  apply pars_cons_cong.
  apply EqOut.
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

Theorem OT14_security :
  OT14_real =0 
                           o <- new L ;;
                           pars [::
                                   OT14Ideal _ ot14_i ot14_m ot14_o;
                                   OT14Ideal _ ot14_i ot14_m o;
                                   OT14_sim o ].
  rewrite ot14_simp.
  rewrite ot_simpl_rerandomize.
  rewrite OT14_real_simE.
  done.
Qed.

End OneOutOf4.

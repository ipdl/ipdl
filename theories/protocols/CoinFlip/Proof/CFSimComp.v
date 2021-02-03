
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Pars Big Lib.Set Lib.OrdLems.
Require Import CFold CoinFlip.

Definition widen_ordS {n} (i : 'I_n) : 'I_(n.+1) := widen_ord (leqnSn n) i.

(* The simulator should work as follows:
   
   0. get leak from ideal world

   1. sends "committed" from everyone to Adv 
   2. once Adv commits message, generate random bits for all honest PIDs, except first honest which is equal to all commits xor leak
   3. Open all to adv
   4. Waits for open from adv, then sends ok to environment
*)

Lemma pars_inline_from_big_shift_index {t t'} {n1 n2} (b : chan t') (f : 'I_n1 -> 'I_n2)  (c : n2.-tuple (chan t)) (p : pred 'I_n1) (k : t -> rxn t') (r : 'I_n1 -> rxn t) (i : 'I_n1) rs :
  isDet _ (r i) ->
  p i ->
  pars [::
          Out b (x <-- Read (tnth c (f i)) ;; k x),
          \||_(j < n1 | p j) Out (tnth c (f j)) (r j) & rs] =0
  pars [::
          Out b (x <-- r i ;; k x),
          \||_(j < n1 | p j) Out (tnth c (f j)) (r j) & rs]. 
  intros.
  focus_tac 1.
  rewrite (bigpar_D1_ord i).
  done.
  done.
  rewrite SeqOps.insert_0.
  swap_tac 0 1.
  rewrite SeqOps.insert_0.
  rewrite par_in_pars; simpl.
  swap_tac 0 2; rewrite SeqOps.insert_0.
  swap_tac 1 2; rewrite SeqOps.insert_0.
  rewrite pars_inline.
  symmetry.
  focus_tac 1.
  rewrite (bigpar_D1_ord i).
  done.
  done.
  rewrite SeqOps.insert_0.
  swap_tac 0 1.
  rewrite SeqOps.insert_0.
  rewrite par_in_pars; simpl.
  swap_tac 0 2; rewrite SeqOps.insert_0.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 1; rewrite SeqOps.insert_0.
  apply pars_cons_cong; rewrite //=.
  done.
Qed.


   Lemma SimComp_simpl5E_subproof (k : nat) {n}
         (commit : (n.+1).-tuple (chan k))
         (sum_commits : (n.+1).-tuple (chan k))
         (committed : (n.+2).-tuple (chan TUnit))
         (sum_committed : (n.+2).-tuple (chan TUnit))
         (r : rxn k)
         (c : chan k) i :
     pars [::
             \||_(i < n.+1) Out (tnth committed (widen_ordS i)) (_ <-- Read (tnth commit i) ;; Ret vtt);
             Out (tnth committed ord_max) (Ret vtt);
          @cfold _ k k commit xort id sum_commits;
          read_all committed sum_committed;
          Out c (_ <-- Read (tnth sum_committed ord_max) ;;
                 _ <-- Read (tnth sum_commits i) ;; r)]
     =0     
     pars [::
             \||_(i < n.+1) Out (tnth committed (widen_ordS i)) (_ <-- Read (tnth commit i) ;; Ret vtt);
             Out (tnth committed ord_max) (Ret vtt);
          @cfold _ k k commit xort id sum_commits;
          read_all committed sum_committed;
          Out c (_ <-- Read (tnth sum_committed ord_max) ;;
                 r)].
     swap_tac 0 4.
     swap_at 0 0 1.
     symmetry; swap_tac 0 4; symmetry.


     move: r.
     induction i using ord_indP; intros.
     swap_tac 1 2.
     rewrite pars_inline_from_big.
     rewrite {1}/cfold_body //=.
     simp_all.
     symmetry.
     swap_tac 1 3.
     rewrite -pars_undep_cfold_input.
     instantiate (1 := ord0).
     swap_tac 1 4.
     have -> : tnth committed ord0 = tnth committed (widen_ordS ord0).
        congr (_ _ _).
        apply/eqP; rewrite eqE //=.
     rewrite pars_inline_from_big_shift_index //=.
     simp_all.
     apply pars_cons_cong; rewrite //=.
     swap_tac 0 1.
     apply pars_cons_cong; rewrite //=.
     swap_tac 0 1.
     apply pars_cons_cong; rewrite //=.
     swap_tac 0 1.
     apply pars_cons_cong; rewrite //=.
     done.
     done.

     intros.
     swap_tac 1 2.
     rewrite pars_inline_from_big.
     rewrite {1}/cfold_body //=.
     simp_at 0.
     swap_at 0 0 1.
     have -> : 
        (widen_ord (m:=n.+1) (leqnSn n)
                            (Ordinal (n:=n) (m:=i)
                                     (OrdLems.ltSS (lift_subproof (n:=n.+1) 0 i)))) =
        (widen_ord (leqnSn n) i).
        apply/eqP; rewrite eqE //=.
     swap_at 0 1 2.
     swap_tac 1 2.
     rewrite IHi; clear IHi.

     symmetry.

     swap_tac 1 3.
     rewrite -pars_undep_cfold_input.
     instantiate (1 := (widen_ord (leqnSn n.+1) (lift ord0 i))).
     swap_tac 1 4.
     rewrite pars_inline_from_big_shift_index //=.
     simp_all.
     apply pars_cons_cong.
     apply EqOut.
     r_swap 0 1.
     done.
     swap_tac 0 2.
     apply pars_cons_cong; rewrite //=.
     apply pars_cons_cong; rewrite //=.
     swap_tac 0 1.
     apply pars_cons_cong; rewrite //=.
     done.
     done.
Qed.


Ltac print_lhs_size :=
  match goal with
  | [ |- EqProt (pars ?rs) _ ] =>
    let j := eval simpl in (size rs) in idtac j end.

Ltac print_rhs_size :=
  match goal with
  | [ |- EqProt _ (pars ?rs) ] =>
    let j := eval simpl in (size rs) in idtac j end.

Lemma pars_replace r2 r1 rs :
  pars [:: r1 & rs] =0 pars [:: r2 & rs] ->
  pars [:: r1 & rs] =0 pars [:: r2 & rs].
  done.
Qed.

Lemma big_ord_not_maxE {n} (f : 'I_(n.+1) -> rset) :
  \||_(i < n.+1 | i != ord_max) (f i) =0 \||_(i < n) (f (widen_ordS i)).
  rewrite bigpar_mkcond.
  rewrite bigpar_ord_recr.
  rewrite eq_refl //= -eq_0par.
  apply EqProt_big_r; intros.
  rewrite eqE //=.
  have: x < n by destruct x.
  intro h.
  rewrite ltn_neqAle in h.
  move/andP: h; elim; intros.
  rewrite H1.
  done.
Qed.


Section SimDef.
  Context (k : nat) {n_ : nat}.
  Let n := nosimpl n_.+2. (* we assume at least 2 players *)
  Context (honest : pred 'I_n).
  Context (H : honest ord_max).
  Context (H0 : ~~ honest ord0).

  Context (leak : (chan k)).
  Context (ok : chan TUnit).

  Context (advCommit : n.-tuple (chan k)).
  Context (advOpen : n.-tuple (chan TUnit)).

  Context (advCommitted : n.-tuple (n.-tuple (chan TUnit))).
  Context (advOpened : n.-tuple (n.-tuple (chan k))).

  
  Definition Sim_CFRealParty_honest 
             (committed : n.-tuple (chan TUnit)) (opened : n.-tuple (chan k))
             (commit : chan k) (open : chan TUnit) 
    :=
      committed_sum <- newvec n @ TUnit ;; 
      opened_sum <- newvec n @ k ;; 
      pars [::
            Out commit (Unif k);
            read_all committed committed_sum;
            Out open (copy (tnth committed_sum ord_max));

            @cfold _ k k opened xort id opened_sum
      ].

  Definition Sim_CFRealParty_corr (i : 'I_n)
             (committed : n.-tuple (chan TUnit))
             (opened : n.-tuple (chan k))
             (commit : chan k) (open : chan TUnit) :=
    pars [::
            Out commit (copy (tnth advCommit i));
            Out open (copy (tnth advOpen i));
            Outvec (tnth advCommitted i) (fun j => copy (tnth committed j));
            Outvec (tnth advOpened i) (fun j => copy (tnth opened j))
    ].

  Definition Sim_CFParty (i : 'I_n)
             (committed : n.-tuple (chan TUnit)) (opened : n.-tuple (chan k))
             (commit : chan k) (open : chan TUnit) :=
    if honest i then Sim_CFRealParty_honest committed opened commit open 
                else Sim_CFRealParty_corr i committed opened commit open.                        

  Definition Sim_CFParty_last
             (sum_commits : n.-tuple (chan k))
             (committed_sum : n.-tuple (chan TUnit))
             (commit : chan k) (open : chan TUnit) :=
    pars [::
            Out commit (
                  x <-- Read (tnth sum_commits (inord n_)) ;; 
                  y <-- Read leak ;;
                  Ret ((x +t y) : k));
            Out open (copy (tnth committed_sum ord_max))
                ].

  Definition Sim :=
    commit <- newvec n @ k ;;
    open <- newvec n @ TUnit ;;
    committed <- newvec n @ TUnit ;;
    opened <- newvec n @ k ;;
    sum_commits <- newvec n @ k ;;
    sum_committed <- newvec n @ TUnit ;;
    sum_open <- newvec n @ TUnit ;;
    sum_opened <- newvec n @ k ;;

    pars [::
            \||_(i < n | i != ord_max) Sim_CFParty i committed opened (tnth commit i) (tnth open i);
         Sim_CFParty_last
           sum_commits
           sum_committed
           (tnth commit ord_max)
           (tnth open ord_max);

         @cfold _ k k commit xort id sum_commits;
         read_all committed sum_committed;
         read_all open sum_open;
         @cfold _ k k opened xort id sum_opened;

         Out (tnth committed ord_max) (Ret vtt);
         Out (tnth opened ord_max) (x <-- Read (tnth commit ord_max) ;; _ <-- Read (tnth open ord_max) ;; Ret x);
         \||_(i < n | i != ord_max) FComm k (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);

         Out ok (_ <-- Read (tnth sum_commits ord_max) ;;
                 _ <-- Read (tnth sum_open ord_max) ;;
                 Ret vtt)
         ].
End SimDef.  

Section SimComp.
  Context (k : nat) {n_ : nat}.
  Let n := nosimpl n_.+2. (* we assume at least 2 players *)
  Context (honest : pred 'I_n).
  Context (H : honest ord_max).
  Context (H0 : ~~ honest ord0).

  Context (advCommit : n.-tuple (chan k)).
  Context (advOpen : n.-tuple (chan TUnit)).

  Context (advCommitted : n.-tuple (n.-tuple (chan TUnit))).
  Context (advOpened : n.-tuple (n.-tuple (chan k))).

  Check CFIdeal.
  
  Definition SimComp (out : n.-tuple (chan k)) :=
    leakB <- new k ;;
    ok <- new TUnit ;; 
    pars [::
            Sim k honest leakB ok advCommit advOpen advCommitted advOpened;
            CFIdeal k _ honest leakB ok out
                 ].
 

  (* out ->
         Out ok (_ <-- Read (tnth sum_commits ord_max) ;;
                 _ <-- Read (tnth sum_open ord_max) ;;
                 x <- Read send ;;
                 Ret x)
  *)

  Print CFIdealFunc.

  Definition SimComp_simpl1 (out : n.-tuple (chan k)) :=
    leak <- new k ;;
    ok <- new TUnit ;; 
    commit <- newvec n @ k ;;
    open <- newvec n @ TUnit ;;
    committed <- newvec n @ TUnit ;;
    opened <- newvec n @ k ;;
    sum_commits <- newvec n @ k ;;
    sum_committed <- newvec n @ TUnit ;;
    sum_open <- newvec n @ TUnit ;;
    sum_opened <- newvec n @ k ;;
    r <- new k ;;
    send <- new k ;;
    
 (pars [:: \||_(i<n | honest i)
             Out (tnth out i)
               (_ <-- Read (tnth sum_commits ord_max);;
                _ <-- Read (tnth sum_open ord_max);;
                copy r);
            Out ok
              (_ <-- Read (tnth sum_commits ord_max);;
               _ <-- Read (tnth sum_open ord_max);;
               Ret vtt);
            Sim_CFParty_last
              k
              leak
              sum_commits
              sum_committed
              (tnth commit ord_max)
              (tnth open ord_max);

         @cfold _ k k commit xort id sum_commits;
         read_all committed sum_committed;
         read_all open sum_open;
         @cfold _ k k opened xort id sum_opened;



         Out (tnth committed ord_max) (Ret vtt);
         Out (tnth opened ord_max) (x <-- Read (tnth commit ord_max) ;; _ <-- Read (tnth open ord_max) ;; Ret x);
         \||_(i < n | i != ord_max) FComm k (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);
           Out r (Unif k);
           Out leak (copy r);
           Out send (_ <-- Read ok ;; copy r);

            \||_(i < n | i != ord_max) Sim_CFParty k honest advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i) ] ).
             

  Lemma SimComp_E1 out : SimComp out =0 SimComp_simpl1 out.
    rewrite /SimComp /SimComp_simpl1.
    apply EqNew => leak _ _.
    apply EqNew => ok _ _.
    rewrite /SimComp.
    rewrite /Sim.
    repeat setoid_rewrite newPars.
    apply EqNew_vec => commit _ _.
    apply EqNew_vec => open _ _.
    apply EqNew_vec => committed _ _.
    apply EqNew_vec => opened _ _.
    apply EqNew_vec => sum_commits _ _.
    apply EqNew_vec => sum_committed _ _.
    apply EqNew_vec => sum_open _ _.
    apply EqNew_vec => sum_opened _ _.
    rewrite pars_pars.
    swap_tac 0 CFIdeal.
    
    rewrite newPars.
    setoid_rewrite pars_pars; simpl. 
    etransitivity.
    apply EqNew => b _ _.
    rewrite newPars.
    setoid_rewrite pars_pars at 1; simpl.
    apply EqRefl.
    rewrite NewNew.
    
    apply EqNew => r _ _.
    apply EqNew => send _ _.
    rewrite /CFIdealParty.
    rewrite -bigpar_mkcond.
    swap_tac 0 3.
    swap_tac 1 2.
    etransitivity.
    apply pars_big_replace.
    intros.
    rewrite pars_inline.
    simp_all.
    swap_tac 1 12.
    rewrite pars_inline.
    swap_tac 1 12.
    apply EqRefl.
    done.
    done.
    apply pars_cons_cong.
    apply EqProt_big_r; intros; apply EqOut.
    simp_rxn.
    rewrite /copy //=.
    swap_tac 0 (Out ok).
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 2.
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 (@cfold _ k k commit xort).
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 2.
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 2.
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 2.
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 2.
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 2.
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 2.
    apply pars_cons_cong; rewrite //=.
    swap_tac 0 1.
    apply pars_cons_cong; rewrite //=.
    apply _.
    apply _.
    apply _.
    apply _.
    apply _.
    apply _.
    apply _.
    apply _.
 Qed.

  Definition SimComp_simpl2 (out : n.-tuple (chan k)) :=
    leak <- new k ;;
    ok <- new TUnit ;; 
    commit <- newvec n @ k ;;
    open <- newvec n @ TUnit ;;
    committed <- newvec n @ TUnit ;;
    opened <- newvec n @ k ;;
    sum_commits <- newvec n @ k ;;
    sum_committed <- newvec n @ TUnit ;;
    sum_open <- newvec n @ TUnit ;;
    sum_opened <- newvec n @ k ;;
    r <- new k ;;
    send <- new k ;;
    
 (pars [:: \||_(i<n | honest i)
             Out (tnth out i)
               (x <-- Read (tnth sum_commits ord_max);;
                _ <-- Read (tnth sum_open ord_max);;
                Ret x);
            Out ok
              (_ <-- Read (tnth sum_commits ord_max);;
               _ <-- Read (tnth sum_open ord_max);;
               Ret vtt);
            
            Sim_CFParty_last
              k
              leak
              sum_commits
              sum_committed
              (tnth commit ord_max)
              (tnth open ord_max);

         @cfold _ k k commit xort id sum_commits;
         read_all committed sum_committed;
         read_all open sum_open;
         @cfold _ k k opened xort id sum_opened;

         Out (tnth committed ord_max) (Ret vtt);
         Out (tnth opened ord_max) (x <-- Read (tnth commit ord_max) ;; _ <-- Read (tnth open ord_max) ;; Ret x);
         \||_(i < n | i != ord_max) FComm k (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);

           Out r (Unif k);
           Out leak (copy r);
           Out send (_ <-- Read ok ;; copy r);

      \||_(i < n | i != ord_max) Sim_CFParty k honest advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i) ] ).
             

  Lemma SimComp_simpl2E out :
    SimComp_simpl1 out =0 SimComp_simpl2 out.

    apply EqNew => leak _ _.
    apply EqNew => ok _ _.
    rewrite /SimComp_simpl1.
    etransitivity.
    apply EqNew_vec => commit _ _.
    apply EqNew_vec => open _ _.
    apply EqNew_vec => committed _ _.
    apply EqNew_vec => opened _ _.
    apply EqNew_vec => sum_commits _ _.
    apply EqNew_vec => sum_committed _ _.
    apply EqNew_vec => sum_open _ _.
    apply EqNew_vec => sum_opened _ _.
    apply EqNew => r _ _.
    apply EqNew => send _ _.
    swap_tac 1 (@cfold _ k k commit).
    etransitivity.
    apply pars_big_replace; intros.
    rewrite pars_inline_from_big //=; last first.
    rewrite /cfold_body //=.
    focus_tac 0.
      apply EqOut.
      simp_rxn.
      apply EqRxnRefl.
    swap_tac 0 (@Sim_CFParty_last).
    rewrite pars_pars //=.
    swap_tac 0 3.
    swap_tac 1 3.

    etransitivity.
    apply pars_big_replace; intros.
    rewrite pars_inline //=.
    apply EqRefl.

    simpl.
    swap_tac 1 (Out leak).
    etransitivity.
    apply pars_big_replace; intros.
    simp_at 0.
    swap_at 0 0 1.
    rewrite pars_inline.
    edit_tac 0.
    rewrite /copy; simp_rxn.
    r_swap 1 4.
    rewrite EqReadSame.
    apply EqRxnRefl.
    apply EqRefl.
    done.
    simpl.
    apply EqRefl.
    symmetry.

    apply EqNew_vec => commit _ _.
    apply EqNew_vec => open _ _.
    apply EqNew_vec => committed _ _.
    apply EqNew_vec => opened _ _.
    apply EqNew_vec => sum_commits _ _.
    apply EqNew_vec => sum_committed _ _.
    apply EqNew_vec => sum_open _ _.
    apply EqNew_vec => sum_opened _ _.
    apply EqNew => r _ _.
    apply EqNew => send _ _.

    swap_tac 1 3.
    etransitivity.
    apply pars_big_replace; intros.
    rewrite pars_inline_from_big.
    rewrite {1}/cfold_body //=.
    apply EqRefl.
    done.
    done.
    swap_tac 0 2.
    rewrite pars_pars //=.
    swap_tac 1 (Out leak).
    swap_at 0 0 1.
    rewrite pars_inline //=.
    swap_tac 0 3.
    swap_tac 1 3.
    etransitivity.
    apply pars_big_replace; intros.
    simp_at 0.
    rewrite pars_inline //=.
    simp_at 0.
    edit_tac 0.
    rewrite /copy; simp_rxn.
    have -> :
      (tnth sum_commits (inord n_)) =
      (tnth sum_commits
        (widen_ord (m:=n_.+2) (leqnSn n_.+1)
           (Ordinal (n:=n_.+1) (m:=n_) (OrdLems.ltSS (ltnSn n_.+1))))).
    congr (_ _ _).
    apply/eqP; rewrite eqE //=.
    rewrite inordK //=.
    apply EqBind_r; intro.
    rewrite !EqReadSame.
    apply EqBind_r; intro.
    apply EqBind_r; intro.
    destruct x1; rewrite //= ?negbK //=.
    instantiate (1 := fun _ => Ret x).
    rewrite -xortA xortK xortC xort0 //=.

    simp_at 0.
    apply EqRefl.

    apply pars_cons_cong; rewrite //=.
    apply EqProt_big_r; intros; apply EqOut.
    apply EqBind_r; intros.

    have -> :
      (tnth sum_commits (inord n_)) =
      (tnth sum_commits
        (widen_ord (m:=n_.+2) (leqnSn n_.+1)
           (Ordinal (n:=n_.+1) (m:=n_) (OrdLems.ltSS (ltnSn n_.+1))))).
    congr (_ _ _).
    apply/eqP; rewrite eqE //=.
    rewrite inordK //=.
    rewrite EqReadSame.
    apply EqBind_r; intro.
    done.

    symmetry.
    swap_tac 0 (Out (tnth commit ord_max)).
    swap_at 0 0 1.
    swap_tac 1 (Out leak).
    rewrite pars_inline.
    align.
    done.
 Qed.


  (* Eliminate send, leakB and ok channels *)

  Definition SimComp_simpl3 (out : n.-tuple (chan k)) :=
    commit <- newvec n @ k ;;
    open <- newvec n @ TUnit ;;
    committed <- newvec n @ TUnit ;;
    opened <- newvec n @ k ;;
    sum_commits <- newvec n @ k ;;
    sum_committed <- newvec n @ TUnit ;;
    sum_open <- newvec n @ TUnit ;;
    sum_opened <- newvec n @ k ;;
    r <- new k ;;
    
[pars [:: \||_(i<n | honest i)
             Out (tnth out i)
               (x <-- Read (tnth sum_commits ord_max);;
                _ <-- Read (tnth sum_open ord_max);;
                Ret x);
      Out (tnth commit ord_max) (x <-- Read (tnth sum_commits (inord n_)) ;;
                                 y <-- Read r ;; Ret ((x +t y) : k));
      Out (tnth open ord_max) (copy (tnth sum_committed ord_max));

         @cfold _ k k commit xort id sum_commits;
         read_all committed sum_committed;
         read_all open sum_open;
         @cfold _ k k opened xort id sum_opened;

         Out (tnth committed ord_max) (Ret vtt);
         Out (tnth opened ord_max) (x <-- Read (tnth commit ord_max) ;; _ <-- Read (tnth open ord_max) ;; Ret x);
         \||_(i < n | i != ord_max) FComm k (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);
         Out r (Unif k);

      \||_(i < n | i != ord_max) Sim_CFParty k honest advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i) ] ].

  Lemma SimComp_simpl3E out :
    SimComp_simpl2 out =0 SimComp_simpl3 out.
    rewrite /SimComp_simpl2.


    etransitivity.
    rotate_news.
    rotate_news.
    apply EqRefl.

    rewrite /SimComp_simpl3.

    apply EqNew_vec => commit _ _.
    apply EqNew_vec => open _ _.
    apply EqNew_vec => committed _ _.
    apply EqNew_vec => opened _ _.
    apply EqNew_vec => sum_commits _ _.
    apply EqNew_vec => sum_committed _ _.
    apply EqNew_vec => sum_open _ _.
    apply EqNew_vec => sum_opened _ _.
    apply EqNew => r _ _.

    (* elim c0 *)
    etransitivity.
    rewrite NewNew.
    setoid_rewrite NewNew at 2.
    apply EqNew; intro => _ _.
    apply EqNew; intro => _ _.
    swap_tac 0 12. 
    rewrite new_pars_remove; last first.
      intros; repeat set_tac.
    apply EqRefl.

    (* elim c0 *)
    etransitivity.
    apply EqNew => c _ _.
    rewrite new_pars_remove; last first.
       intros; repeat set_tac.
         right; right; right; left.
         eapply In_big; rewrite //=.
         right; done.
         rewrite mem_index_enum //=.

         right; left.
         eapply In_big; rewrite //=.
         right; done.
         rewrite mem_index_enum //=.
         apply EqRefl.
   (* now elim last *)
   swap_tac 0 9. 
   rewrite /Sim_CFParty_last.
   swap_tac 0 9.
   setoid_rewrite pars_pars; simpl.
   etransitivity.
   apply EqNew => c _ _.
   swap_at 0 0 1.
   swap_tac 1 (Out c).
   apply EqRefl.
   rewrite pars_fold.
   align.
   apply EqOut.
   rewrite /copy; simp_rxn.
   r_swap 0 1.
   done.
 Qed.

  (* Rerandomize r *)

  Definition SimComp_simpl4 (out : n.-tuple (chan k)) :=
    commit <- newvec n @ k ;;
    open <- newvec n @ TUnit ;;
    committed <- newvec n @ TUnit ;;
    opened <- newvec n @ k ;;
    sum_commits <- newvec n @ k ;;
    sum_committed <- newvec n @ TUnit ;;
    sum_open <- newvec n @ TUnit ;;
    sum_opened <- newvec n @ k ;;
    r <- new k ;;
    
[pars [:: \||_(i<n | honest i)
             Out (tnth out i)
               (x <-- Read (tnth sum_commits ord_max);;
                _ <-- Read (tnth sum_open ord_max);;
                Ret x);
      Out (tnth commit ord_max) (_ <-- Read (tnth sum_commits (inord n_)) ;;
                                 x <-- Read r ;; Ret x);
      Out (tnth open ord_max) (copy (tnth sum_committed ord_max));

         @cfold _ k k commit xort id sum_commits;
         read_all committed sum_committed;
         read_all open sum_open;
         @cfold _ k k opened xort id sum_opened;

         Out (tnth committed ord_max) (Ret vtt);
         Out (tnth opened ord_max) (x <-- Read (tnth commit ord_max) ;; _ <-- Read (tnth open ord_max) ;; Ret x);
         \||_(i < n | i != ord_max) FComm k (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);
        Out r (Unif k);

      \||_(i < n | i != ord_max) Sim_CFParty k honest advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i) ] ].

  Lemma SimComp_simpl4E out :
    SimComp_simpl3 out =0 SimComp_simpl4 out.
    apply EqNew_vec => commit _ _.
    apply EqNew_vec => open _ _.
    apply EqNew_vec => committed _ _.
    apply EqNew_vec => opened _ _.
    apply EqNew_vec => sum_commits _ _.
    apply EqNew_vec => sum_committed _ _.
    apply EqNew_vec => sum_open _ _.
    apply EqNew_vec => sum_opened _ _.
    etransitivity.
    swap_tac 0 10.
    etransitivity.
    apply EqNew => r _ _.
    swap_at 1 0 1.
    apply EqRefl.
    swap_tac 0 1.
    rewrite pars_fold.
    edit_tac 0.
    r_swap 0 1.
    apply EqBind_r; intro.
    instantiate (1 := fun _ => (y <-- Unif k ;; Ret y)).
    simpl.
    rewrite EqBindRet.
    symmetry.
    apply EqSampBijection.
    apply xort_inj_l.
    swap_at 0 0 1.
    rewrite -pars_fold.
    apply EqNew => r _ _.
    swap_at 0 0 1.
    align.
Qed.

  (* Eliminate last commit *)

  Definition SimComp_simpl5 (out : n.-tuple (chan k)) :=
    open <- newvec n @ TUnit ;;
    committed <- newvec n @ TUnit ;;
    opened <- newvec n @ k ;;
    sum_commits_ <- newvec (n_.+1) @ k ;;
    sum_commits_last <- new k;;
    sum_committed <- newvec n @ TUnit ;;
    sum_open <- newvec n @ TUnit ;;
    sum_opened <- newvec n @ k ;;
    r <- new k ;;
    commit <- newvec (n_.+1) @ k ;;
    
[pars [:: \||_(i<n | honest i)
             Out (tnth out i)
               (x <-- Read (tnth [tuple of rcons sum_commits_ sum_commits_last] ord_max);;
                _ <-- Read (tnth sum_open ord_max);;
                Ret x);
      Out r (Unif k);
      Out (tnth open ord_max) (copy (tnth sum_committed ord_max));

      @cfold _ k k commit xort id sum_commits_;
      Out sum_commits_last (x <-- Read r ;; y <-- Read (tnth sum_commits_ ord_max) ;; Ret ((x +t y) : k));
         read_all committed sum_committed;
         read_all open sum_open;
         @cfold _ k k opened xort id sum_opened;

         Out (tnth committed ord_max) (Ret vtt);
         Out (tnth opened ord_max) (x <-- Read r ;; _ <-- Read (tnth open ord_max) ;; Ret x);
         \||_(i < (n_.+1)) FComm k (tnth commit i) (tnth committed (widen_ordS i)) (tnth open (widen_ordS  i)) (tnth opened (widen_ordS i));

      \||_(i < n_.+1) Sim_CFParty k honest advCommit advOpen advCommitted advOpened (widen_ordS i) committed opened (tnth commit i) (tnth open (widen_ordS i)) ] ].

  Lemma SimComp_simpl5E out :
    SimComp_simpl4 out =0 SimComp_simpl5 out.
    rewrite /SimComp_simpl4.
    rewrite /SimComp_simpl5.
    etransitivity.
    rotate_news.
    apply EqRefl.

    apply EqNew_vec => open _ _.
    apply EqNew_vec => committed _ _.
    apply EqNew_vec => opened _ _.
    etransitivity.
    rewrite newvecS_r.
    apply EqRefl.
    rewrite -New_newvec.
    apply EqNew_vec => sum_commits_ _ _.
    apply EqNew => sum_commits_last _ _.
    apply EqNew_vec => sum_committed _ _.
    apply EqNew_vec => sum_open _ _.
    apply EqNew_vec => sum_opened _ _.
    apply EqNew => r _ _.
    etransitivity.
    rewrite newvecS_r.
    done.
    rewrite -New_newvec.
    apply EqNew_vec => commit _ _.

    etransitivity.
    (* Now elim y *)
    etransitivity.
    apply EqNew => commit_last _ _.
    have -> : tnth [tuple of rcons commit commit_last] ord_max = commit_last.
        rewrite /tnth nth_rcons size_tuple //= ltnn eq_refl //=.
    rewrite cfoldS_r.
    swap_tac 0 3.
    rewrite pars_pars //=.
    inline_tac (Out sum_commits_last) (Out commit_last).
    simp_at 0.
        edit_tac 0.
        r_swap 1 2.
        have -> : (tnth [tuple of rcons sum_commits_ sum_commits_last] (inord n_))
                  =
                  (tnth sum_commits_ ord_max).
            rewrite /tnth nth_rcons.
            rewrite size_tuple inordK ltnS.
            rewrite leqnn.
            simpl.
            apply set_nth_default.
            rewrite size_tuple.
            rewrite ltnS leqnn //=.
            rewrite leqnSn //=.
        
        rewrite EqReadSame.
        r_swap 0 1.
        done.

   inline_tac (Out (tnth opened ord_max)) (Out commit_last).
   simp_at 0.
   apply EqRefl.
   
   (* remove commit_last from FComm and Sim_CFParty *)
   etransitivity.
   apply EqNew => commit_last _ _.
   focus_tac 10.
   rewrite big_ord_not_maxE.
   apply EqProt_big_r; intros.
   have -> : tnth [tuple of rcons commit commit_last] (widen_ordS x) =
             tnth commit x.
       rewrite /tnth nth_rcons //= size_tuple.
       have -> : x < n_.+1 by destruct x.
       apply set_nth_default.
       rewrite size_tuple; destruct x; done.
   apply EqRefl.
   focus_tac 12.
   rewrite big_ord_not_maxE.
   apply EqProt_big_r; intros.
   have -> : tnth [tuple of rcons commit commit_last] (widen_ordS x) =
             tnth commit x.
       rewrite /tnth nth_rcons //= size_tuple.
       have -> : x < n_.+1 by destruct x.
       apply set_nth_default.
       rewrite size_tuple; by destruct x.
   apply EqRefl.

   apply EqRefl.
   swap_tac 0 1.
   rewrite new_pars_remove; last first.
   intros; repeat set_tac.

   apply EqRefl.

   (* now the LHS and RHS are the same, except that opened ord_max has a dependency on this sum_commits stuff -- so now we remove it *)
   etransitivity.
   apply (pars_replace
            (Out (tnth opened ord_max) (
                   x <-- Read r ;; _ <-- Read (tnth open ord_max) ;; Ret x))).
   have -> : tnth [tuple of rcons sum_commits_ sum_commits_last] (inord n_) =
             tnth sum_commits_ ord_max.
      rewrite /tnth nth_rcons //=.
      rewrite size_tuple inordK //=.
      rewrite ltnSn.
      apply set_nth_default.
      rewrite size_tuple ltnSn //=.

    etransitivity.
    edit_tac 0.
    r_swap 0 2.
    done.
   inline_tac (Out (tnth opened ord_max)) (Out (tnth open ord_max)).
   rewrite /copy.
   simp_at 0.

   symmetry.
    etransitivity.
    edit_tac 0.
    r_swap 0 1.
    done.

   inline_tac (Out (tnth opened ord_max)) (Out (tnth open ord_max)).
   rewrite /copy.
   etransitivity.
   edit_tac 0.
     simp_rxn.
     apply EqRxnRefl.
   symmetry.
   swap_tac 1 2.
   swap_tac 2 4.
   swap_tac 3 9.
   swap_tac 4 7.
   rewrite (pars_split 5); simpl.

   symmetry.
   swap_tac 1 2.
   swap_tac 2 4.
   swap_tac 3 9.
   swap_tac 4 7.
   rewrite (pars_split 5); simpl.
   symmetry.

   apply EqCong.
   rewrite big_pars2.
   swap_tac 0 3; rewrite pars_pars //=; swap_tac 0 1.
   symmetry; swap_tac 0 3; rewrite pars_pars //=; swap_tac 0 1; symmetry.
   apply pars_cons_cong; rewrite //=.
   swap_tac 1 4.
   swap_tac 2 4.
   swap_tac 3 4.
   rewrite SimComp_simpl5E_subproof.
   align.

   align.

   swap_tac 0 3.
   apply pars_cons_cong; rewrite //=.
   swap_tac 0 (Out r).
   apply pars_cons_cong; rewrite //=.
   align.
   apply EqOut.
   apply EqBind_r; intro.
   apply EqBind_r; intro.
   rewrite xortC //=.
Qed.


(* 1. Collapse r into commit
   2. re-fold sum_commits and sum_commits_last, given 1.
   3. depend last committed on last commit, fold last committed, opened into FComm
 *)


  Definition SimComp_simpl6 (out : n.-tuple (chan k)) :=
    open <- newvec n @ TUnit ;;
    committed <- newvec n @ TUnit ;;
    opened <- newvec n @ k ;;
    sum_commits <- newvec n @ k ;;
    sum_committed <- newvec n @ TUnit ;;
    sum_open <- newvec n @ TUnit ;;
    sum_opened <- newvec n @ k ;;
    commit <- newvec n @ k ;;
    
[pars [:: \||_(i<n | honest i)
             Out (tnth out i)
               (x <-- Read (tnth sum_commits ord_max);;
                _ <-- Read (tnth sum_open ord_max);;
                Ret x);
      Out (tnth commit ord_max) (Unif k);
      Out (tnth open ord_max) (copy (tnth sum_committed ord_max));

      @cfold _ k k commit xort id sum_commits;
         read_all committed sum_committed;
         read_all open sum_open;
         @cfold _ k k opened xort id sum_opened;

         \||_(i < n) FComm k (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);

      \||_(i < n | i != ord_max) Sim_CFParty k honest advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i) ] ].

Lemma SimComp_simpl6E out :
    SimComp_simpl5 out =0 SimComp_simpl6 out.
  rewrite /SimComp_simpl5.
  rewrite /SimComp_simpl6.
  symmetry.

  apply EqNew_vec => open _ _.
  apply EqNew_vec => committed _ _.
  apply EqNew_vec => opened _ _.

  etransitivity.
  rewrite newvecS_r.
  apply EqRefl.
  rewrite New_newvec.
  apply EqNew => sum_commits_last _ _.
  apply EqNew_vec => sum_commits _ _.
  apply EqNew_vec => sum_committed _ _.
  apply EqNew_vec => sum_open _ _.
  apply EqNew_vec => sum_opened _ _.
  etransitivity.
    rewrite newvecS_r.
  apply EqRefl.
  apply EqNew => last_commit _ _.
  apply EqNew_vec => commit _ _.
  symmetry.

  swap_tac 0 (Out (tnth committed ord_max)).
  Check pars_undep.
  rewrite -pars_undep //=.
  symmetry.
  swap_tac 0 7.
  rewrite bigpar_ord_recr par_in_pars.
  rewrite pars_pars //=.

  (* just matching things up now *)
  apply pars_cons_cong.
    rewrite tnth_rcons_ord_max; done.
  swap_tac 0 2.
  apply pars_cons_cong.
    rewrite tnth_rcons_ord_max; done.
  swap_tac 0 (Out (tnth open ord_max)).
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  rewrite cfoldS_r pars_pars //=.
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  apply EqOut; apply EqBind_r; intro; apply EqBind_r; intro; rewrite xortC //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 1.
  apply pars_cons_cong; rewrite //=.
  rewrite /copy.
  apply EqOut.
  rewrite tnth_rcons_ord_max.
  r_swap 0 1.
  done.
  apply pars_cons_cong; rewrite //=.
  apply EqProt_big_r; intros.
  rewrite tnth_rcons_widen_ord //=.
  apply pars_cons_cong; rewrite //=.
  rewrite big_ord_not_maxE.
  apply EqProt_big_r; intros.
  rewrite tnth_rcons_widen_ord //.
Qed.

(* Restore last party to be like others *)

  Definition SimComp_simpl7 (out : n.-tuple (chan k)) :=
    open <- newvec n @ TUnit ;;
    committed <- newvec n @ TUnit ;;
    opened <- newvec n @ k ;;
    sum_commits <- newvec n @ k ;;
    sum_open <- newvec n @ TUnit ;;
    commit <- newvec n @ k ;;
    
[pars [:: \||_(i<n | honest i)
             Out (tnth out i)
               (x <-- Read (tnth sum_commits ord_max);;
                _ <-- Read (tnth sum_open ord_max);;
                Ret x);

      @cfold _ k k commit xort id sum_commits;
         read_all open sum_open;

         \||_(i < n) FComm k (tnth commit i) (tnth committed i) (tnth open i) (tnth opened i);

      \||_(i < n) Sim_CFParty k honest advCommit advOpen advCommitted advOpened i committed opened (tnth commit i) (tnth open i) ] ].

  Lemma SimComp_simpl7E out :
    SimComp_simpl6 out =0 SimComp_simpl7 out.
    rewrite /SimComp_simpl6.
    rewrite /SimComp_simpl7.
    apply EqNew_vec => open _ _.
    apply EqNew_vec => committed _ _.
    apply EqNew_vec => opened _ _.
    apply EqNew_vec => sum_commits _ _.
    rotate_news.
    apply EqNew_vec => sum_open _ _.
    rotate_news.
    apply EqNew_vec => commit _ _.
    symmetry.
    etransitivity.
    swap_tac 0 4.
    rewrite (bigpar_D1_ord ord_max).
    rewrite par_in_pars.
    rewrite /Sim_CFParty H.
    rewrite newPars.
    setoid_rewrite newPars.
    setoid_rewrite pars_pars.
    apply EqRefl.
    apply _.
    done.
    apply EqNew_vec => sum_committed _ _.
    apply EqNew_vec => sum_opened _ _.
    simpl.
    align.
 Qed.
End SimComp.

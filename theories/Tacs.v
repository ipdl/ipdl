(* This library develops the tactics useful for 
 performing proofs IPDL programs. *)


From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop fintype.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Base Ipdl.Exp Ipdl.Core Ipdl.Lems Lib.Dist Lib.Perm Lib.SeqOps Lib.TupleLems Lib.Set Ipdl.Big Ipdl.Approx Pars.

Ltac Intro :=
  match goal with
    | |- EqProt (_ <- new _ ;; _) _ => apply EqCongNew
    | |- EqProt (_ <- newvec _ @  _ ;; _) _ => apply EqCongNew_vec
    | |- AEqProt _ _ (_ <- new _ ;; _) _ => apply AEq_new
    | |- AEqProt _ _ (_ <- newvec _ @  _ ;; _) _ => apply AEq_newvec
                                                   end.


Ltac ensure_exact' t :=
match goal with
  | |- AEqProt _ _ _ _ => eapply exact_tr; [ t | ]
  | _ => t end.

Tactic Notation "ensure_exact" tactic(t) :=
  ensure_exact' t.

(* Swaps the i'th and j'th element of a pars *)

(* Focuses on editing the n'th element of a pars, as a rxn (needs to be a reaction) *)
Ltac edit_tac n :=
  ensure_exact ltac:(
    rewrite (pars_edit_out n); last first; 
    [ simpl; congr (_ _); congr (_ _ _) | idtac | rewrite /lset; simpl]).


(* Focuses on editing the n'th element of a pars *)
Ltac focus_tac n :=
  ensure_exact ltac:(
    rewrite (pars_edit n); last first; 
    [ simpl; congr (_ _); congr (_ _ _) | idtac | rewrite /lset //= ]).

(* Focuses on editing the n'th element of a pars *)

Ltac swap_at i n m :=
  ensure_exact ltac:(edit_tac i; [r_swap n m; reflexivity |]).


Lemma focus2_tacP {C} r1 r2 r' rs :
  EqProt (r1 ||| r2) r' ->
  @EqProt C (pars (r1 :: r2 :: rs)) (pars (r' :: rs)).
  intros.
  rewrite !pars_cons.
  rewrite EqCompAssoc.
  rewrite H; reflexivity.
Qed.

(* Requires first two to be in position *)
Ltac focus2_tac :=
  ensure_exact ltac:(etransitivity; [rewrite focus2_tacP; last first |]).

Ltac focus2_with i j :=
  ensure_exact ltac:(swap_tac 0 i; swap_tac 1 j; focus2_tac).

(*+ Deterministic inlining lemmas +*)


   Lemma new_pars_inline {chan} {t} {t'} (b : chan t') k r rs :
     isDet _ r ->
     EqProt (c <- new t ;; pars [:: (Out b (x <-- Read c ;; k x)), Out c r & rs c])
                      (c <- new t ;; pars [:: (Out b (x <-- r ;; k x)), Out c r & rs c]).
     intros.
     apply EqCongNew => c.
     focus2_tac.
     rewrite inline.
     done.
     done.
     done.
     rewrite par_in_pars //=.
   Qed.
   

Ltac find_in_lhs p :=
  match goal with
    | [ |- EqProt (pars ?rs) _ ] => find_in_pars_rec p rs 0
    | [ |- AEqProt _ _ (pars ?rs) _ ] => find_in_pars_rec p rs 0
  end.

Ltac inline_tac x y :=
  let i := find_in_lhs x in
  swap_tac 0 i;
  let j := find_in_lhs y in
  swap_tac 1 j;
  rewrite pars_inline //=.

(* Requires n to be index of single out *)
Ltac simp_at i :=
  ensure_exact ltac:(edit_tac i; [simp_rxn ; apply EqRxnRefl | idtac]).

Ltac simp_tac x :=
  let i := find_in_lhs x in
  edit_tac i; [simp_rxn; apply EqRxnRefl | idtac].

Ltac swap0_find_tac x :=
  let i := find_in_lhs x in
  swap_tac 0 i.

Ltac swap_in x n m :=
  let i := find_in_lhs x in
  edit_tac i; [r_swap n m; reflexivity |].


Ltac unused_tac y x :=
  let i := find_in_lhs y in
  swap_tac 0 i;
  let j := find_in_lhs x in
  swap_tac 1 j;
  rewrite pars_unused //=.

Ltac rename_to j :=
  match goal with
  | [ |- (newvec ?i ?t ?k) =p ?h] =>
    change (j <- newvec i @ t ;; k j =p h) end.


(* does r have a samp? returns bool *)
Ltac hasSamp r K :=
  lazymatch eval simpl in r with
  | @Samp _ _ _ => K constr:(true)
  | @Bind _ _ _ ?c ?k =>
    hasSamp c ltac:(fun j => 
        match j with
        | true => K constr:(true)
        | false =>
        match type of k with
        | ?t -> _ =>
            let y := eval simpl in (k witness) in
            hasSamp y K
        end
        end
     )
  | @Ret _ _ _ => K constr:(false)
  | @Read _ _ _ => K constr:(false)
  end.

(* does r read from c? and if so, what index? returns option nat *)
(* Assumes reaction is in associated form with no bare read *)
Ltac find_read_in_rxn_rec r c i K :=
  lazymatch eval simpl in r with
  | @Bind _ _ _ ?d ?k =>
    lazymatch d with
    | Read c => K constr:(Some i)
    | _ => find_read_in_rxn_rec (k witness) c (S i) K
    end
  | _ => K constr:(@None nat) end.

Ltac find_read_in_rxn r c K := find_read_in_rxn_rec r c 0 K.

    

(* Finds index in rs of reaction that reads from c, and the index in the reaction where c is read. returns option (nat * nat) *)
Ltac find_read_rec rs c i K :=
  let s := eval simpl in (List.nth_error rs i) in
  lazymatch s with
  | Some (Out _ ?r) =>
    find_read_in_rxn r c ltac:(fun b =>
                        match b with
                        | Some ?j => K constr:(Some (i, j))
                        | None => find_read_rec rs c (S i) K
                        end)
  | Some _ => find_read_rec rs c (S i) K                 
  | None => K constr:(@None (nat * nat))
  end.

Ltac find_read rs c K := find_read_rec rs c 0 K.

(* Finds index in rs of: deterministic reaction that's hidden, index of reaction that reads from it, and index in that reaction of the read. 
returns option (nat * nat * nat) *)
Ltac find_inline_info_rec rs i K :=
  let s := eval simpl in (List.nth_error rs i) in
  lazymatch s with
  | Some (Out ?c ?r) =>
      hasSamp r ltac:( fun b =>
                         lazymatch b with
                         | true => find_inline_info_rec rs (S i) K
                         | false =>
                           find_read rs c ltac:(fun p =>
                                                  lazymatch p with
                                                  | Some (?j, ?k) =>
                                                    K constr:((i, j, k))
                                                  | None =>
                                                    find_inline_info_rec rs (S i) K
                                                  end)
                         end )
  | Some _ => find_inline_info_rec rs (S i) K
  | None => fail
  end.

Ltac find_inline_info rs K := find_inline_info_rec rs 0 K.

Lemma pars_inline_rev {chan} {t t'} (b : chan t') (c : chan t) k r rs :
  isDet _ r ->
  pars [:: Out c r, Out b (x <-- Read c ;; k x) & rs] =p
  pars [:: Out c r, Out b (x <-- r ;; k x) & rs].
  intros.
  swap_tac 0 1.
  rewrite insert_0.
  rewrite pars_inline //=.
  swap_tac 0 1.
  rewrite insert_0.
  done.
Qed.

Ltac do_inline :=
  match goal with
  | [ |- EqProt (pars ?rs) _ ] =>
    find_inline_info rs ltac:(fun x =>
                                match x with
                                | (?i, ?j, ?k) =>
                                  swap_at j 0 k;
                                  swap_tac 1 i;
                                  swap_tac 0 j;
                                  (rewrite pars_inline; last first; [done | rewrite /lset /=; swap_tac 0 j; swap_tac 1 i]) + 
                                  (rewrite pars_inline_rev; last first; [done | rewrite /lset /=; swap_tac 0 j; swap_tac 1 i]) 
                                end )

  end.


Lemma Eq_Outvec {chan} {I} {t} (v : I.-tuple (chan t)) f1 f2 :
  (forall j, f1 j =r f2 j)  ->
  Outvec v f1 =p Outvec v f2.
  intros; apply EqProt_big_r; intros; apply EqCongReact.
  apply H.
Qed.

Ltac swap_Outvec_at i n m :=
  etransitivity; [ focus_tac i; apply Eq_Outvec; intros; r_swap n m; apply EqRxnRefl |].

Ltac simp_Outvec_at i :=
  etransitivity; [ focus_tac i; apply Eq_Outvec; intros; simp_rxn; apply EqRxnRefl |].


(* ***  Tactics for bigops *** *)


Ltac get_witness t K :=
  (K constr:(@witness t ltac:(apply _))) + (fail "Inhabited instance not found for" t).

(* does r read from c? and if so, what index? returns option nat *)
(* Assumes reaction is in associated form with no bare read *)
Ltac find_big_read_in_rxn_rec r v i K :=
  lazymatch eval simpl in r with
  | @Bind _ _ _ ?d ?k =>
    lazymatch d with
    | Read (tnth v _) => K constr:(Some i)
    | _ => find_big_read_in_rxn_rec (k witness) v (S i) K
    end
  | _ => K constr:(@None nat) end.

Ltac find_big_read_in_body f v K :=
  match type of f with
  | ?t -> _ =>
    get_witness t ltac:(fun x => 
                          find_big_read_in_rxn_rec (f x) v 0 K)
  end.

(* Finds index in rs of reaction that reads from c, and the index in the reaction where c is read. returns option (nat * nat) *)
Ltac find_big_read_rec rs v i K :=
  let s := eval simpl in (List.nth_error rs i) in
  lazymatch s with
  | Some (Outvec _ ?f) =>
    find_big_read_in_body f v ltac:(fun b =>
                        match b with
                        | Some ?j => K constr:(Some (i, j))
                        | None => find_big_read_rec rs v (S i) K
                        end)
  | Some _ => find_big_read_rec rs v (S i) K                 
  | None => K constr:(@None (nat * nat))
  end.

Ltac find_big_read rs v K := find_big_read_rec rs v 0 K.

Ltac find_big_inline_info_rec rs i K :=
  let s := eval simpl in (List.nth_error rs i) in
  lazymatch s with
  | Some (Outvec ?v ?f) =>
      hasSamp (f witness) ltac:( fun b =>
                         lazymatch b with
                         | true => find_big_inline_info_rec rs (S i) K
                         | false =>
                           find_big_read rs v ltac:(fun p =>
                                                  lazymatch p with
                                                  | Some (?j, ?k) =>
                                                    K constr:((i, j, k))
                                                  | None =>
                                                    find_big_inline_info_rec rs (S i) K
                                                  end)
                         end )
  | Some _ => find_big_inline_info_rec rs (S i) K
  | None => fail
  end.

Ltac find_big_inline_info rs K := find_big_inline_info_rec rs 0 K.

Ltac do_big_inline :=
  match goal with
  | [ |- EqProt (pars ?rs) _ ] =>
    find_big_inline_info rs ltac:(fun x =>
                                lazymatch x with
                                | (?i, ?j, ?k) =>
                                  swap_Outvec_at j 0 k;
                                  simpl;
                                  swap_tac 1 i;
                                  swap_tac 0 j;
                                  rewrite pars_big_inline //=
                                end )

  end.


(* Find unused hidden channels. *)

Ltac find_unused_rec rs i :=
  let r := eval simpl in (List.nth_error rs i) in
    lazymatch r with
    | Some (Outvec ?v _) =>
            lazymatch eval simpl in (SeqOps.remove rs i) with
                | context[v] => find_unused_rec rs (S i)
                | _ => constr:(Some i)
            end
    | Some (Out ?c _) =>
            lazymatch eval simpl in (SeqOps.remove rs i) with
                | context[c] => find_unused_rec rs (S i)
                | _ => constr:(Some i)
            end
    | Some _ => find_unused_rec rs (S i)
    | None => constr:(@None nat) end.                            

Ltac find_unused :=
  match goal with
    | [ |- EqProt (pars ?rs) _ ] => find_unused_rec rs 0 end.

Ltac unused_to_front :=
  etransitivity; [
    repeat match goal with
           | [ |- EqProt (New _ _) _ ] => apply EqCongNew; intro
           | [ |- EqProt (newvec _ _ _) _ ] => apply EqCongNew_vec; intro
    end; 
    let i := find_unused in
    match i with
      | None => idtac
      | Some ?j => swap_tac 0 j end; apply EqRefl |].


(* Manipulating new's *)

Ltac rotate_news :=
  etransitivity; [ 
  lazymatch goal with
  | [ |- EqProt (New _ (fun x => New _ _)) _ ] =>
    rewrite EqNewExch; apply EqCongNew; intro; rotate_news; apply EqRefl
  | [ |- EqProt (New _ (fun x => newvec _ _ _)) _ ] =>
    rewrite -New_newvec; apply EqCongNew_vec; intro; rotate_news; apply EqRefl
  | [ |- EqProt (newvec _ _ (fun x => newvec _ _ _)) _ ] =>
    rewrite newvec_newvec; apply EqCongNew_vec; intro; rotate_news; apply EqRefl
  | [ |- EqProt (newvec _ _ (fun x => New _ _)) _ ] =>
    rewrite New_newvec; apply EqCongNew; intro; rotate_news; apply EqRefl
    | _ => idtac                                                                 
                                                                 end | ].

(* Simplification *)

Ltac simp_all_rec rs i :=
  let s := eval simpl in (List.nth_error rs i) in
  lazymatch s with
  | Some (Out _ _) =>
    simp_at i; simp_all_rec rs (S i)
  | Some (Outvec _ _) =>
    simp_Outvec_at i; simp_all_rec rs (S i)
    | Some _ => simp_all_rec rs (S i)
    | None => idtac end.

Ltac simp_all' :=
  unfold copy in *;
  match goal with
  | [ |- AEqProt _ _ (pars ?xs) _ ] =>
    eapply exact_tr; [ simp_all_rec xs 0 | ]
    | [ |- EqProt (pars ?xs) _ ] => simp_all_rec xs 0 end.

Ltac simp_all :=
  match goal with
    | |- EqProt _ _ => simp_all'
    | |- AEqProt _ _ _ _ => simp_all'; [ apply EqRefl | ]
                                       end.

Ltac align_step :=
  match goal with
  | [ |- EqProt (pars ?lhs) (pars ?rhs) ] =>
    match rhs with
      | nil => idtac
      | ?r :: ?rhs' =>
        let i := lazymatch r with
                    | Out ?d _ => find_in_pars (Out d) lhs
                    | Outvec ?v _ => find_in_pars (Outvec v) lhs
                    | _ => find_in_pars r lhs end in
        swap_tac 0 i; apply pars_cons_cong; rewrite //=
    end
  end.

Ltac align := repeat align_step.

Lemma fold_outvecE {chan} {n} {t} (v : n.-tuple (chan t)) f :
  \||_(j < n) Out (tnth v j) (f j) = Outvec v f.
  done.
Qed.


                                          

(*** Old stuff that only works with EqProt ***)


Ltac under_new_rec t :=
  lazymatch goal with
  | [ |- EqProt (New _ _) _ ] =>
    t + (etransitivity; [ apply EqCongNew; intro; under_new_rec t | apply EqRefl ] )
  | [ |- EqProt (newvec _ _ _) _ ] =>
    t + (etransitivity; [ apply EqCongNew_vec; intro; under_new_rec t | apply EqRefl ] )
  | [ |- EqProt _ _ ] => t; apply EqRefl end.

Tactic Notation "under_new" tactic(t) :=
  (etransitivity; [under_new_rec t | idtac]).

Inductive PointsTo {chan} : forall t, ipdl -> chan t -> rxn t -> Type :=
| pt_Out t c r : PointsTo t (Out c r) c r
| pt_Par_l t c r p1 p2 : PointsTo t p1 c r  -> PointsTo t (Par p1 p2) c r
| pt_Par_r t c r p1 p2 : PointsTo t p2 c r  -> PointsTo t (Par p1 p2) c r
| pt_New t t2 (c : chan t) k r :
    (forall (c' : chan t2), PointsTo t (k c') c r) -> PointsTo t (New t2 k) c r.

Lemma pointsTo_inline {chan} t (c : chan t) rxn (r : ipdl) {t'} (c' : chan t') k :
  PointsTo t r c rxn ->
  isDet _ rxn ->
  Out c' (x <-- Read c ;; k x) ||| r =p
  Out c' (x <-- rxn ;; k x) ||| r.
  intros.
  induction X; subst.
  rewrite inline //=.
  rewrite EqCompAssoc.
  rewrite IHX //=.
  rewrite EqCompAssoc //=.
  rewrite (EqCompComm p1).
  rewrite EqCompAssoc.
  rewrite IHX //=.
  rewrite EqCompAssoc //=.
  rewrite newComp_r.
  etransitivity.
  apply EqCongNew; intros.
  rewrite H0 //=.
  apply EqRefl.
  rewrite newComp_r.
  done.
Qed.

Lemma pars_pointsTo_inline {chan} t (c : chan t) rxn (rs : seq ipdl) {t'} (c' : chan t') k :
  PointsTo t (pars rs) c rxn ->
  isDet _ rxn ->
  pars [::
    Out c' (x <-- Read c ;; k x) & rs] =p
  pars [::
    Out c' (x <-- rxn ;; k x) & rs].
  intros.
  rewrite pars_cons.
  rewrite (pointsTo_inline _ c rxn) //=.
Qed.

Lemma pars_PointsTo {chan} (i : nat) t (c : chan t) rxn (rs : seq ipdl) :
  PointsTo t  (nth prot0 rs i) c rxn ->
  PointsTo t  (pars rs) c rxn.
  move: t c rxn i.
  induction rs; intros.
  destruct i; simpl in X; inversion X.
  destruct i.
  simpl in *.
  apply pt_Par_l; done.
  apply pt_Par_r.
  eapply IHrs.
  apply X.
Qed.

Require Import Lib.OrdLems.

Lemma pointsTo_big_ord {chan} {n} {t} (i : 'I_n) (f : _ -> @ipdl chan) c r :
  PointsTo t (f i) c r ->
  PointsTo t (\||_(j < n) f j) c r.
  induction n.
  destruct i; done.
  destruct (ordP i); subst.
  rewrite big_ord_recl; apply pt_Par_l.
  rewrite big_ord_recl; intros; apply pt_Par_r.
  eapply IHn.
  apply X.
Qed.

Lemma pointsTo_par_inv {chan} {t} (c : chan t) r p q :
  PointsTo t (p ||| q) c r ->
  PointsTo t p c r + PointsTo t q c r.
  intro h; inversion h; subst.
  move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H3); intro; subst.
  move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H4); intro; subst.
  left; done.
  move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H3); intro; subst.
  move: (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ H4); intro; subst.
  right; done.
Qed.

Lemma pointsTo_front {chan} {t} (c : chan t) r p :
  PointsTo _ p c r ->
  { q : ipdl | p =p (c ::= r) ||| q }.
  intro h; induction h.
  exists prot0.
  rewrite -eq_par0 //=.
  destruct IHh.
  exists (x ||| p2).
  rewrite e.
  rewrite EqCompAssoc //=.

  destruct IHh.
  exists (x ||| p1).
  rewrite e.
  rewrite EqCompComm.
  rewrite EqCompAssoc //=.

  exists (New _ (fun x => proj1_sig (X x))).
  rewrite newComp_r.
  apply EqCongNew => c'.
  destruct (X c').
  simpl.
  done.
Qed.

Lemma pars_pointsTo_to_front {chan} {t} (c : chan t) r rs :
  PointsTo _ (pars rs) c r ->
  { rs' : seq ipdl | pars rs =p pars [:: c ::= r & rs' ] }.
  move/(@pointsTo_front chan).
  case => x Hx.
  exists [:: x].
  rewrite Hx.
  rewrite pars2 //=.
Qed.

Lemma pars3 {chan} p q r : p ||| q ||| r =p @pars chan [:: p; q; r].
  rewrite pars_cons.
  rewrite pars_cons.
  rewrite pars_cons.
  rewrite -eq_par0.
  done.
Qed.


Lemma pars_pointsTo_mkread {chan} {t1 t2 t3} (c : chan t1) r (c' : chan t2) (c'' : chan t3) rs k :
  PointsTo _ (pars rs) c r  ->
  reads_from c' r ->
  pars [:: c'' ::= (_ <-- Read c' ;; x <-- Read c ;; k x) & rs ] =p
  pars [:: c'' ::= (x <-- Read c ;; k x) & rs ]. 
  move/(@pointsTo_front chan).
  case; intros.
  rewrite !pars_cons.
  rewrite p.
  rewrite !EqCompAssoc.
  apply EqCongComp_l.
  symmetry.
  apply EqSubsume_reads_from.
  left; done.
  done.
Qed.

Inductive DependsOn {chan} : forall t1 t2, ipdl -> chan t1 -> chan t2 -> Prop :=
| DependsOn_base t1 t2 (c : chan t1) (c' : chan t2) r p :
    PointsTo _ p c r  -> reads_from c' r -> DependsOn _ _ p c c' 
| DependsOn_tr t1 t2 t3 (c : chan t1) (c' : chan t2) (c'' : chan t3) p :
    DependsOn _ _ p c c' -> DependsOn _ _ p c' c'' -> DependsOn _ _ p c c''.

Lemma pars_DependsOn_undep {chan} {t1 t2 t3} (c : chan t1) (c' : chan t2) (c'' : chan t3) rs r :
  DependsOn _ _ (pars rs) c c' ->
  pars [::
          c'' ::= (_ <-- Read c';; x <-- Read c ;; r x) & rs] =p
  pars [::
          c'' ::= (x <-- Read c ;; r x) & rs].
  intro h.
  remember (pars rs) as p.
  induction h; subst.
  eapply pars_pointsTo_mkread.
  apply X.
  done.
  rewrite -IHh1 //=.
  rewrite -IHh2 //=.
  symmetry.
  edit_tac 0.
  r_swap 0 1.
  r_swap 1 2.
  done.
  rewrite insert_0.
  rewrite IHh1 //=.
  apply pars_cons_cong.
  apply EqCongReact.
  r_swap 0 1.
  done.
  done.
Qed.


Lemma DependsOn_par_l {chan} {t1 t2} (c : chan t1) (c' : chan t2) p q :
  DependsOn _ _ p c c' ->
  DependsOn _ _ (p ||| q) c c'.
  intro h; induction h.
  eleft.
  apply pt_Par_l.
  apply X.
  done.
  eright.
  apply IHh1.
  done.
Qed.

Lemma DependsOn_par_r {chan} {t1 t2} (c : chan t1) (c' : chan t2) p q :
  DependsOn _ _ p c c' ->
  DependsOn _ _ (q ||| p) c c'.
  intro h; induction h.
  eleft.
  apply pt_Par_r.
  apply X.
  done.
  eright.
  apply IHh1.
  done.
Qed.

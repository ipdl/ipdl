
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq tuple.
From mathcomp Require Import choice path bigop fintype.
Require Import FunctionalExtensionality Classes.Equivalence.
Require Import Lib.Base Ipdl.Exp Ipdl.Core Ipdl.Lems Lib.Dist Lib.Perm Lib.SeqOps Lib.TupleLems Lib.Set Ipdl.Big Pars.

     

(*+ Simple permutation lemmas/tacs +*)

Ltac under_new_rec t :=
  lazymatch goal with
  | [ |- EqProt (New _ _) _ ] =>
    t + (etransitivity; [ apply EqNew; intro; move => _ _; under_new_rec t | apply EqRefl ] )
  | [ |- EqProt (newvec _ _ _) _ ] =>
    t + (etransitivity; [ apply EqNew_vec; intro; move => _ _; under_new_rec t | apply EqRefl ] )
  | [ |- EqProt _ _ ] => t; apply EqRefl end.

Tactic Notation "under_new" tactic(t) :=
  (etransitivity; [under_new_rec t | idtac]).
 

Close Scope bool_scope.
Require Import Morphisms.

Check newvec.

                         

Ltac edit_new :=
  apply EqNew.

(* Focus in on editing the left side of a composition *)
Ltac edit_left :=
  apply EqPar_l.

(* Focus in on editing the right side of a composition *)
Ltac edit_right :=
  apply EqPar.


(* Substitutes the nth reaction into the mth *)

Open Scope bool_scope.
Ltac edit_big :=
  apply EqProt_big_r.


(* Swaps the i'th and j'th element of a pars *)

(* Focuses on editing the n'th element of a pars, as a rxn (needs to be a reaction) *)
Ltac edit_tac n :=
  rewrite (pars_edit_out n); last first; 
  [ rewrite //=; congr (_ _); congr (_ _ _) | idtac | rewrite /lset //=].

(* Focuses on editing the n'th element of a pars *)
Ltac focus_tac n :=
  rewrite (pars_edit n); last first; 
  [ rewrite //=; congr (_ _); congr (_ _ _) | idtac | rewrite /lset //=].

Ltac edit_tac' n :=
  let i := get_idx n in 
  rewrite (pars_edit_out i); last first; 
  [ simpl; congr (_ _); congr (_ _ _) | idtac | rewrite /lset //=].

(* Focuses on editing the n'th element of a pars *)

Ltac swap_at i n m :=
  edit_tac' i; [r_swap n m; reflexivity |].

Lemma focus2_tacP r1 r2 r' rs :
  EqProt (r1 ||| r2) r' ->
  EqProt (pars (r1 :: r2 :: rs)) (pars (r' :: rs)).
  intros.
  rewrite !pars_cons.
  rewrite ParAssoc.
  rewrite H; reflexivity.
Qed.

(* Requires first two to be in position *)
Ltac focus2_tac :=
  etransitivity; [rewrite focus2_tacP; last first |].

Ltac focus2_with i j :=
  swap_tac 0 i; swap_tac 1 j; focus2_tac.

(*+ Deterministic inlining lemmas +*)


   Lemma new_pars_inline {t} {t'} (b : chan t') k r rs :
     isDet _ r ->
     EqProt (c <- new t ;; pars [:: (Out b (x <-- Read c ;; k x)), Out c r & rs c])
                      (c <- new t ;; pars [:: (Out b (x <-- r ;; k x)), Out c r & rs c]).
     intros.
     apply EqNew => c _ _.
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
  end.

Ltac inline_tac x y :=
  let i := find_in_lhs x in
  swap_tac 0 i;
  let j := find_in_lhs y in
  swap_tac 1 j;
  rewrite pars_inline //=.


(* Requires n to be index of single out *)
Ltac simp_at i :=
  edit_tac i; [simp_rxn ; apply EqRxnRefl | idtac].


Ltac simp_tac x :=
  let i := find_in_lhs x in
  edit_tac i; [simp_rxn; apply EqRxnRefl | idtac].

Ltac swap0_find_tac x :=
  let i := find_in_lhs x in
  swap_tac 0 i.

Ltac swap_in x n m :=
  let i := find_in_lhs x in
  edit_tac' i; [r_swap n m; reflexivity |].


(*+ Undep +*)


Ltac undep_tac y x :=
  let i := find_in_lhs y in
  swap_tac 0 i;
  let j := find_in_lhs x in
  swap_tac 1 j;
  rewrite pars_undep //=.

(*+ Lemmas about new / respectful contexts +*)


Require Import Lib.Crush.

Ltac notin_inv :=
  unfold In in *; match goal with
  | [ H : ~ (chans (newvec _ _ _)) _ |- _] =>
    move/notin_newvec: H; elim; intros
  | [ H : ~ (chans (Par _ _)) _ |- _ ] => simpl in H; set_tac
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : ~ (chans (pars _)) _ |- _ ] => simpl in H
  | [ H : ~ (chans (New _ _)) _ |- _] =>
    move/notin_newP :H; elim; intros
                                         end.

Inductive PointsTo : forall t, rset -> chan t -> rxn t -> Prop :=
| pt_Out t c r : PointsTo t (Out c r) c r
| pt_Par_l t c r p1 p2 : PointsTo t p1 c r  -> PointsTo t (Par p1 p2) c r
| pt_Par_r t c r p1 p2 : PointsTo t p2 c r  -> PointsTo t (Par p1 p2) c r
| pt_New t t2 (c : chan t) k r : (forall (c' : chan t2), mkChan c' <> mkChan c -> PointsTo t (k c') c r) -> PointsTo t (New t2 k) c r.

Lemma pointsTo_inline t (c : chan t) rxn (r : rset) {t'} (c' : chan t') k :
  PointsTo t r c rxn ->
  isDet _ rxn ->
  Out c' (x <-- Read c ;; k x) ||| r ~=
  Out c' (x <-- rxn ;; k x) ||| r.
  intros.
  induction H; subst.
  rewrite inline //=.
  rewrite ParAssoc.
  rewrite IHPointsTo //=.
  rewrite ParAssoc //=.
  rewrite (ParSym p1).
  rewrite ParAssoc.
  rewrite IHPointsTo //=.
  rewrite ParAssoc //=.
  rewrite newComp_r.
  etransitivity.
  apply EqNew; intros.
  rewrite H1 //=.
  apply EqRefl.
  simpl in H3.
  move: (mkFresh _ [:: c0]); elim => c3 Hc3.
  repeat set_tac.
  rewrite newComp_r.
  done.
Qed.

Lemma pars_pointsTo_inline t (c : chan t) rxn (rs : seq rset) {t'} (c' : chan t') k :
  PointsTo t (pars rs) c rxn ->
  isDet _ rxn ->
  pars [::
    Out c' (x <-- Read c ;; k x) & rs] ~=
  pars [::
    Out c' (x <-- rxn ;; k x) & rs].
  intros.
  rewrite pars_cons.
  rewrite (pointsTo_inline _ c rxn) //=.
Qed.

Lemma pars_PointsTo (i : nat) t (c : chan t) rxn (rs : seq rset) :
  PointsTo t  (nth prot0 rs i) c rxn ->
  PointsTo t  (pars rs) c rxn.
  move: t c rxn i.
  induction rs; intros.
  destruct i; simpl in H; inversion H.
  destruct i.
  simpl in *.
  apply pt_Par_l; done.
  apply pt_Par_r.
  eapply IHrs.
  apply H.
Qed.

Require Import Lib.OrdLems.

Lemma pointsTo_big_ord {n} {t} (i : 'I_n) f c r :
  PointsTo t (f i) c r ->
  PointsTo t (\||_(j < n) f j) c r.
  induction n.
  destruct i; done.
  destruct (ordP i); subst.
  rewrite big_ord_recl; apply pt_Par_l.
  rewrite big_ord_recl; intros; apply pt_Par_r.
  eapply IHn.
  apply H.
Qed.

Check pars_undep.


Require Import Lib.Crush.

Ltac rename_to j :=
  match goal with
  | [ |- (newvec ?i ?t ?k) ~= ?h] =>
    change (j <- newvec i @ t ;; k j ~= h) end.

Lemma mkdep_pointsTo {t1 t2} (c1 : chan t1) (c2 : chan t2) R r r' :
  PointsTo _ R c1 r ->
  List.Forall (In (rxn_inputs r')) (rxn_inputs r) ->
  (Out c2 r') ||| R ~=
  (Out c2 (_ <-- Read c1 ;; r')) ||| R. 
  intros.
  induction H.
  symmetry; rewrite ParSym.
  rewrite RUndep.
  rewrite ParSym //=.
  done.
  rewrite ParAssoc.
  rewrite IHPointsTo.
  rewrite ParAssoc //=.
  done.
  rewrite (ParSym p1).
  rewrite ParAssoc.
  rewrite IHPointsTo.
  rewrite ParAssoc //=.
  done.
  rewrite newComp_r.
  rewrite newComp_r.
  apply EqNew; intros.
  rewrite H1.
  done.
  repeat notin_inv; eauto.
  done.
Qed.

Lemma pars_mkdep_pointsTo {t1 t2} (c1 : chan t1) (c2 : chan t2) R r r' :
  PointsTo _ (pars R) c1 r ->
  List.Forall (In (rxn_inputs r')) (rxn_inputs r) ->
  pars [:: Out c2 r' & R] ~=
  pars [:: (Out c2 (_ <-- Read c1 ;; r')) & R]. 
  intros; rewrite pars_cons.
  rewrite mkdep_pointsTo.
  rewrite -pars_cons.
  done.
  apply H.
  done.
Qed.

Lemma trans_dep_pointsTo {t1 t2 t3} (a : chan t1) (m : chan t3) (r1 : rxn t1) r2 (b : chan t2) R:
  PointsTo _ R a r1 ->
  In  (rxn_inputs r1) (mkChan m) ->
  In  (rxn_inputs r2) (mkChan a) ->
  wfRxn r2 ->
  Out b r2 ||| R ~= Out b (_ <-- Read m;; r2) ||| R.
  intros.
  induction H.
  rewrite ParSym.
  symmetry; rewrite ParSym; symmetry.
  apply RTr.
  done.
  done.
  done.
  rewrite ParAssoc IHPointsTo //= ParAssoc //=.
  rewrite (ParSym p1).
  rewrite ParAssoc IHPointsTo //= ParAssoc //=.
  rewrite !newComp_r.
  apply EqNew; intros.
  apply H3.
  repeat notin_inv.
  simpl in H5.
  repeat set_tac.
  intro.
  congruence.
  done.
  done.
Qed.


Lemma pars_trans_dep_pointsTo {t1 t2 t3} (a : chan t1) (m : chan t3) (r1 : rxn t1) r2 (b : chan t2) R :
  In (rxn_inputs r1)  (mkChan m) ->
  In (rxn_inputs r2) (mkChan a)  ->
  wfRxn r2 ->
  PointsTo _ (pars R) a r1 ->
  pars [:: Out b r2 & R] ~= pars [:: Out b (_ <-- Read m;; r2) & R].
  intros.
  rewrite !pars_cons.
  intros; eapply trans_dep_pointsTo.
  apply H2.
  done.
  done.
  done.
Qed.



(* 
Lemma pars_trans_dep_include {t1 t2} (a : chan t1) (r1 : rxn t1) r2 (b : chan t2) R :
  List.In (mkChan a) (rxn_inputs r2) ->
  PointsTo _ (pars R) a r1 ->
  pars [:: Out b r2 & R] ~= pars [:: Out b (_ <-- r1;; r2) & R].
*)

(*    new tactics for automation *)

(* does r have a samp? returns bool *)
Ltac hasSamp r K :=
  lazymatch eval simpl in r with
  | Unif _ => K constr:(true)
  | @Samp _ _ => K constr:(true)
  | @Bind _ _ ?c ?k =>
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
  | @Ret _ _ => K constr:(false)
  | @Read _ _ => K constr:(false)
  end.

(* does r read from c? and if so, what index? returns option nat *)
(* Assumes reaction is in associated form with no bare read *)
Ltac find_read_in_rxn_rec r c i K :=
  lazymatch eval simpl in r with
  | @Bind _ _ ?d ?k =>
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

Lemma pars_inline_rev {t t'} (b : chan t') (c : chan t) k r rs :
  isDet _ r ->
  pars [:: Out c r, Out b (x <-- Read c ;; k x) & rs] ~=
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


Lemma Eq_Outvec {I} {t} (v : I.-tuple (chan t)) f1 f2 :
  (forall j, f1 j =r f2 j)  ->
  Outvec v f1 ~= Outvec v f2.
  intros; apply EqProt_big_r; intros; apply EqOut.
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
  | @Bind _ _ ?d ?k =>
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
           | [ |- EqProt (New _ _) _ ] => apply EqNew; intro => _ _
           | [ |- EqProt (newvec _ _ _) _ ] => apply EqNew_vec; intro => _ _
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
    rewrite NewNew; apply EqNew; intro => _ _; rotate_news; apply EqRefl
  | [ |- EqProt (New _ (fun x => newvec _ _ _)) _ ] =>
    rewrite -New_newvec; apply EqNew_vec; intro => _ _; rotate_news; apply EqRefl
  | [ |- EqProt (newvec _ _ (fun x => newvec _ _ _)) _ ] =>
    rewrite newvec_newvec; apply EqNew_vec; intro => _ _; rotate_news; apply EqRefl
  | [ |- EqProt (newvec _ _ (fun x => New _ _)) _ ] =>
    rewrite New_newvec; apply EqNew; intro => _ _; rotate_news; apply EqRefl
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

Ltac simp_all :=
  unfold copy in *;
  match goal with
    | [ |- EqProt (pars ?xs) _ ] => simp_all_rec xs 0 end.

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

Lemma fold_outvecE {n} {t} (v : n.-tuple (chan t)) f :
  \||_(j < n) Out (tnth v j) (f j) = Outvec v f.
  done.
Qed.


                                          

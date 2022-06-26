

Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Ipdl.Big Pars Typ.

Require Import Permutation Lib.Perm Lib.SeqOps.
Lemma perm_eq_skip {A} (x y : A) (xs ys : seq A) :
  x = y ->
  Permutation xs ys ->
  Permutation (x :: xs) (y :: ys).
  intros; subst.
  apply perm_skip; done.
Qed.

Require Import GMWIdeal OTIdeal Circ.
Require Import Eqdep.

Definition close {chan : Type -> Type} {t} (c : chan t) := (c ::= Read c).

Section GenOTChannels.
  Context {chan : Type -> Type}.
  Record OTChannels :=
    mkOTChannels {
      ot_i : chan (bool * bool);
      ot_m : chan ((bool * bool) * (bool * bool));
      ot_o : chan bool;
      ot_leakBit : chan bool (* Leakage channel for alice *)
                  }.

  Print withOT14.
  Check mktuple.

  Definition withOTs L (leak : L.-tuple (chan bool)) (P : L.-tuple (OTChannels) -> @ipdl chan) : @ipdl chan :=
    ins <- newvec L @ (bool * bool);;
    m <- newvec L @ ((bool * bool) * (bool * bool));;
    o <- newvec L @ bool;;
    pars [:: 
            \||_(i < L) (OT14Ideal bool (ins ## i) (m ## i) (o ## i));
            P (mktuple (fun i => mkOTChannels (ins ## i) (m ## i) (o ## i) (leak ## i)))
      ].
End GenOTChannels.

Definition pair4 {A} (f : bool -> bool -> A) : (A * A) * (A * A) :=
    ((f false false, f false true), (f true false, f true true)).

Section Init.
  Context {chan : Type -> Type}.
  Context (A B : nat).
  Open Scope bool_scope.

  Definition initAlice (inA leakAdv a2b leaka2b a2a : A.-tuple (chan bool)) (b2a leakb2a : B.-tuple (chan bool)) :=
    pars [::
            Outvec a2b (fun j => _ <-- Read (tnth inA j) ;; y <-- Samp Unif ;; Ret y) ;
            Outvec a2a (fun j => a <-- Read (tnth inA j) ;; b <-- Read (tnth a2b j) ;; Ret (a (+) b : bool));
            copy_tup inA leakAdv;
            copy_tup a2b leaka2b;
            copy_tup b2a leakb2a].
          
  Definition initBob (inB b2a b2b : B.-tuple (chan bool)) :=
    pars [::
            Outvec b2a (fun j => _ <-- Read (tnth inB j) ;; y <-- Samp Unif ;; Ret y) ;
            Outvec b2b (fun j => a <-- Read (tnth inB j) ;; b <-- Read (tnth b2a j) ;; Ret (a (+) b : bool)) ].

End Init.

Section GMWDefs.
  Context {chan : Type -> Type}.
  Open Scope bool_scope.

Definition alice_and 
           (x y : chan bool) 
           (leakOTBit : chan bool)
           (ot_m : chan ((bool * bool) * (bool * bool)))
           (z : chan bool) :=
  r <- new bool ;;
  pars [::
          Out r (Samp Unif) ;
          Out leakOTBit (copy r);
          Out ot_m (
                r <-- Read r ;;
                x <-- Read x ;;
                y <-- Read y ;;
                Ret (pair4 (fun i j =>
                               (x && j)
                                 (+)
                                 (y && i)
                                 (+)
                                 r : bool) ));
          Out z (
                r <-- Read r ;;
                x <-- Read x ;;
                y <-- Read y ;;
                Ret (r (+) ( x && y) : bool))].


Definition bob_and
           (x y : chan bool)
           (ot_i : chan (bool * bool))
           (ot_o : chan bool)
           (z : chan bool) :=
  pars [::
          Out ot_i (
            x <-- Read x ;;
            y <-- Read y ;;
            Ret ( x, y ) );
          Out z (
                b <-- Read ot_o ;;
                x <-- Read x ;;
                y <-- Read y ;;
                Ret ((x && y) (+) b : bool ))].


Definition performOp {A B n} (me : party) (o : Op A B n) (otc : OTChannels)
           (aliceIn : A.-tuple (chan bool)) (bobIn : B.-tuple (chan bool))
           (wires : n.-tuple (chan bool)) (w : chan bool) :=
  match o with
  | InA a => Out w (copy (tnth aliceIn a))
  | InB a => Out w (copy (tnth bobIn a))
  | Xor x y =>
    Out w (a <-- Read (tnth wires x) ;; b <-- Read (tnth wires y) ;; Ret (a (+) b : bool)) 
  | Not x =>
    Out w (
          x <-- Read (tnth wires x) ;;
          Ret (if me == alice then ~~ x : bool else x : bool))
  | And x y =>
    if me == alice then
      alice_and (tnth wires x) (tnth wires y) (ot_leakBit otc) (ot_m otc) w
    else
      bob_and (tnth wires x) (tnth wires y) (ot_i otc) (ot_o otc) w end.

Definition close_ots {A B n} (me : party) (o : Op A B n) (otc : @OTChannels chan) :=
  match o with
    | And _ _ => prot0
    | _ => if me == alice then pars [:: close (ot_leakBit otc); close (ot_m otc)]
                          else close (ot_i otc) end.

Definition performComp {A B n} (me : party) (c : Circ A B n) (ots : n.-tuple OTChannels)
           (aliceIn : A.-tuple (chan bool)) (bobIn : B.-tuple (chan bool))
           (wires : n.-tuple (chan bool)) :=
  \||_(j < n) pars [::
                 performOp me (c j) (ots ## j) aliceIn bobIn (tuple_trunc wires j) (tnth wires j);
                 close_ots me (c j) (ots ## j)]
               .


Definition performOuts {n o} (outs : circOuts n o) (wires : n.-tuple (chan bool))
           (outputs sendOutShares recvOutShares : o.-tuple (chan bool)) :=
  pars [::
          Outvec sendOutShares (fun j => copy (tnth wires (tnth outs j)));
          Outvec outputs (fun j =>
                            x <-- Read (tnth wires (tnth outs j)) ;;
                            y <-- Read (tnth recvOutShares j) ;;
                            Ret (x (+) y : bool))].

Definition aliceReal {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (AIn : A.-tuple (chan bool))
           (AOut : o.-tuple (chan bool))
           (ots : n.-tuple OTChannels)
           (a2b_init : A.-tuple (chan bool))
           (b2a_init : B.-tuple (chan bool))
           (leakAdv_AIn : A.-tuple (chan bool))
           (leakAdv_a2b : A.-tuple (chan bool))
           (leakAdv_b2a : B.-tuple (chan bool))
           (a2b_final : o.-tuple (chan bool))
           (b2a_final : o.-tuple (chan bool))
           (leakAdv_b2a_final : o.-tuple (chan bool))
  :=
  a2a <- newvec A @ bool ;;
  aliceWires <- newvec n @ bool ;;
  pars [::
          initAlice _ _ AIn leakAdv_AIn a2b_init leakAdv_a2b a2a b2a_init leakAdv_b2a ;
          performComp alice c ots a2a b2a_init aliceWires ;
          performOuts outs aliceWires AOut a2b_final b2a_final;
          copy_tup b2a_final leakAdv_b2a_final ].
          
Definition bobReal {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (BIn : B.-tuple (chan bool))
           (BOut : o.-tuple (chan bool))
           (ots : n.-tuple OTChannels)
           (b2a_init : B.-tuple (chan bool))
           (a2b_init : A.-tuple (chan bool))
           (b2a_final : o.-tuple (chan bool))
           (a2b_final : o.-tuple (chan bool))
  :=
    b2b <- newvec B @ bool ;;
    bobWires <- newvec n @ bool ;;
    pars [::
            initBob _ BIn b2a_init b2b;
            performComp bob c ots a2b_init b2b bobWires;
            performOuts outs bobWires BOut b2a_final a2b_final ].

Definition GMWReal {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (AIn : A.-tuple (chan bool))
           (BIn : B.-tuple (chan bool))
           (AOut BOut : o.-tuple (chan bool))
           (leakOTs : n.-tuple (chan bool)) 
           (leak_AIn : A.-tuple (chan bool))
           (leakInit_a2b : A.-tuple (chan bool))
           (leakInit_b2a : B.-tuple (chan bool))
           (leakFinal_b2a : o.-tuple (chan bool))
  :=
    withOTs _ leakOTs (fun ots =>
                         a2b_init <- newvec A @ bool ;;
                         b2a_init <- newvec B @ bool ;;
                         a2b_final <- newvec o @ bool ;;
                         b2a_final <- newvec o @ bool ;;
                         pars [::
                                 aliceReal c outs AIn AOut ots a2b_init b2a_init leak_AIn leakInit_a2b leakInit_b2a a2b_final b2a_final leakFinal_b2a ;
                              bobReal c outs BIn BOut ots b2a_init a2b_init b2a_final a2b_final

                      ] ).
                         
  
(* Typing lemmas *)



  
Lemma eq_tupleP {A} {n} (x y : n.-tuple A) :
  x = y -> (x : list A) = y.
  destruct x, y.
  rewrite //=.
  intro.
  inversion H; done.
Qed.


Lemma withOTs_t L (leak : L.-tuple (chan bool)) (P : L.-tuple (OTChannels) -> ipdl) o :
  (forall (v : L.-tuple OTChannels), [tuple of map ot_leakBit v] = leak -> ipdl_t (tags leak ++ tags [tuple of map ot_i v] ++ tags [tuple of map ot_m v] ++ o) (P v)) ->
  ipdl_t (tags leak ++ o) (withOTs L leak P).
  intros.
  rewrite /withOTs.
  repeat type_tac.
  rewrite /OT14Ideal.
  repeat type_tac.
  apply H.
  simpl.
  rewrite tupleE //=.
  apply eq_tuple.
  rewrite //=.
  rewrite -map_comp /comp //=.
  rewrite map_tnth_enum //=.
  simpl.
  rewrite !catA.
  cat_perm_tac.
  apply perm_eq_skip.
  rewrite flatten_map1.
  rewrite map_comp map_tnth_enum //=.

  setoid_rewrite (SeqOps.Perm_swap 0 2) at 1; rewrite /SeqOps.swap //= /SeqOps.lset //=.
  apply perm_skip.
  apply perm_eq_skip.
  rewrite tupleE //=.
  congr (_ _).
  apply eq_tuple; rewrite //= -map_comp /comp //= map_tnth_enum //=.
  apply perm_eq_skip.
  rewrite tupleE //=.
  congr (_ _).
  apply eq_tuple; rewrite //= -map_comp /comp //= map_tnth_enum //=.
  done.
Qed.

Lemma aliceReal_t {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (AIn : A.-tuple (chan bool))
           (AOut : o.-tuple (chan bool))
           (ots : n.-tuple OTChannels)
           (a2b_init : A.-tuple (chan bool))
           (b2a_init : B.-tuple (chan bool))
           (leakAdv_AIn : A.-tuple (chan bool))
           (leakAdv_a2b : A.-tuple (chan bool))
           (leakAdv_b2a : B.-tuple (chan bool))
           (a2b_final : o.-tuple (chan bool))
           (b2a_final : o.-tuple (chan bool))
           (leakAdv_b2a_final : o.-tuple (chan bool)) :
  ipdl_t (tags AOut ++ tags a2b_init ++ tags leakAdv_AIn ++ tags leakAdv_a2b ++ tags leakAdv_b2a ++ tags a2b_final ++ tags leakAdv_b2a_final ++ (map (fun i => tag (ot_m (ots ## i))) (enum 'I_n))
                ++ (map (fun i => tag (ot_leakBit (ots ## i))) (enum 'I_n))) (aliceReal c outs AIn AOut ots a2b_init b2a_init leakAdv_AIn leakAdv_a2b leakAdv_b2a a2b_final b2a_final leakAdv_b2a_final).
    rewrite /aliceReal.
    apply newvec_t => a2a.
    apply newvec_t => aliceWires.
  
  rewrite /aliceReal /initAlice /copy_tup /performComp /performOp /close_ots /performOuts /bobReal /initBob /performComp /performOp /close_ots /performOuts.
  rewrite /alice_and /close.
  repeat type_tac.
  instantiate (1 := match c i with
                    | And _ _ =>
                      [::
                        tag (ot_leakBit (ots ## i));
                         tag (ot_m  (ots ## i));
                          tag (aliceWires ## i)]
                    | _ => [:: tag (aliceWires ## i) ] end).
  destruct (c i); repeat type_tac.
  instantiate (1 := match c i with
                    | And _ _ => nil
                    | _ => [:: tag (ot_leakBit (ots ## i));
                               tag (ot_m (ots ## i))] end).
  destruct (c i); repeat type_tac.
  instantiate (1 := fun i => [:: tag (ot_leakBit (ots ## i));
                     tag (ot_m (ots ## i));
                     tag (aliceWires ## i)]).
  simpl.
  destruct (c i); simpl; perm_match.
  rewrite !flatten_map_cons flatten_map_nil.
  rewrite cats0.
  rewrite !catA.
  rewrite !mkFlattenE.
  apply Permutation_flatten.
  repeat perm_match_step.
  rewrite map_tag_enum.
  setoid_rewrite (Perm_swap 0 3) at 1; rewrite /swap //= /lset //=.
  apply perm_skip.
  setoid_rewrite (Perm_swap 0 2) at 1; rewrite /swap //= /lset //=.
Qed.
  
Lemma bobReal_t {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (BIn : B.-tuple (chan bool))
           (BOut : o.-tuple (chan bool))
           (ots : n.-tuple OTChannels)
           (b2a_init : B.-tuple (chan bool))
           (a2b_init : A.-tuple (chan bool))
           (b2a_final : o.-tuple (chan bool))
           (a2b_final : o.-tuple (chan bool)) :
  ipdl_t (tags BOut ++ tags b2a_init ++ tags b2a_final ++ map (fun i => tag (ot_i (ots ## i))) (enum 'I_n)) (bobReal c outs BIn BOut ots b2a_init a2b_init b2a_final a2b_final).
  rewrite /aliceReal /initAlice /copy_tup /performComp /performOp /close_ots /performOuts /bobReal /initBob /performComp /performOp /close_ots /performOuts /bob_and /close.
  repeat type_tac.
  instantiate (1 :=
                 match c i with
                 | And _ _ => [:: tag (ot_i (ots ## i)); tag (cs0 ## i)]
                 | _ => [:: tag (cs0 ## i)] end).
  destruct (c i); repeat type_tac.
  instantiate (1 := match c i with
                    | And _ _ => nil
                    | _ => [:: tag (ot_i (ots ## i))] end).
  destruct (c i); repeat type_tac.
  instantiate (1 := fun i => [:: tag (ot_i (ots ## i)); tag (cs0 ## i)]).
  simpl; destruct (c i); repeat type_tac; rewrite perm_swap //=.
  rewrite !flatten_map_cons !flatten_map_nil !cats0.
  rewrite !catA.
  rewrite !mkFlattenE.
  apply Permutation_flatten.
  setoid_rewrite (Perm_swap 0 3) at 1; rewrite /swap //= /lset //=; apply perm_skip.
  apply perm_skip.
  setoid_rewrite (Perm_swap 0 3) at 1; rewrite /swap //= /lset //=; apply perm_skip.
  rewrite map_tag_enum.
  apply perm_skip.
  done.
Qed.
           
Definition GMWReal_t {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (AIn : A.-tuple (chan bool))
           (BIn : B.-tuple (chan bool))
           (AOut BOut : o.-tuple (chan bool))
           (leakOTs : n.-tuple (chan bool)) 
           (leak_AIn : A.-tuple (chan bool))
           (leakInit_a2b : A.-tuple (chan bool))
           (leakInit_b2a : B.-tuple (chan bool))
           (leakFinal_b2a : o.-tuple (chan bool)) :
  ipdl_t (tags leakOTs ++ tags AOut ++ tags BOut ++ tags leak_AIn ++ tags leakInit_a2b ++ tags leakInit_b2a ++ tags leakFinal_b2a) (GMWReal c outs AIn BIn AOut BOut leakOTs leak_AIn leakInit_a2b leakInit_b2a leakFinal_b2a).
  rewrite /GMWReal.
  eapply withOTs_t; intros.
  eapply newvec_t; intro a2b_init.
  eapply newvec_t; intro b2a_init.
  eapply newvec_t; intro a2b_final.
  eapply newvec_t; intro b2a_final.
  eapply par_t.
  apply aliceReal_t.
  eapply par_t.
  apply bobReal_t.
  apply zero_t.
  rewrite cats0; done.
  rewrite /tags -map_comp /comp //=.
  rewrite !catA !mkFlattenE.
  apply Permutation_flatten.
  repeat perm_match_step.
  rewrite -map_comp /comp //=.
  symmetry.
  repeat perm_match_step.
  setoid_rewrite (Perm_swap 0 2) at 1; rewrite /swap //= /lset //=.
  rewrite !(map_tnth_enum_map (fun x => tag (ot_i x))).
  rewrite !(map_tnth_enum_map (fun x => tag (ot_m x))).
  apply perm_skip.
  rewrite perm_swap.
  rewrite -H map_comp /comp //=.
  rewrite map_tnth_enum_map.
  done.
Qed.

End GMWDefs.

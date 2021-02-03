

Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun fintype.
From mathcomp Require Import choice path bigop.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Tacs Lib.setoid_bigop Ipdl.Big Pars.

Require Import GMWIdeal OTIdeal Circ.
Require Import Eqdep.

Section GenOTChannels.
  Record OTChannels :=
    mkOTChannels {
      ot_i : chan (TBool ** TBool);
      ot_m : chan ((TBool ** TBool) ** (TBool ** TBool));
      ot_o : chan TBool;
      ot_leakBit : chan TBool (* Leakage channel for alice *)
                  }.

  Program Fixpoint withOTs L (leak : L.-tuple (chan TBool)) (P : L.-tuple OTChannels -> rset) : rset :=
    match L with
    | 0 => P [tuple]
    | S L' =>
      withOT14 TBool (fun i m o =>
                    withOTs L' [tuple of behead leak]
                            (fun v => P [tuple of (mkOTChannels i m o (thead leak)) :: v])) end.

End GenOTChannels.

Definition pair4 {A : type} (f : bool -> bool -> A) : (A ** A) ** (A ** A) :=
    ((f false false, f false true), (f true false, f true true)).

Section Init.
  Context (A B : nat).

  Definition initAlice (inA leakAdv a2b leaka2b a2a : A.-tuple (chan TBool)) (b2a leakb2a : B.-tuple (chan TBool)) :=
    pars [::
            Outvec a2b (fun j => _ <-- Read (tnth inA j) ;; y <-- Unif TBool ;; Ret y) ;
            Outvec a2a (fun j => a <-- Read (tnth inA j) ;; b <-- Read (tnth a2b j) ;; Ret (a (+) b : TBool));
            copy_tup inA leakAdv;
            copy_tup a2b leaka2b;
            copy_tup b2a leakb2a].
          
  Definition initBob (inB b2a b2b : B.-tuple (chan TBool)) :=
    pars [::
            Outvec b2a (fun j => _ <-- Read (tnth inB j) ;; y <-- Unif TBool ;; Ret y) ;
            Outvec b2b (fun j => a <-- Read (tnth inB j) ;; b <-- Read (tnth b2a j) ;; Ret (a (+) b : TBool)) ].

End Init.

Definition alice_and
           (x y : chan TBool) 
           (leakOTBit : chan TBool)
           (ot_m : chan ((TBool ** TBool) ** (TBool ** TBool)))
           (z : chan TBool) :=
  r <- new TBool ;;
  pars [::
          Out r (Unif TBool) ;
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
                                 r : TBool) ));
          Out z (
                r <-- Read r ;;
                x <-- Read x ;;
                y <-- Read y ;;
                Ret (r (+) ( x && y) : TBool))].

Definition bob_and
           (x y : chan TBool)
           (ot_i : chan (TBool ** TBool))
           (ot_o : chan TBool)
           (z : chan TBool) :=
  pars [::
          Out ot_i (
            x <-- Read x ;;
            y <-- Read y ;;
            Ret {{ x, y }} );
          Out z (
                b <-- Read ot_o ;;
                x <-- Read x ;;
                y <-- Read y ;;
                Ret ((x && y) (+) b : TBool ))].

Definition performOp {A B n} (me : party) (o : Op A B n) (otc : OTChannels)
           (aliceIn : A.-tuple (chan TBool)) (bobIn : B.-tuple (chan TBool))
           (wires : n.-tuple (chan TBool)) (w : chan TBool) :=
  match o with
  | InA a => Out w (copy (tnth aliceIn a))
  | InB a => Out w (copy (tnth bobIn a))
  | Xor x y =>
    Out w (a <-- Read (tnth wires x) ;; b <-- Read (tnth wires y) ;; Ret (a (+) b : TBool)) 
  | Not x =>
    Out w (
          x <-- Read (tnth wires x) ;;
          Ret (if me == alice then ~~ x : TBool else x : TBool))
  | And x y =>
    if me == alice then
      alice_and (tnth wires x) (tnth wires y) (ot_leakBit otc) (ot_m otc) w
    else
      bob_and (tnth wires x) (tnth wires y) (ot_i otc) (ot_o otc) w end.

Definition performComp {A B n} (me : party) (c : Circ A B n) (ots : n.-tuple OTChannels)
           (aliceIn : A.-tuple (chan TBool)) (bobIn : B.-tuple (chan TBool))
           (wires : n.-tuple (chan TBool)) :=
  \||_(j < n) performOp me (c j) (tnth ots j) aliceIn bobIn (tuple_trunc wires j) (tnth wires j).
     
Definition performOuts {n o} (outs : circOuts n o) (wires : n.-tuple (chan TBool))
           (outputs sendOutShares recvOutShares : o.-tuple (chan TBool)) :=
  pars [::
          Outvec sendOutShares (fun j => copy (tnth wires (tnth outs j)));
          Outvec outputs (fun j =>
                            x <-- Read (tnth wires (tnth outs j)) ;;
                            y <-- Read (tnth recvOutShares j) ;;
                            Ret (x (+) y : TBool))].

Definition aliceReal {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (AIn : A.-tuple (chan TBool))
           (AOut : o.-tuple (chan TBool))
           (ots : n.-tuple OTChannels)
           (a2b_init : A.-tuple (chan TBool))
           (b2a_init : B.-tuple (chan TBool))
           (leakAdv_AIn : A.-tuple (chan TBool))
           (leakAdv_a2b : A.-tuple (chan TBool))
           (leakAdv_b2a : B.-tuple (chan TBool))
           (a2b_final : o.-tuple (chan TBool))
           (b2a_final : o.-tuple (chan TBool))
           (leakAdv_b2a_final : o.-tuple (chan TBool))
  :=
  a2a <- newvec A @ TBool ;;
  aliceWires <- newvec n @ TBool ;;
  pars [::
          initAlice _ _ AIn leakAdv_AIn a2b_init leakAdv_a2b a2a b2a_init leakAdv_b2a ;
          performComp alice c ots a2a b2a_init aliceWires ;
          performOuts outs aliceWires AOut a2b_final b2a_final;
          copy_tup b2a_final leakAdv_b2a_final ].
          
Definition bobReal {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (BIn : B.-tuple (chan TBool))
           (BOut : o.-tuple (chan TBool))
           (ots : n.-tuple OTChannels)
           (b2a_init : B.-tuple (chan TBool))
           (a2b_init : A.-tuple (chan TBool))
           (b2a_final : o.-tuple (chan TBool))
           (a2b_final : o.-tuple (chan TBool))
  :=
    b2b <- newvec B @ TBool ;;
    bobWires <- newvec n @ TBool ;;
    pars [::
            initBob _ BIn b2a_init b2b;
            performComp bob c ots a2b_init b2b bobWires;
            performOuts outs bobWires BOut b2a_final a2b_final ].
 
Definition GMWReal {A B n o} (c : Circ A B n) (outs : circOuts n o)
           (AIn : A.-tuple (chan TBool))
           (BIn : B.-tuple (chan TBool))
           (AOut BOut : o.-tuple (chan TBool))
           (leakOTs : n.-tuple (chan TBool)) 
           (leak_AIn : A.-tuple (chan TBool))
           (leakInit_a2b : A.-tuple (chan TBool))
           (leakInit_b2a : B.-tuple (chan TBool))
           (leakFinal_b2a : o.-tuple (chan TBool))
  :=
    withOTs _ leakOTs (fun ots =>
                         a2b_init <- newvec A @ TBool ;;
                         b2a_init <- newvec B @ TBool ;;
                         a2b_final <- newvec o @ TBool ;;
                         b2a_final <- newvec o @ TBool ;;
                         pars [::
                                 aliceReal c outs AIn AOut ots a2b_init b2a_init leak_AIn leakInit_a2b leakInit_b2a a2b_final b2a_final leakFinal_b2a ;
                                 bobReal c outs BIn BOut ots b2a_init a2b_init b2a_final a2b_final ] ).
                         
  
           
           

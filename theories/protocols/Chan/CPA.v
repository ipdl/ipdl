
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Ipdl.Tacs Lib.Dist Ipdl.Big Pars Typing Lib.Set.  

(* ----------- *) 

Definition CPA0 {msg ctxt key : nat} (q : nat) (genK : Dist key) (enc : msg -> key -> Dist ctxt) (i : q.-tuple (chan msg)) (o : q.-tuple (chan ctxt)) :=
  k <- new key ;;
  pars [::
          Out k (Samp genK);
          Outvec o (fun j =>
                      m <-- Read (tnth i j) ;; K <-- Read k ;;
                      c <-- Samp (enc m K) ;;
                      Ret c)].

Definition CPA1 {msg ctxt key : nat} (q : nat) (genK : Dist key) (enc : msg -> key -> Dist ctxt) (i : q.-tuple (chan msg)) (o : q.-tuple (chan ctxt)) :=
  k <- new key ;;
  pars [::
          Out k (Samp genK);
          Outvec o (fun j =>
                      _ <-- Read (tnth i j) ;; K <-- Read k ;;
                      c <-- Samp (enc [tuple of nseq _ false] K) ;;
                      Ret c)].

Definition CPA_Secure {msg ctxt key : nat} (q : nat) (genK : Dist key) (enc : msg -> key -> Dist ctxt) := forall (i : q.-tuple (chan msg)) (o : q.-tuple (chan ctxt)), CPA0 q genK enc i o ~= CPA1 q genK enc i o.

Definition dec_correct {msg ctxt key : nat} (genK : Dist key) (enc : msg -> key -> Dist ctxt) (dec : ctxt -> key -> msg) := forall (k : chan key) (c : chan ctxt) (i : chan msg) (o : chan msg),
    pars [::
            Out k (Samp genK);
            Out c (x <-- Read k ;; m <-- Read i ;; c <-- Samp (enc m x) ;; Ret c);
            Out o (x <-- Read c ;; y <-- Read k ;; Ret (dec x y)) ] ~= 
    pars [::
            Out k (Samp genK);
            Out c (x <-- Read k ;; m <-- Read i ;; c <-- Samp (enc m x) ;; Ret c);
            Out o (copy i) ].

Lemma Multi_dec_correct {msg ctxt key : nat} q (genK : Dist key) (enc : msg -> key -> Dist ctxt) (dec : ctxt -> key -> msg) : dec_correct genK enc dec -> forall (k : chan key) (c : q.-tuple (chan ctxt)) (i : q.-tuple (chan msg)) (o : q.-tuple (chan msg)),
    pars [::
            Out k (Samp genK);
            Outvec c (fun j => x <-- Read k ;; m <-- Read (tnth i j) ;; c <-- Samp (enc m x) ;; Ret c);
            Outvec o (fun j => x <-- Read (tnth c j) ;; y <-- Read k ;; Ret (dec x y)) ] ~= 
    pars [::
            Out k (Samp genK);
            Outvec c (fun j => x <-- Read k ;; m <-- Read (tnth i j) ;; c <-- Samp (enc m x) ;; Ret c);
            Outvec o (fun j => copy (tnth i j)) ].
  intros.
  swap_tac 0 2.
  rewrite -par_in_pars.
  rewrite -bigpar_par.
  symmetry.
  swap_tac 0 2.
  rewrite -par_in_pars.
  rewrite -bigpar_par.
  symmetry.
  apply pars_big_hybrid2; intros.
  rewrite bigpar_par par_in_pars.
  swap_tac 0 2; rewrite par_in_pars.
  symmetry.
  rewrite par_in_pars.
  swap_tac 0 2; rewrite par_in_pars.
  symmetry.
  swap_tac 0 4.
  swap_tac 2 4.
  rewrite (pars_split 3); simpl.
  rewrite H.
  rewrite -pars_cat //=.
  symmetry.
  swap_tac 0 (Out k).
  apply pars_cons_cong; rewrite //=.
  apply pars_cons_cong; rewrite //=.
  swap_tac 0 2.
  apply pars_cons_cong; rewrite //=.
Qed.

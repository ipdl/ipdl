
Require Import List.
From mathcomp Require Import ssreflect ssrbool ssrnat eqtype seq tuple ssrfun.
From mathcomp Require Import choice path bigop fintype ssrnum ssralg.
Require Import Lib.Base Ipdl.Exp Ipdl.Core String Ipdl.Lems Lib.TupleLems Lib.Dist Ipdl.Big Pars Lib.Set Ipdl.Big.  
Require Import FunctionalExtensionality.

Definition is_encodable (T : Type) := exists (ft : finType), ((ft : Type) = T).

Class Encodable (T : Type) := { is_enc : is_encodable T }.
(* every finType is encodable *)
#[global]
Instance Encodable_finType (T : finType) : Encodable T.
    constructor.
    exists T.
    done.
Qed.

Fixpoint rxn_encodable {chan} {t} (r : @rxn chan t) :=
  match r with
    | @Read _ t _ => is_encodable t
    | @Bind _ _ _ c k => rxn_encodable c /\ (forall x, rxn_encodable (k x))
    | _ => True end.                                            
Class EncodableRxn chan {t} (r : @rxn chan t) := { enc_rxn : rxn_encodable r }.
#[global]
Instance EncodableRet chan {t} (x : t) : EncodableRxn chan (Ret x).
   done.
Qed.

#[global]
Instance EncodableSamp chan {t} (x : Dist t) : EncodableRxn chan (Samp x).
   done.
Qed.

#[global]
Instance EncodableRead {chan} {t} `{Encodable t} (c : chan t) : EncodableRxn chan (Read c).
   constructor.
   simpl.
   destruct H; done.
Qed.

#[global]
Instance EncodableBind {chan} {t1 t2} (c : rxn t1) (k : t1 -> rxn t2)
          `{EncodableRxn chan _ c} `{forall x, EncodableRxn _ (k x)} : EncodableRxn _ (Bind c k).
  constructor.
  simpl; split.
  destruct H; done.
  intro; destruct (H0 x); done.
Qed.

#[global]
Instance EncodableRxnIf chan {t} b (r1 r2 : rxn t) `{EncodableRxn chan _ r1} `{EncodableRxn _ _ r2} : EncodableRxn _ (if b then r1 else r2).
destruct b; done.
Qed.


Fixpoint ipdl_encodable {chan} (i : @ipdl chan) :=
  match i with
    | Zero => True
    | @Out _ t _ r => is_encodable t /\ rxn_encodable r
    | Par p1 p2 => ipdl_encodable p1 /\ ipdl_encodable p2
    | New t k => forall c, ipdl_encodable (k c) end.

Class EncodableIPDL chan (i : @ipdl chan) := { enc_ipdl : ipdl_encodable i }.

#[global]
Instance EncodableZero chan : EncodableIPDL chan Zero.
    constructor; done.
Qed.

#[global]
Instance EncodableOut {chan} t c r `{Encodable t} `{EncodableRxn chan _ r} : EncodableIPDL _ (@Out chan t c r).
constructor.
destruct H.
split.
done.
destruct H0; done.
Qed.

#[global]
Instance EncodablePar chan p1 p2 `{EncodableIPDL _ p1} `{EncodableIPDL _ p2} : EncodableIPDL chan (Par p1 p2).
 constructor; simpl.
 split; destruct H, H0; done.
Qed.

#[global]
Instance EncodableNew chan t k `{forall c, EncodableIPDL chan (k c)} : EncodableIPDL _ (New t k).
constructor; simpl; intro.
 destruct (H c).
 done.
Qed.

#[global]
Instance EncodableFoldr chan {A} (xs : seq A) (P : A -> ipdl) (p : pred A) `{forall x, EncodableIPDL chan (P x)} :
EncodableIPDL _
    (foldr (fun (x : A) (x0 : ipdl) => if p x then P x ||| x0 else x0) prot0
       (xs)).
induction xs.
simpl.
apply _.
simpl.
destruct (p a).
apply _.
apply IHxs.
Qed.

#[global]
Instance EncodableBigOrd {chan} n p P `{forall i, EncodableIPDL chan (P i)} :
  EncodableIPDL _ (\||_(i < n | p i) P i).
    rewrite BigOp.bigopE.
    apply EncodableFoldr.
    done.
Qed.

#[global]
Instance EncodableNewvec {chan} {n} {t} (k : n.-tuple (chan t) -> ipdl) `{forall v, EncodableIPDL chan (k v)} : EncodableIPDL _ (v <- newvec n @ t ;; k v).
induction n.
simpl.
apply H.
simpl.
apply EncodableNew; intro.
apply IHn.
intros; apply H.
Qed.

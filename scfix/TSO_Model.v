(******************************************************************************)
(** * Definition of the TSO memory model *)
(******************************************************************************)
Require Import Classical List Relations Peano_dec.
Require Import Hahn HahnMinPath.
Require Import Basic TSO_Events.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section TSO_Model.

Record execution := 
  { acts  : list act_id ;
    lab   : act_id -> label ;
    sb    : relation act_id ;
    rf    : relation act_id ;
    mo    : relation act_id ;
  }.

Variable G : execution.

Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'mo'" := G.(mo).
Notation "'[E]'" := ⦗fun a => In a acts⦘.
Notation "'[R]'" := ⦗is_r lab⦘.
Notation "'[W]'" := ⦗is_w lab⦘.
Notation "'[RMW]'" := ⦗fun a => is_rmw lab a /\ is_w lab a⦘.
Notation "'[F]'" := ⦗is_f lab⦘.
Notation "'[RW]'" := ⦗is_rw lab⦘.
Notation "'[WF]'" := ⦗is_wf lab⦘.
Notation "'[RMW_F]'" := ([RMW] ∪ [F]).
Notation "a |loc" := (restr_eq_rel (loc lab) a) (at level 1).

Notation "a ＊" := (clos_refl_trans a) (at level 1, format "a ＊").

Definition rb := rf⁻¹ ⨾ mo|loc ⨾ [W].

Definition hb := (sb ∪ rf)⁺.

Definition rfe := rf \ sb.

Definition WfACTS := 
  << ACTS_INIT: forall a (INIT: is_init lab a), In a acts >>.

Definition WfSB := 
  << SB_ACT: sb ⊆ [E] ⨾ sb ⨾ [E] >> /\
  << SB_INIT: forall a b (INIT: init_pair lab a b) (IN: In b acts), sb a b >> /\
  << SB_DOMb: forall a b (SB: sb a b), ~ is_init lab b >> /\
  << SB_IRR: irreflexive sb >> /\
  << SB_T: transitive sb >> .

Definition WfRF := 
  << RF_ACT: rf ⊆ [E] ⨾ rf ⨾ [E] >> /\
  << RF_DOM: rf ⊆ [W] ⨾ rf ⨾ [R] >> /\
  << RF_LOC: forall a b (RF: rf a b), (loc lab a = loc lab b) >> /\
  << RF_VAL: forall a b (RF: rf a b), (valw lab a = valr lab b) >> /\
  << RF_FUN: rf ⨾ rf⁻¹ ⊆ ⦗fun _ => True⦘ >> /\ 
  << RF_TOT: forall b (IN: In b acts) (READ: is_r lab b), exists a, rf a b >>.

Definition WfMO :=
  << MO_ACT: mo ⊆ [E] ⨾ mo ⨾ [E] >> /\
  << MO_DOM: mo ⊆ [WF] ⨾ mo ⨾ [WF] >> /\
  << MO_IRR: irreflexive mo >> /\
  << MO_T: transitive mo >> /\
  << MO_TOT: is_total (fun a => In a acts /\ (is_wf lab a)) mo >>.

Definition Wf :=
  << WF_ACTS : WfACTS >> /\
  << WF_SB   : WfSB >> /\
  << WF_RF   : WfRF >> /\
  << WF_MO   : WfMO >>.

Definition Consistent :=
  << WF : Wf >> /\
  << hbI: acyclic (sb ∪ rf) >> /\
  << Cww : irreflexive (mo ⨾ hb) >> /\
  << Cwr : irreflexive (rb ⨾ hb) >> /\
  << Cat : irreflexive (rb ⨾ mo) >> /\
  << Crfe: irreflexive (rb ⨾ mo ⨾ rfe ⨾ sb) >> /\
  << Csc: irreflexive (rb ⨾ mo ⨾ [RMW_F] ⨾ sb) >>.

Lemma con_wf  (CON: Consistent) : Wf.
Proof. cdes CON; done. Qed.

End TSO_Model.
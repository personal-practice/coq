(******************************************************************************)
(** * Domains of the Power memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Power_Events Power_Model.

Set Implicit Arguments.

Section Power_Locations.

Variable G : power_execution.

(* Basic *)
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'mo'" := G.(mo).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'ctrl_isync'" := G.(ctrl_isync).
(* Events *)
Notation "'E'" := G.(E).
Notation "'R'" := G.(R).
Notation "'W'" := G.(W).
Notation "'F_sync'" := G.(F_sync).
Notation "'F_lwsync'" := G.(F_lwsync).
Notation "'RW'" := G.(RW).
Notation "'_WF'" := G.(_WF).
Notation "'F'" := G.(F).
(* Relations *)
Notation "'same_loc'" := G.(same_loc).
Notation "'deps'" := G.(deps).
Notation "'rb'" := G.(rb).
Notation "'rdw'" := G.(rdw).
Notation "'detour'" := G.(detour).
Notation "'ii0'" := G.(ii0).
Notation "'ci0'" := G.(ci0).
Notation "'cc0'" := G.(cc0).
Notation "'ii'" := G.(ii).
Notation "'ic'" := G.(ic).
Notation "'ci'" := G.(ci).
Notation "'cc'" := G.(cc).
Notation "'L'" := G.(L).
Notation "'Li'" := G.(Li).
Notation "'ii_alt'" := G.(ii_alt).
Notation "'ic_alt'" := G.(ic_alt).
Notation "'ci_alt'" := G.(ci_alt).
Notation "'cc_alt'" := G.(cc_alt).
Notation "'ppo'" := G.(ppo).
Notation "'sync'" := G.(sync).
Notation "'lwsync'" := G.(lwsync).
Notation "'fence'" := G.(fence).
Notation "'hb'" := G.(hb).
Notation "'prop1'" := G.(prop1).
Notation "'prop2'" := G.(prop2).
Notation "'prop'" := G.(prop).
Notation "'psbloc'" := G.(psbloc).
Notation "'eco'" := G.(eco).
(* Well-formed axioms *)
Notation "'WfDEPS'" := G.(WfDEPS).
Notation "'WfACTS'" := G.(WfACTS).
Notation "'WfSB'" := G.(WfSB).
Notation "'WfRF'" := G.(WfRF).
Notation "'WfMO'" := G.(WfMO).
Notation "'WfRMW'" := G.(WfRMW).
Notation "'Wf'" := G.(Wf).
(* Consistency *)
Notation "'PowerConsistent'" := G.(PowerConsistent).
(* Notation *)
Notation "'restrict_location'" := G.(restrict_location).
Notation "s ⌇ x" := (restrict_location s x) (at level 1).
Notation "rel |loc" := (rel ∩ same_loc) (at level 1).
Notation "a ∙" := (a ∩ same_thread) (at level 1, format "a ∙").
Notation "a ∘" := (a \ same_thread) (at level 1, format "a ∘").

Hypothesis WF: Wf.

Lemma rf_loc a b (RF: rf a b) : loc lab a = loc lab b.
Proof. by cdes WF; cdes WF_RF; apply RF_LOC. Qed.

Lemma mo_loc a b (MO: mo a b) : loc lab a = loc lab b.
Proof. by cdes WF; cdes WF_MO; apply MO_LOC. Qed.

Lemma rmw_loc a b (RMW: rmw a b) : loc lab a = loc lab b.
Proof. by cdes WF; cdes WF_RMW; apply RMW_LOC. Qed.

Lemma rb_loc a b (RB: rb a b) : loc lab a = loc lab b.
Proof.
  unfold Power_Model.rb in RB.
  unfolder in RB. destruct RB as [z [RF MO]].
  apply rf_loc in RF.
  apply mo_loc in MO.
  congruence.
Qed.

Hint Resolve rf_loc mo_loc rmw_loc rb_loc : locations.

Lemma eco_loc a b (ECO: eco a b) : loc lab a = loc lab b.
Proof.
  unfold Power_Model.eco in ECO; unfolder in ECO.
  desf; eauto with locations;
  (apply mo_loc in ECO + apply rb_loc in ECO);
  apply rf_loc in ECO0; congruence.
Qed.

Lemma Wa_implies_some_loc a (WA: W a) : loc lab a <> None.
Proof.
  unfold Power_Model.W, is_w in WA.
  remember (lab a) as l.
  destruct l; try contradiction.
  unfold loc.
  rewrite <- Heql.
  red; ins.
Qed.

Lemma writes_same_loc_implies_mo (CON: PowerConsistent) a b l 
  (WA: (restrict_location W l) a) (WB: (restrict_location W l) b)
  (ACTA: In a acts) (ACTB: In b acts) (NEQ: a <> b) : 
    mo a b \/ mo b a.
Proof.
  cdes WF; cdes WF_MO; clear - WF CON WA WB ACTA ACTB NEQ MO_ACT MO_LOC MO_TOT.
  assert (l <> None).
    by unfold Power_Model.restrict_location in *; desf; apply Wa_implies_some_loc.
  apply not_none_implies_some in H. desc.
  apply MO_TOT with x; splits; unfold Power_Model.restrict_location in *; desf; eauto.
Qed.

Lemma RW_has_loc a : RW a -> loc lab a <> None.
Proof.
  repeat autounfold with type_unfold; unfold set_union, is_r, is_w.
  ins; desf; unfold Power_Events.loc; desf.
Qed.

End Power_Locations.

(* Export Hints *)
Hint Resolve rf_loc mo_loc rmw_loc rb_loc eco_loc : locations.

(******************************************************************************)
(** * Definitions of the RC11 axiomatic memory model *)
(******************************************************************************)
Require Import Classical List Relations Peano_dec.
Require Import Hahn.
Require Import Basic RC11_Events.

Set Implicit Arguments.
Remove Hints plus_n_O.

Record execution := 
  { acts : list event ;
    lab  : event -> label ;
    sb   : relation event ;
    rmw  : relation event ;
    rf   : relation event ;
    mo   : relation event ;
    data : relation event ;
    addr : relation event ;
    ctrl : relation event ;
  }.

Section Consistency.

Variable G : execution.

Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rmw'" := G.(rmw).
Notation "'rf'" := G.(rf).
Notation "'mo'" := G.(mo).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

Notation "'R'" := (R lab).
Notation "'W'" := (W lab).
Notation "'F'" := (F lab).
Notation "'RMW'" := (RMW lab).

Notation "'RW'" := (RW lab).
Notation "'FR'" := (FR lab).
Notation "'FW'" := (FW lab).

Notation "'Na'" := (Only_Na lab).
Notation "'Rlx'" := (Rlx lab).
Notation "'Rel'" := (Rel lab).
Notation "'Acq'" := (Acq lab).
Notation "'Acqrel'" := (Acqrel lab).
Notation "'Sc'" := (Sc lab).

Definition E a := In a acts.
Definition same_loc := (fun x y => loc lab x <> None /\ loc lab x = loc lab y).
Notation "rel |loc" := (rel ∩ same_loc) (at level 1).

(******************************************************************************)
(** ** Derived relations  *)
(******************************************************************************)

Definition useq := (rf ⨾ (rmw ∪ ⦗RMW⦘))⁺.

(* release sequence *)
Definition rs := ⦗E⦘ ⨾ ⦗W⦘ ⨾ (sb|loc)^? ⨾ ⦗W∩₁Rlx⦘ ⨾ useq^?.

Definition release := (⦗W∩₁Rel⦘ ∪ ⦗F∩₁Rel⦘ ⨾ sb) ⨾ rs.

(* synchronizes with *)
Definition sw := release ⨾ rf ⨾ (⦗R∩₁Acq⦘ ∪ ⦗R∩₁Rlx⦘ ⨾ sb ⨾ ⦗F∩₁Acq⦘).

(* happens-before *)
Definition hb := (sb ∪ sw)⁺.

(* reads-before *)
Definition rb := (rf⁻¹ ⨾ mo) \ ⦗E⦘.

(* extended coherence order *)
Definition eco := rf ∪ mo ⨾ rf^? ∪ rb ⨾ rf^?.

Definition sb_neq_loc := sb \ sb|loc.
  
Definition scb := sb ∪ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ∪ hb|loc ∪ mo ∪ rb.

Definition psc_base := (⦗Sc⦘ ∪ ⦗F∩₁Sc⦘ ⨾ hb) ⨾ scb ⨾ (⦗Sc⦘ ∪ hb ⨾ ⦗F∩₁Sc⦘).

Definition psc_f := ⦗F∩₁Sc⦘ ⨾ (hb ∪ hb ⨾ eco ⨾ hb) ⨾ ⦗F∩₁Sc⦘.

Definition psc := psc_base ∪ psc_f.

Definition deps := data ∪ addr ∪ ctrl.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma sb_in_hb : sb ⊆ hb.
Proof. vauto. Qed.

Lemma sw_in_hb : sw ⊆ hb.
Proof. vauto. Qed.

Lemma hb_trans : transitive hb.
Proof. vauto. Qed.

Lemma hb_hb : hb ⨾ hb ⊆ hb.
Proof. unfold seq, inclusion; ins; desf; vauto. Qed.

Lemma cr_hb_hb : hb^? ⨾ hb ⊆ hb.
Proof. unfold hb; rels. Qed.

Lemma sb_neq_loc_in_sb : sb_neq_loc ⊆ sb.
Proof. by unfold sb_neq_loc; basic_solver. Qed.

Lemma sb_neq_loc_in_hb : sb_neq_loc ⊆ hb.
Proof. by rewrite sb_neq_loc_in_sb, sb_in_hb. Qed.

Lemma hb_loc_in_hb : hb|loc ⊆ hb.
Proof. basic_solver. Qed.

(******************************************************************************)
(** ** Well-formed relations *)
(******************************************************************************)
Definition WfACTS := 
  ⟪ ACTS_INIT : forall l, In (Init l) acts ⟫ /\
  ⟪ LAB_INIT  : forall l, lab (Init l) = init_label l⟫.

Definition WfSB := 
  ⟪ SB_ACT  : sb ⊆ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘ ⟫ /\
  ⟪ SB_INIT : init_pair ⨾ ⦗E⦘ ⊆ sb ⟫ /\
  ⟪ SB_IRR  : irreflexive sb ⟫ /\
  ⟪ SB_T    : transitive sb ⟫ /\
  ⟪ SB_TID  : sb ⊆ sb∙ ∪ init_pair ⟫ /\
  ⟪ SB_TOT  : forall i, is_total (E ∩₁ (fun a => tid a = Some i)) sb ⟫.

Definition WfRF := 
  ⟪ RF_ACT: rf ⊆ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘ ⟫ /\
  ⟪ RF_IRR  : irreflexive rf ⟫ /\
  ⟪ RF_DOM: rf ⊆ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘ ⟫ /\
  ⟪ RF_LOC: funeq (loc lab) rf ⟫ /\
  ⟪ RF_VAL: forall a b, rf a b -> (valw lab) a = (valr lab) b ⟫ /\
  ⟪ RF_FUN: functional rf⁻¹ ⟫ /\ 
  ⟪ RF_TOT: forall b (IN: E b) (READ: R b), exists a, rf a b ⟫.

Definition WfMO :=
  ⟪ MO_ACT: mo ⊆ ⦗E⦘ ⨾ mo ⨾ ⦗E⦘ ⟫ /\
  ⟪ MO_DOM: mo ⊆ ⦗W⦘ ⨾ mo ⨾ ⦗W⦘ ⟫ /\
  ⟪ MO_LOC: funeq (loc lab) mo ⟫ /\
  ⟪ MO_IRR: irreflexive mo ⟫ /\
  ⟪ MO_T  :   transitive mo ⟫ /\
  ⟪ MO_TOT: forall l, is_total (E ∩₁ W ∩₁ (fun a => loc lab a = Some l)) mo ⟫.

Definition WfRMW := 
  ⟪ RMW_DOM: rmw ⊆ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘ ⟫ /\
  ⟪ RMW_LOC: funeq (loc lab) rmw ⟫ /\
  ⟪ RMW_MOD: forall a b (RMW_AB: rmw a b), 
      (Rlx a /\ Rlx b) \/ (Acq a /\ Rlx b) \/ (Rlx a /\ Rel b) \/ (Acq a /\ Rel b) \/ (Sc a /\ Sc b) ⟫ /\
  ⟪ RMW_IMM: rmw ⊆ sb|imm ⟫.

Definition WfDEPS :=
  ⟪ DATA        : data ⊆ ⦗R⦘ ⨾ data ⨾ ⦗W⦘⟫ /\
  ⟪ ADDR        : addr ⊆ ⦗R⦘ ⨾ addr ⨾ ⦗RW⦘⟫ /\
  ⟪ CTRL_RE     : ctrl ⊆ ⦗R⦘ ⨾ ctrl ⟫ /\
  ⟪ DATA_IN_SB  : data ⊆ sb ⟫ /\
  ⟪ ADDR_IN_SB  : addr ⊆ sb ⟫ /\
  ⟪ CTRL_SB     : ctrl ⨾ sb ⊆ ctrl ⟫ /\
  ⟪ CTRL_IN_SB  : ctrl ⊆ sb ⟫ /\
  ⟪ RMW_DEPS    : rmw ⊆ deps ⟫.

Definition Wf :=
  ⟪ WF_ACTS   : WfACTS ⟫ /\
  ⟪ WF_SB     : WfSB ⟫ /\
  ⟪ WF_RMW    : WfRMW ⟫ /\
  ⟪ WF_RF     : WfRF ⟫ /\
  ⟪ WF_MO     : WfMO ⟫ /\
  ⟪ WF_DEPS   : WfDEPS ⟫.

Implicit Type WF : Wf.

Lemma wf_sb WF : WfSB.
Proof. cdes WF; done. Qed.
Lemma wf_rmw WF : WfRMW.
Proof. cdes WF; done. Qed.
Lemma wf_rf WF : WfRF.
Proof. cdes WF; done. Qed.
Lemma wf_mo WF : WfMO.
Proof. cdes WF; done. Qed.
Lemma wf_deps WF : WfDEPS.
Proof. cdes WF; done. Qed.

Hint Resolve wf_sb wf_rmw wf_rf wf_mo.

(******************************************************************************)
(** ** Coherence *)
(******************************************************************************)

Definition Coherent := irreflexive (hb ⨾ eco^?).
Definition Atomic := irreflexive (rb ⨾ mo ⨾ rmw⁻¹).
Definition Atomic2 := irreflexive (mo ⨾ mo ⨾ rf⁻¹).
Definition PSC := acyclic psc.
Definition NoThinAir := acyclic (sb ∪ rf).

Definition consistent :=
  ⟪ WF  : Wf ⟫ /\
  ⟪ COH : Coherent ⟫ /\
  ⟪ AT  : Atomic ⟫ /\
  ⟪ AT2 : Atomic2 ⟫ /\
  ⟪ SC  : PSC ⟫ /\
  ⟪ NTA : NoThinAir ⟫.

Definition wconsistent :=
  ⟪ WF   : Wf ⟫ /\
  ⟪ COH  : Coherent ⟫ /\
  ⟪ AT   : Atomic ⟫ /\
  ⟪ AT2  : Atomic2 ⟫ /\
  ⟪ SC   : PSC ⟫.

Lemma con_wf  (CON: consistent) : Wf.
Proof. cdes CON; done. Qed.

Lemma wcon_wf  (CON: wconsistent) : Wf.
Proof. cdes CON; done. Qed.

Hint Resolve con_wf.

Lemma atomicity_equiv : rmw ∩ (rb ⨾ mo) ⊆ ∅₂ <-> irreflexive (rb ⨾ mo ⨾ rmw⁻¹).
Proof.  split; basic_solver 8. Qed.

Lemma atomicity_equiv2 : rf ∩ (mo ⨾ mo) ⊆ ∅₂ <-> irreflexive (mo ⨾ mo ⨾ rf⁻¹).
Proof.  split; basic_solver 8. Qed.

Implicit Type CON : consistent.
Implicit Type WCON : wconsistent.
Implicit Type COH: irreflexive (hb ⨾ eco^?).

(******************************************************************************)
(** ** Outcomes  *)
(******************************************************************************)
Definition conflicting :=
  (⦗E⦘ ⨾ ⦗W⦘ ⨾ same_loc ⨾ ⦗E⦘ ∪ ⦗E⦘ ⨾ same_loc ⨾ ⦗W⦘ ⨾ ⦗E⦘) \ ⦗fun x => True⦘.

Definition race := conflicting \ (hb ∪ hb⁻¹).

Definition racy := ⦗Na⦘ ⨾ race ∪ race ⨾ ⦗Na⦘.

Definition outcome (O: location -> value) :=
  forall l, exists w,
    W w /\
    loc lab w = Some l /\
    val lab w = Some (O l) /\
    max_elt mo w.

(******************************************************************************)
(** ** Same Location relations  *)
(******************************************************************************)

Lemma restr_eq_rel_same_loc r : ⦗RW⦘ ⨾ restr_eq_rel (loc lab) r ⨾ ⦗RW⦘ ≡ r ∩ same_loc.
Proof.
unfold same_loc; unfolder.
unfold RC11_Events.loc.
solve_type_mismatch 42.
Qed.

Lemma loceq_useq WF : funeq (loc lab) useq.
Proof.
cdes WF; cdes WF_RMW; cdes WF_RF.
unfold useq; eauto 10 with rel.
Qed.

Lemma loceq_rs WF : funeq (loc lab) rs.
Proof.
unfold rs; eauto 10 using loceq_useq with rel.
Qed.

Lemma loceq_hb_loc WF : funeq (loc lab) hb|loc.
Proof.
  unfold funeq, same_loc; basic_solver.
Qed.

(******************************************************************************)
(** ** Actions in graph *)
(******************************************************************************)

Local Notation "'acta' r" := (doma r (fun x => In x acts)) (at level 2).
Local Notation "'actb' r" := (domb r (fun x => In x acts)) (at level 2).

Lemma act_helper r :
    r ⊆ ⦗fun a => In a acts⦘ ⨾ r ⨾ ⦗fun a => In a acts⦘ <->
    acta r /\ actb r.
Proof. apply domab_helper. Qed.

Lemma sb_acta (WF: WfSB) : acta sb.
Proof. apply act_helper, WF. Qed.
Lemma sb_actb (WF: WfSB) : actb sb.
Proof. apply act_helper, WF. Qed.
Hint Resolve sb_acta sb_actb : rel.
Lemma sbloc_acta (WF: WfSB) : acta sb|loc.
Proof. arewrite (sb|loc ⊆ sb). eauto with rel. Qed.
Lemma sbloc_actb (WF: WfSB) : actb sb|loc.
Proof. arewrite (sb|loc ⊆ sb). eauto with rel. Qed.
Lemma rmw_acta (WF_SB: WfSB) (WF_RMW: WfRMW) : acta rmw.
Proof.
  by cdes WF_RMW; rewrite RMW_IMM; arewrite (sb|imm ⊆ sb); apply sb_acta.
Qed.
Lemma rmw_actb (WF_SB: WfSB) (WF_RMW: WfRMW) : actb rmw.
Proof.
  by cdes WF_RMW; rewrite RMW_IMM; arewrite (sb|imm ⊆ sb); apply sb_actb.
Qed.
Lemma rf_acta (WF: WfRF) : acta rf.
Proof. apply act_helper, WF. Qed.
Lemma rf_actb (WF: WfRF) : actb rf.
Proof. apply act_helper, WF. Qed.
Lemma mo_acta (WF: WfMO) : acta mo.
Proof. apply act_helper, WF. Qed.
Lemma mo_actb (WF: WfMO) : actb mo.
Proof. apply act_helper, WF. Qed.
Lemma rb_acta (WF: WfRF) : acta rb.
Proof.
  unfold rb; arewrite (rf⁻¹ ⨾ mo \ ⦗E⦘ ⊆ rf⁻¹ ⨾ mo).
  eauto using rf_actb with rel.
Qed.
Lemma rb_actb (WF: WfMO) : actb rb.
Proof.
  unfold rb; arewrite (rf⁻¹ ⨾ mo \ ⦗E⦘ ⊆ rf⁻¹ ⨾ mo).
  eauto using mo_actb with rel.
Qed.
Lemma rb_act WF : rb ⊆ ⦗fun a => In a acts⦘ ⨾ rb ⨾ ⦗fun a => In a acts⦘.
Proof. eapply domab_helper; splits; [apply rb_acta|apply rb_actb]; auto. Qed.

Hint Resolve 
  sbloc_acta rmw_acta rf_acta mo_acta rb_acta
  sbloc_actb rmw_actb rf_actb mo_actb rb_actb
: rel.

Lemma eco_act WF :
  eco ⊆ ⦗fun a => In a acts⦘ ⨾ eco ⨾ ⦗fun a => In a acts⦘.
Proof.
unfold eco; cdes WF; cdes WF_RF; cdes WF_MO.
rewrite RF_ACT at 1 2 3; rewrite MO_ACT at 1; rewrite rb_act at 1; try done.
apply inclusion_union_l; solve_type_mismatch 15.
Qed.
Lemma eco_acta WF : acta eco.
Proof. by apply act_helper, eco_act. Qed.
Lemma eco_actb WF : actb eco.
Proof. by apply act_helper, eco_act. Qed.
Lemma useq_acta WF : acta useq. Proof. eauto with rel. Qed.
Lemma useq_actb WF : actb useq.
Proof. unfold useq; rewrite seq_union_r; eauto 10 with rel. Qed.
Hint Resolve useq_acta useq_actb : rel.
Lemma rs_acta WF : acta rs. Proof. eauto with rel. Qed.
Lemma rs_actb WF : actb rs.
Proof. unfold rs; rewrite <- !seqA; eauto 10 with rel. Qed.
Hint Resolve rs_acta rs_actb : rel.
Lemma rel_acta WF : acta release.
Proof. unfold release; relsf; eauto 10 with rel. Qed.
Lemma rel_actb WF : actb release. Proof. eauto with rel. Qed.
Hint Resolve rel_acta rel_actb : rel. 
Lemma sw_acta WF : acta sw. Proof. eauto with rel. Qed.
Lemma sw_actb WF : actb sw.
Proof. unfold sw; relsf; rewrite inclusion_seq_eqv_r; auto 12 with rel. Qed.
Hint Resolve sw_acta sw_actb : rel.
Lemma hb_acta WF : acta hb. Proof. eauto 10 with rel. Qed.
Lemma hb_actb WF : actb hb. Proof. eauto 10 with rel. Qed.
Hint Resolve hb_acta hb_actb : rel.

(******************************************************************************)
(** ** Domains and Codomains of relations  *)
(******************************************************************************)
Lemma sb_domb (WF: WfSB) : domb sb (fun x => ~ is_init x).
Proof.
  cdes WF.
  rewrite SB_TID.
  apply domb_helper.
  unionL.
  - rewrite seq_union_l; unionR left.
    unfolder; ins; desf; splits; auto.
    unfold same_thread, tid, is_init in *; desf.
  - rewrite seq_union_l; unionR right.
    unfolder; ins; desf; splits; auto.
    red in H; desf.
Qed.
Lemma rmw_doma (WF: WfRMW) : doma rmw R.
Proof.
eapply doma_helper; cdes WF; rewrite RMW_DOM at 1.
solve_type_mismatch.
Qed.
Lemma rmw_domb (WF: WfRMW) : domb rmw W.
Proof. 
eapply domb_helper; cdes WF; rewrite RMW_DOM at 1.
solve_type_mismatch.
Qed.
Lemma rf_doma (WF: WfRF) : doma rf W.
Proof. 
eapply doma_helper; cdes WF; rewrite RF_DOM at 1.
solve_type_mismatch.
Qed.
Lemma rf_domb (WF: WfRF) : domb rf R.
Proof. 
eapply domb_helper; cdes WF; rewrite RF_DOM at 1.
solve_type_mismatch.
Qed.
Lemma mo_doma (WF: WfMO) : doma mo W.
Proof. 
eapply doma_helper; cdes WF; rewrite MO_DOM at 1.
solve_type_mismatch.
Qed.
Lemma mo_domb (WF: WfMO) : domb mo W.
Proof. 
eapply domb_helper; cdes WF; rewrite MO_DOM at 1.
solve_type_mismatch.
Qed.
Lemma rb_doma WF : doma rb R.
Proof.
  unfold rb; arewrite (rf⁻¹ ⨾ mo \ ⦗E⦘ ⊆ rf⁻¹ ⨾ mo).
  eauto using rf_domb with rel.
Qed.
Lemma rb_domb WF : domb rb W.
Proof.
  unfold rb; arewrite (rf⁻¹ ⨾ mo \ ⦗E⦘ ⊆ rf⁻¹ ⨾ mo).
  eauto using mo_domb with rel.
Qed.

Lemma sb_dom (WF: WfSB) : sb ⊆ ⦗fun _ => True⦘ ⨾ sb ⨾ ⦗fun x => ~ is_init x⦘.
Proof. rewrite domb_fold; [rels | eapply sb_domb; eauto | ins; eauto]. Qed.
Lemma rmw_dom (WF: WfRMW) : rmw ⊆ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘.
Proof. apply WF. Qed.
Lemma rf_dom (WF: WfRF) : rf ⊆ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘.
Proof. apply WF. Qed.
Lemma mo_dom (WF: WfMO) : mo ⊆ ⦗W⦘ ⨾ mo ⨾ ⦗W⦘.
Proof. apply WF. Qed.
Lemma rb_dom WF : rb ⊆ ⦗R⦘ ⨾ rb ⨾ ⦗W⦘.
Proof. apply domab_helper; split; [apply rb_doma | apply rb_domb]; done. Qed.

Lemma eco_doma WF : doma eco RW.
Proof.
unfold eco; rewrite rf_dom, mo_dom, rb_dom; auto.
unfold doma; solve_type_mismatch.
Qed.

Lemma eco_domb WF : domb eco RW.
Proof.
unfold eco; rewrite rf_dom, mo_dom, rb_dom; auto.
unfold domb; solve_type_mismatch.
Qed.

Lemma eco_dom WF : eco ⊆ ⦗RW⦘ ⨾ eco ⨾ ⦗RW⦘.
Proof. apply domab_helper; split; [apply eco_doma | apply eco_domb]; done. Qed.

Lemma useq_doma WF : doma useq W.
Proof. unfold useq; eauto using rf_doma with rel. Qed.

Lemma RMW_in_W : RMW ⊆₁ W.
Proof. solve_type_mismatch. Qed.

Lemma useq_domb WF : domb useq W.
Proof.
  unfold useq; rewrite seq_union_r, RMW_in_W; eauto 12 using rmw_domb with rel.
Qed.
Lemma useq_dom WF : useq ⊆ ⦗W⦘ ⨾ useq ⨾ ⦗W⦘.
Proof. apply domab_helper; split; [apply useq_doma | apply useq_domb]; try done. Qed.
Lemma rs_doma WF : doma rs W.
Proof. unfold rs; eauto with rel. Qed.
Lemma rs_domb WF : domb rs W.
Proof. unfold rs; rewrite useq_dom; [solve_type_mismatch|done]. Qed.
Lemma rel_doma WF : doma release (FW∩₁Rel).
Proof. unfold release; solve_type_mismatch. Qed.
Lemma rel_domb WF : domb release W.
Proof. unfold release; eauto using rs_domb with rel. Qed.
Lemma sw_doma WF : doma sw (FW∩₁Rel).
Proof. unfold sw; eauto using rel_doma with rel. Qed.
Lemma sw_domb WF : domb sw (FR∩₁Acq).
Proof. unfold sw; rewrite rf_dom; auto; solve_type_mismatch. Qed.
Lemma rs_dom WF : rs ⊆ ⦗W⦘ ⨾ rs ⨾ ⦗W⦘.
Proof. apply domab_helper; split; [apply rs_doma | apply rs_domb]; try done. Qed.
Lemma rel_dom WF : release ⊆ ⦗FW∩₁Rel⦘⨾ release ⨾ ⦗W⦘.
Proof. apply domab_helper; split; [apply rel_doma | apply rel_domb]; try done. Qed.
Lemma sw_dom WF : sw ⊆ ⦗FW∩₁Rel⦘ ⨾ sw ⨾ ⦗FR∩₁Acq⦘.
Proof. apply domab_helper; split; [apply sw_doma | apply sw_domb]; try done. Qed.

(******************************************************************************)
(** ** Execution Types  *)
(******************************************************************************)
Definition NO_RMW_EVENTS := RMW ≡₁ ∅₁.
Implicit Type NRMW : NO_RMW_EVENTS.

Lemma NRMW_implies_type_mismatch NRMW : R ∩₁ W ⊆₁ ∅₁.
Proof.
  red in NRMW; type_unfolder; unfolder in *.
  ins; specialize (NRMW x); desf.
Qed.

Lemma NRMW_implies_original_rb WF NRMW : rb ≡ rf⁻¹ ⨾ mo.
Proof.
  unfold rb; split; [basic_solver|].
  unfolder; ins; desf.
  eexists; splits; eauto; red; ins; desf.
  apply rf_domb in H; auto; apply mo_domb in H0; auto.
  apply NRMW_implies_type_mismatch with y; auto.
  unfolder; auto.
Qed.

Lemma NRMW_implies_original_useq WF NRMW : useq ≡ (rf ⨾ rmw)⁺.
Proof.
  unfold useq; red in NRMW; rewrite NRMW, eqv_empty_is_empty; relsf.
Qed.

Lemma NRMW_implies_rf_irr NRMW (RF_DOM: rf ⊆ ⦗W⦘ ⨾ rf⨾ ⦗R⦘) : irreflexive rf.
Proof.
  rewrite RF_DOM; rotate; unfolder; ins; desf.
  by apply (NRMW_implies_type_mismatch NRMW) with z.
Qed.

Lemma NRMW_implies_atomic2 WF NRMW : Atomic2.
Proof.
  red; cdes WF; rewrite rf_dom, mo_dom; auto.
  unfolder; ins; desf.
  by apply (NRMW_implies_type_mismatch NRMW) with z3.
Qed.

(******************************************************************************)
(** ** §3.4 Comparison with C11 *)
(******************************************************************************)

Definition coherent_expanded :=
  ⟪ Chb   : irreflexive hb ⟫ /\
  ⟪ Crf   : irreflexive (rf ⨾ hb) ⟫ /\
  ⟪ Crw   : irreflexive (mo ⨾ rf ⨾ hb) ⟫ /\
  ⟪ Cww   : irreflexive (mo ⨾ hb) ⟫ /\
  ⟪ Cwr   : irreflexive (mo ⨾ hb ⨾ rf⁻¹) ⟫ /\
  ⟪ Crr   : irreflexive (mo ⨾ rf ⨾ hb ⨾ rf⁻¹) ⟫.

(* Proposition 1 *)
Lemma hb_eco_r_alt : 
  hb ⨾ eco^? ≡ 
    hb ∪ hb ⨾ rf ∪ hb ⨾ mo ∪ hb ⨾ mo ⨾ rf ∪ hb ⨾ rb ∪ hb ⨾ rb ⨾ rf.
Proof. unfold eco, rb; basic_solver 42. Qed.

Proposition coherence_expanded_eq :
  irreflexive (hb ⨾ eco^?) <-> coherent_expanded.
Proof.
  rewrite hb_eco_r_alt; unfold coherent_expanded, rb.
  intuition; unnw; repeat (apply irreflexive_union in H; desf); try by rotate.
  - rotate 2.
    red; unfolder; ins; desf.
    apply H1 with x.
    unfolder; ins; desf.
    exists z; splits; auto.
    exists z0; splits; auto.
    red; ins; desf.
    basic_solver.
  - rotate 2.
    red; unfolder; ins; desf.
    apply H0 with x.
    unfolder; ins; desf.
    exists z; splits; auto.
    exists z1; splits; auto.
    exists z0; splits; auto.
    red; ins; desf.
    apply H4 with x.
    basic_solver.
  - unionL; try by (idtac + rotate + rotate 2).
    + apply irreflexive_inclusion with (r' := hb ⨾ rf⁻¹ ⨾ mo).
        basic_solver 42.
      by rotate.
    + apply irreflexive_inclusion with (r' := hb ⨾ rf⁻¹ ⨾ mo ⨾ rf).
        basic_solver 42.
      by rotate 2.
Qed.

(* Proposition 2 *)
Proposition sc_eq :
  acyclic psc <-> 
  exists S, strict_total_order Sc S /\ irreflexive (S ⨾ psc).
Admitted.

(* Proposition 3 *)
Definition sc_distinct_loc :=
  forall a b, 
  ~ is_init a -> 
  ~ is_init b ->
  Sc a ->
  loc lab a = loc lab b ->
  Sc b.

Proposition non_sc_loc :
  sc_distinct_loc -> ⦗Sc⦘ ⨾ hb ⨾ ⦗Sc⦘ ⊆ psc⁺.
Admitted.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma rmw_in_sb_loc WF: rmw ⊆ sb |loc.
Proof.
  cdes WF; cdes WF_RMW.
  red in RMW_LOC.
  arewrite (rmw ⊆ rmw|loc).
  { unfolder; ins; splits; auto.
    red; splits; auto.
    assert (R x) by (apply RMW_DOM in H; unfolder in H; desf).
    unfold loc; red in H0.
    unfold loc; desf.
  }
  arewrite (rmw ⊆ sb).
    by rewrite RMW_IMM; unfold immediate; basic_solver.
  done.
Qed.

Lemma sb_neq_loc_in_sb_minus_rmw WF:  sb_neq_loc ⊆ sb \ rmw.
Proof.
  unfold sb_neq_loc.
  arewrite (rmw ⊆ sb|loc); try done.
  by apply rmw_in_sb_loc.
Qed.

Lemma rf_seq_mo WF NRMW: rf ⨾ mo ⊆ ∅₂.
Proof.
  rewrite rf_dom, mo_dom; auto.
  assert (T := (NRMW_implies_type_mismatch NRMW)).
  unfolder in *; ins; desf.
  specialize (T z1).
  solve_type_mismatch.
Qed.

Lemma rel_seq_rf WF: release ⨾ rf ⨾ ⦗R∩₁Acq⦘⊆ sw.
Proof. unfold sw; relsf. Qed.

Lemma rf_seq_rf WF NRMW : rf ⨾ rf ⊆ ∅₂.
Proof.
  rewrite rf_dom, rf_dom; auto.
  assert (T := (NRMW_implies_type_mismatch NRMW)).
  unfolder in *; ins; desf.
  specialize (T z4).
  solve_type_mismatch.
Qed.

Lemma irr_rf WF: irreflexive rf.
Proof. by cdes WF; cdes WF_RF. Qed.

Lemma rmw_in_sb WF: rmw ⊆ sb.
Proof.
  by cdes WF; cdes WF_RMW; rewrite RMW_IMM; unfold immediate; basic_solver.
Qed.

Lemma useq_in_sb_rf WF: useq ⊆ (sb ∪ rf)⁺.
Proof.
  unfold useq; rewrite rmw_in_sb; try done.
  clear_equivs ⦗RMW⦘; relsf.
  eauto using inclusion_t_t2, inclusion_step2_ct with rel.
Qed.

Lemma rs_in_sb_rf WF: rs ⊆ (sb ∪ rf)＊.
Proof.
  unfold rs.
  rewrite useq_in_sb_rf; try done; relsf; auto 8 with rel rel_full.
Qed.

Lemma rel_in_sb_rf WF: release ⊆ (sb ∪ rf)＊.
Proof.
  unfold release; rewrite rs_in_sb_rf; try done; relsf; auto 8 with rel rel_full.
Qed.

Lemma sw_in_sb_rf WF: sw ⊆ (sb ∪ rf)⁺.
Proof.
  unfold sw; rewrite rel_in_sb_rf; try done; relsf; auto 8 with rel rel_full.
Qed.

Lemma hb_in_sb_rf WF: hb ⊆ (sb ∪ rf)⁺.
Proof.
  unfold hb; rewrite sw_in_sb_rf; try done; relsf; auto 8 with rel rel_full.
Qed.

Lemma rf_seq_transp_rf (WF: WfRF): rf ⨾ rf⁻¹ ⊆ ⦗fun _ => True⦘.
Proof. by apply functional_alt, WF.  Qed.

Lemma rf_seq_rb WF: rf ⨾ rb ⊆ mo.
Proof.
  unfold rb; arewrite (rf⁻¹ ⨾ mo \ ⦗E⦘ ⊆ rf⁻¹ ⨾ mo).
  sin_rewrite rf_seq_transp_rf. relsf. eapply WF.
Qed.

Lemma mo_seq_mo WF: mo ⨾ mo ⊆ mo.
Proof. apply rewrite_trans, WF. Qed.

Lemma rb_seq_mo WF NRMW : rb ⨾ mo ⊆ rb.
Proof.
  unfold rb.
  rewrite NRMW_implies_original_rb; auto.
  by rewrite seqA, mo_seq_mo.
Qed.

Lemma mo_seq_rb WF NRMW : mo ⨾ rb ⊆ ∅₂.
Proof.
  unfolder; ins; desf.
  apply mo_domb in H; auto.
  eapply rb_doma in H0; auto.
  apply NRMW_implies_type_mismatch with z; solve_type_mismatch.
Qed.

Lemma rb_seq_rb WF NRMW: rb ⨾ rb ⊆ ∅₂.
Proof.
  unfold seq; red; ins; desf.
  apply rb_domb in H; eapply rb_doma in H0; auto.
  apply NRMW_implies_type_mismatch with z; solve_type_mismatch.
Qed.

Lemma eco_alt WF: eco ≡ (mo ∪ rb) ∪ (mo ∪ rb)^? ⨾ rf.
Proof. unfold eco; rewrite !crE; relsf; split; unionL; auto with rel. Qed.

Lemma eco_alt2 WF NRMW: eco ≡ rf ∪ (rf⁻¹)^? ⨾ mo ⨾ rf^?.
Proof.
  unfold eco; rewrite NRMW_implies_original_rb; auto.
  rewrite !crE; relsf; rewrite !seqA; split; unionL; auto with rel.
Qed.

Lemma eco_trans WF NRMW: transitive eco.
Proof.
  apply transitiveI.
  rewrite (eco_alt WF) at 1. unfold eco.
  rewrite !seq_union_l, !seq_union_r, !seqA, rf_seq_rf; try done.
  sin_rewrite !(rf_seq_mo WF NRMW); sin_rewrite !(rf_seq_rb WF).
  relsf.
  rewrite (crE (mo ∪ rb)); relsf.
  sin_rewrite !(rb_seq_mo WF NRMW); sin_rewrite !(mo_seq_mo WF).
  sin_rewrite (rb_seq_rb WF NRMW); sin_rewrite (mo_seq_rb WF NRMW).
  relsf; unionL; eauto with rel.
Qed.

Lemma irr_eco WF NRMW: irreflexive eco.
Proof.
  unfold eco; rewrite crE; relsf.
  do 3 (try apply irreflexive_union; splits).
  by red; ins; eapply rf_seq_rf; unfold seq; eauto.
  eby eapply WF.
  by eapply irreflexive_seqC; red; ins; eapply rf_seq_mo; unfold seq; eauto.
  by red; ins; eapply rb_seq_rb; unfold seq; eauto.
  eby eapply irreflexive_seqC; rewrite rf_seq_rb; eapply WF.
Qed.

Lemma mo_in_eco WF: mo ⊆ eco.
Proof. unfold eco; basic_solver 6. Qed.
Lemma rf_in_eco WF: rf ⊆ eco.
Proof. unfold eco; basic_solver 6. Qed.
Lemma rb_in_eco WF: rb ⊆ eco.
Proof. unfold eco; basic_solver 6. Qed.

Lemma eco_alt3 WF NRMW: eco ≡ (rf ∪ mo ∪ rb)⁺.
Proof.
  split; eauto 8 using rf_in_eco, mo_in_eco, rb_in_eco, eco_trans with rel.
  unfold eco; rewrite !crE; relsf. 
  repeat apply inclusion_union_l; eauto 6 using inclusion_step2_ct with rel.
Qed.

Lemma useq_in_eco WF NRMW (RMW_IN_RB: rmw ⊆ rb) : useq ⊆ eco.
Proof.
  rewrite eco_alt3; try done. unfold useq; rewrite RMW_IN_RB.
  clear_equivs ⦗RMW⦘; relsf.
  eauto 10 using inclusion_step2_ct with rel.
Qed.

Lemma eco_seq_f WF : eco ⨾ ⦗F⦘ ≡ ∅₂.
Proof.
split; try done.
rewrite eco_dom; try done.
solve_type_mismatch.
Qed.

Lemma rs_in_eco WF NRMW
  (SBLOC: ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo)
  (RMW_IN_RB: rmw ⊆ rb) : rs ⊆ eco^?.
Proof.
  unfold rs; rewrite useq_in_eco; try done.
  arewrite (⦗W∩₁Rlx⦘ ⊆ ⦗W⦘ ⨾ ⦗W∩₁Rlx⦘) by solve_type_mismatch.
  rewrite crE. relsf. sin_rewrite SBLOC.
  rewrite !inclusion_seq_eqv_l, mo_in_eco, crE; relsf.
  rewrite (rewrite_trans (eco_trans WF NRMW)); relsf.
Qed.

Lemma sw_in_eco WF NRMW
  (SBLOC: ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo)
  (RMW_IN_SB: rmw ⊆ rb) : ⦗W⦘ ⨾ sw ⨾ ⦗R⦘ ⊆ eco.
Proof.
  unfold sw, release; rewrite rs_in_eco, rf_in_eco; try edone.
  unfold seq, union, clos_refl, eqv_rel; red; ins; desf.
  all: try by solve_type_mismatch.
  eby eapply eco_trans; eauto.
Qed.

Lemma sw_in_eco_sb WF NRMW
  (SBLOC: ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo)
  (RMW_IN_RB: rmw ⊆ rb) : ⦗W⦘ ⨾ sw ⨾ ⦗F⦘ ⊆ eco ⨾ sb.
Proof.
unfold sw, release; rewrite rs_in_eco, rf_in_eco; try edone.
relsf; unionL; try by solve_type_mismatch 2.
rewrite !seqA; arewrite(eco ^? ⨾ eco ⊆ eco).
  rewrite crE; relsf; apply inclusion_union_l, rewrite_trans; try done.
  by apply eco_trans.
repeat apply inclusion_union_l; rewrite ?seqA; try done.
solve_type_mismatch 3.
Qed.

Lemma sw_in_sb_eco_sb WF NRMW
  (SBLOC: ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo)
  (RMW_IN_RB: rmw ⊆ rb) :
    sw ⊆ (⦗F⦘ ⨾ sb)^? ⨾ eco ⨾ (sb ⨾ ⦗F⦘)^?.
Proof.
unfold sw, release; rewrite rs_in_eco, rf_in_eco; try edone.
relsf; rewrite !seqA.
assert (ECO: eco ^? ⨾ eco ⊆ eco).
  rewrite crE; relsf; apply inclusion_union_l, rewrite_trans; try done.
  by apply eco_trans.
sin_rewrite !ECO.
arewrite (⦗F∩₁Acq⦘ ⊆ ⦗F⦘) by solve_type_mismatch 10.
unionL; solve_type_mismatch 15.
Qed.

Lemma eco_sw_helper WF NRMW
  (SBLOC: ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo)
  (RMW_IN_RB: rmw ⊆ rb) 
  x y z (ECO: eco x y) (SW: sw y z) (NECO: ~ eco y z) :
  exists k, eco x k /\ sb k z /\ ~ rmw k z.
Proof.
assert (Wy: W y).
  apply eco_domb in ECO; try edone.
  apply sw_doma in SW; try edone.
  by solve_type_mismatch.
assert (SW1 := SW).
apply sw_domb in SW1; try edone.
repeat autounfold with type_unfolderDb in SW1.
destruct SW1, H; cycle 1.
- exfalso; apply NECO.
  apply sw_in_eco; try done.
  unfolder; ins; desf.
- exploit sw_in_eco_sb; eauto.
  unfolder; splits; eauto.
  unfold eqv_rel, seq; ins; desf.
  exists z0; splits; eauto using (eco_trans WF NRMW).
  intro A; eapply rmw_domb in A; auto; solve_type_mismatch.
Qed.

Lemma eco_sw WF NRMW
  (SBLOC: ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo)
  (RMW_IN_RB: rmw ⊆ rb) :
eco ⨾ (sw \ eco) ⊆ eco ⨾ (sb \ rmw).
Proof.
unfold seq, minus_rel, inclusion; ins; desc.
eapply eco_sw_helper; eauto.
Qed.

Lemma eco_seq_hb WF NRMW
  (SBLOC: ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo)
  (RMW_IN_RB: rmw ⊆ rb) : 
  eco ⨾ hb ⊆ eco ∪ eco ⨾ (sb \ rmw) ⨾ hb^?.
Proof.
  unfold hb; rewrite seq_ct_absorb_lt, cr_of_ct; eauto using eco_trans.
  rewrite minus_union_l.
  relsf; repeat apply inclusion_union_l; eauto with rel.
  rewrite RMW_IN_RB, rb_in_eco; auto with rel.
  sin_rewrite eco_sw; auto.
  rewrite !seqA; auto with rel.
Qed.

Lemma eco_almost_total WF NRMW x y 
  (ACTx: In x acts) (ACTy: In y acts)
  (RWx: RW x) (RWy: RW y) (LOC: loc lab x = loc lab y)
  (NEQ: x <> y): 
  eco x y \/ eco y x \/ exists z, rf z x /\ rf z y.
Proof.
unfold RC11_Events.RW, set_union in *.
assert (exists l, loc lab x = Some l).
by eapply rw_has_location; solve_type_mismatch.
cdes WF; cdes WF_RF; cdes WF_MO.
desf.  
- apply RF_TOT in RWx; try done.
  apply RF_TOT in RWy; try done.
  desf.
  assert (RF_LOC' := RF_LOC).
  specialize (RF_LOC _ _ RWx); specialize (RF_LOC' _ _ RWy); desc.
  destruct (classic (a=a0)); try subst; eauto.
  assert (mo a a0 \/ mo a0 a); cycle 1.
  { unfold eco. unfold rb.
    desf; [right; left | left];
    hahn_rewrite (NRMW_implies_original_rb WF NRMW); basic_solver 42. }
  eapply MO_TOT; splits; eauto; unfold set_inter; splits.
  eapply rf_acta; eauto.
  by eapply rf_doma; eauto.
  eby rewrite RF_LOC', <- LOC.
  by eapply rf_acta; eauto.
  by eapply rf_doma; eauto.
  by rewrite RF_LOC.
- apply RF_TOT in RWy; try done.
  desf.
  specialize (RF_LOC _ _ RWy); desc.
  destruct (classic (a=x)); [subst; unfold eco; basic_solver 5|].
  assert (mo a x \/ mo x a); cycle 1.
  { unfold eco. unfold rb.
    desf; [right; left | left];
    hahn_rewrite (NRMW_implies_original_rb WF NRMW); basic_solver 42. }
  eapply MO_TOT; splits; eauto; unfold set_inter; splits; eauto.
  by eapply rf_acta; eauto.
  by eapply rf_doma; eauto.
  eby rewrite RF_LOC, <- LOC.
- apply RF_TOT in RWx; try done.
  desf.
  specialize (RF_LOC _ _ RWx); desc.
  destruct (classic (a=y)); [subst; unfold eco; basic_solver 5|].
  assert (mo a y \/ mo y a); cycle 1.
  { unfold eco. unfold rb.
    desf; [left | right; left];
    hahn_rewrite (NRMW_implies_original_rb WF NRMW); basic_solver 42. }
  eapply MO_TOT; splits; eauto; unfold set_inter; splits; auto.
  by eapply rf_acta; eauto.
  by eapply rf_doma; eauto.
  eby rewrite RF_LOC.
  eby rewrite <- LOC.
- assert (mo x y \/ mo y x); [|  unfold eco; basic_solver 10].
  eapply MO_TOT; splits; eauto; unfold set_inter; splits; eauto.
  eby rewrite <- LOC.
Qed.

Lemma irr_hb COH: irreflexive hb.
Proof. red; ins; eapply COH; econstructor; eauto. Qed.

Lemma cww_mo 
  WF COH
  a b (A: hb a b)
  (Wa : W a) (Wb : W b) 
  (LOC: loc lab a = loc lab b) :
  mo a b.
Proof.
  assert (exists l, loc lab a = Some l).
  by eapply rw_has_location; solve_type_mismatch.
  desc.  
  ins; eapply tot_ex.
  - eapply WF.
  - unfolder; splits; try edone. eapply hb_actb; eauto. eby rewrite <- LOC.
  - unfolder; splits; try edone. eapply hb_acta; eauto.
  - intro; eapply COH.
    unfold eco, clos_refl, seq, union, eqv_rel; eauto 10.
  - intro; subst; eapply irr_hb; eauto.
Qed.

Lemma sb_loc_in_mo WF COH:
  ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo.
Proof.
  red; ins.
  unfold same_loc in H; unfolder in H; desf.
  apply cww_mo; auto using sb_in_hb.
Qed.

Lemma BasicRMW WF COH:
  forall a b (MO: a=b \/ mo a b) c (RF: rf b c) (RMW_CA: rmw c a), False.
Proof.
ins; apply rmw_in_sb, sb_in_hb in RMW_CA; eauto.
eapply COH; desf; unfold eco, clos_refl, seq, union, eqv_rel; eauto 10.
Qed.

Lemma rmw_in_rb WF COH: rmw ⊆ rb.
Proof.
  intros a b A; cdes WF; cdes WF_RMW; cdes WF_RF; cdes WF_MO.
  unfold seq in *; desf.
  assert (Ra: R a).
    by eapply rmw_doma; eauto.
  assert (ACT: In a acts).
    by eapply rmw_acta; eauto.
  specialize (RMW_LOC _ _ A); desf.
  destruct (RF_TOT a ACT Ra) as [c RF].
  unfold rb; unfolder; splits.
  - exists c; split; ins.
    specialize (RF_LOC _ _ RF); desf.
    assert (exists l, loc lab a = Some l).
    by eapply rw_has_location; solve_type_mismatch.
    desc.
    desf; eapply tot_ex; eauto using BasicRMW.
    unfolder; splits;
      [eapply rmw_actb; eauto| eapply rmw_domb; eauto| eby rewrite <- RMW_LOC].
    unfolder; splits;
      [eapply rf_acta; eauto| eapply rf_doma; eauto| eby rewrite RF_LOC].
  - apply or_not_and; left; intro; desf.
    apply RMW_IMM in A; destruct A.
    by cdes WF_SB; apply SB_IRR in H.
Qed.

Lemma rf_rmw_mo WF COH: 
    rf ⨾ rmw ⊆ mo.
Proof.
  rewrite rmw_in_rb; eauto using rf_seq_rb. 
Qed.

Lemma useq_mo WF NRMW COH:
   useq ⊆ mo.
Proof.
  rewrite (NRMW_implies_original_useq WF NRMW).
  eapply inclusion_t_ind, WF.
  eauto 10 using rf_rmw_mo.
Qed.

Lemma rs_mo WF NRMW COH: 
   rs ⊆ mo^?.
Proof.
  unfold rs.
  arewrite (⦗W∩₁Rlx⦘ ⊆ ⦗W⦘) by solve_type_mismatch.
  rewrite useq_mo, crE; relsf.
  sin_rewrite sb_loc_in_mo; auto.
  rewrite !inclusion_seq_eqv_l, crE; relsf.
  rewrite mo_seq_mo; eauto with rel.
Qed.

Lemma rel_mo WF NRMW COH: 
   ⦗W⦘ ⨾ release ⊆ mo^?.
Proof.
  unfold release; rewrite rs_mo; relsf.
  apply inclusion_union_l; [by rewrite !inclusion_seq_eqv_l|].
  unfold seq, eqv_rel; red; ins; desf.
  exfalso; solve_type_mismatch. 
Qed.

Lemma rel_hb_mo WF NRMW COH: 
    release ⊆ (hb^? ⨾ mo^?).
Proof.
  unfold release; rewrite rs_mo, !inclusion_seq_eqv_l, sb_in_hb; auto.
  basic_solver 10.
Qed.

Lemma transp_rf_rf_eco WF NRMW COH: 
    rf⁻¹ ⨾ rf ⨾ eco ⊆ eco.
Proof.
unfold eco; relsf.
rewrite rf_seq_rf; auto.
sin_rewrite rf_seq_mo; auto.
rewrite NRMW_implies_original_rb; auto.
rewrite !seqA.
sin_rewrite rf_seq_transp_rf; auto.
relsf.
Qed.

Lemma eco_transp_rf_rf WF NRMW COH: 
    eco ⨾ rf⁻¹ ⨾ rf ⊆ eco.
Proof.
  unfold eco; relsf.
  rewrite NRMW_implies_original_rb; auto.
  rewrite !seqA, !crE; relsf.
  arewrite_false (mo ⨾ rf⁻¹).
  { rewrite rf_dom; auto.
    rewrite mo_dom; auto.
    assert (T := NRMW_implies_type_mismatch NRMW).
    unfolder in *; ins; desf.
    specialize (T z0).
    solve_type_mismatch.
  }
  sin_rewrite !rf_seq_transp_rf; auto.
  basic_solver 8.
Qed.

Lemma hb_loc_in_eco WF NRMW COH: 
  ⦗RW⦘ ⨾ hb|loc ⨾ ⦗RW⦘ ⊆ eco ∪ (sb \ rmw) ∪ (sb \ rmw) ⨾ hb ⨾ (sb \ rmw).
Proof.
  unfold restr_eq_rel, same_loc.
  unfolder; ins; desf.
  rename H0 into HB, H2 into LOC, H3 into SAME_LOC, H into RWx, H1 into RWy.
  forward (apply eco_almost_total with (x:=x) (y:=y)); eauto.
    eapply hb_acta; eauto.
    eapply hb_actb; eauto.
    red in LOC; desf.
    intro; subst; eapply irr_hb; edone. 
  ins; desf; [basic_solver | |].
  by exfalso; eapply COH; basic_solver.
  apply ct_begin in HB.
  unfold seq in HB; desc.
  destruct HB as [HB|X]; cycle 1.
  exfalso; eapply sw_doma in X; eapply rf_domb in H; eauto.
  { assert (T := NRMW_implies_type_mismatch NRMW).
    apply T with x; solve_type_mismatch. }
  apply rtE in HB0.
  unfold eqv_rel, union in HB0; desf.
  - destruct (classic (rmw x y)).
    by left; left; apply rb_in_eco, rmw_in_rb; auto.
    by left; right; splits; eauto.
  - apply ct_end in HB0.
    unfold seq in HB0; desc.
    destruct HB1 as [HB1|X]; cycle 1.
    * exfalso.
      apply sw_in_sb_eco_sb in X; auto using sb_loc_in_mo, rmw_in_rb.
      unfold seq, eqv_rel, clos_refl in X; desf.
      + apply COH with (x:=x).
        exists z2; splits.
        apply ct_begin; basic_solver.
        right; apply eco_transp_rf_rf; auto; basic_solver 8.
      + apply COH with (x:=x).
        exists z2; splits.
        apply ct_begin; eexists; splits; try apply rt_end; basic_solver 6.
        by right; apply eco_transp_rf_rf; auto; basic_solver 8.
      + solve_type_mismatch.
      + solve_type_mismatch.
    * assert (~rmw x z0).
      { intro RMW_x_z0.
        apply COH with (x:=z0).
        exists y; splits.
        apply ct_end; basic_solver 6.
        apply rmw_in_rb, rb_in_eco in RMW_x_z0; auto.
        right; apply transp_rf_rf_eco; auto; basic_solver 8.
      }
      assert (~rmw z1 y).
      { intro RMW_z1_y.
        apply COH with (x:=x).
        exists z1; splits.
        apply ct_begin; basic_solver 6.
        apply rmw_in_rb, rb_in_eco in RMW_z1_y; auto.
        right; apply eco_transp_rf_rf; auto; basic_solver 8.
      }
      apply rtE in HB0; unfold union, eqv_rel in HB0; desf.
      + left; right; splits.
        cdes COH; cdes WF; cdes WF_SB; eapply SB_T; eauto.
        intro RMW_x_y.
        apply rf_domb in H0; auto.
        apply rmw_domb in RMW_x_y; auto.
        apply (NRMW_implies_type_mismatch NRMW) with y.
        solve_type_mismatch.
      + basic_solver 8.
Qed.

(******************************************************************************)
(** ** Propositions in Appendix C *)
(******************************************************************************)

Section C_RC11_Properties.
Hypothesis WF: Wf.

(* Proposition C.1 *)
Proposition C1_spo_eco NRMW : strict_partial_order eco.
Proof.
  unfold strict_partial_order; splits.
  - (* irreflexive *) by apply irr_eco.
  - (* transitive *) by apply eco_trans.
Qed.

(* Proposition C.2 *)
Hypothesis SB_IN_MO : ⦗W⦘ ⨾ sb|loc ⨾ ⦗W⦘ ⊆ mo.
Hypothesis RMW_IN_RB : rmw ⊆ rb.

Proposition C2_1_rs_in_eco NRMW : rs ⊆ eco^?.
Proof. by apply rs_in_eco. Qed.

Proposition C2_2_sw_in_eco NRMW : ⦗W⦘ ⨾ sw ⨾ ⦗R⦘ ⊆ eco.
Proof. by apply sw_in_eco. Qed.

Proposition C2_3_sw_in_eco_sb NRMW : ⦗W⦘ ⨾ sw ⨾ ⦗F⦘ ⊆ eco ⨾ sb.
Proof. by apply sw_in_eco_sb. Qed.

Proposition C2_4_eco_seq_hb NRMW : eco ⨾ hb ⊆ eco ∪ eco ⨾ (sb \ rmw) ⨾ hb^?.
Proof. by apply eco_seq_hb. Qed.

End C_RC11_Properties.

(* Proposition C.3 *)
Proposition C3
  dom_rf (DOM_RF: doma rf dom_rf)
  a (A: a ≡₁ W∩₁Rel \₁ dom_rf)
  : True.
Proof. Admitted.

End Consistency.

Hint Resolve con_wf.
Hint Unfold  E : unfolderDb.

(* Lemma fence_hb_r WF NRMW
  (SBLOC: ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo)
  (RMW_IN_RB: rmw ⊆ rb) : 
  ⦗Sc⦘⨾ hb ⨾ ⦗F~Sc⦘ ⊆
    ⦗Sc⦘⨾ sb ⨾ ⦗F~Sc⦘
  ∪ ⦗Sc⦘⨾ sb ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗Sc⦘⨾ eco ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ eco ⨾ hb ⨾ ⦗F~Sc⦘.
Proof.
  unfold hb.
  arewrite ((sb ∪ sw)⁺ ⊆ (sb ∪ sw) ⨾ (sb ∪ sw)＊) at 1.
    by rels.
  relsf; repeat apply inclusion_union_l.
   rewrite rtE at 1; relsf.
  rewrite sw_in_sb_eco_sb at 1; try done.
  arewrite (sb ⨾ ⦗F⦘ ⊆ sb).
  arewrite (sb ^? ⊆ (sb ∪ sw) ^?).
  arewrite ((sb ∪ sw) ^? ⨾ (sb ∪ sw)＊ ⊆ (sb ∪ sw)＊).
  rewrite rtE at 1; relsf.
  arewrite_false (eco ⨾ ⦗F~Sc⦘).
    rewrite eco_dom; try done.
    solve_type_mismatch.
  relsf.
  rewrite crE at 1; relsf.
  repeat apply inclusion_union_l; eauto with rel.
  rewrite !seqA.
  arewrite (⦗Sc⦘ ⨾ ⦗F⦘ ⊆ ⦗F~Sc⦘).
  solve_type_mismatch.
  arewrite (sb ⊆ (sb ∪ sw) ⁺).
  eauto with rel.
Qed.

Lemma fence_hb_l WF NRMW
  (SBLOC: ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo)
  (RMW_IN_RB: rmw ⊆ rb) :
  ⦗F~Sc⦘ ⨾ hb ⨾ ⦗Sc⦘ ⊆
    ⦗F~Sc⦘ ⨾ sb ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ sb ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ eco ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ eco ⨾ hb ⨾ ⦗F~Sc⦘.
Proof.
  unfold hb.
  arewrite ((sb ∪ sw)⁺ ⊆ (sb ∪ sw)＊ ⨾ (sb ∪ sw)).
  relsf; repeat apply inclusion_union_l; eauto with rel.
  by rewrite rtE at 1; relsf.
  rewrite sw_in_sb_eco_sb at 2; try done. 
  rewrite !seqA.
  arewrite ((⦗F⦘ ⨾ sb) ^? ⊆ (sb ∪ sw)^?).
  arewrite ((sb ∪ sw)＊ ⨾ (sb ∪ sw) ^? ⊆ (sb ∪ sw)＊).
  rewrite rtE; relsf.
  arewrite_false (⦗F~Sc⦘ ⨾ eco).
    rewrite eco_dom; try done.
    solve_type_mismatch.
  relsf.
  rewrite crE; relsf.
  repeat apply inclusion_union_l; eauto with rel.
  rewrite !seqA.
  arewrite (⦗F⦘ ⨾ ⦗Sc⦘⊆ ⦗F~Sc⦘).
    solve_type_mismatch.
  arewrite (sb ⊆ (sb ∪ sw) ⁺) at 2. 
  eauto with rel.
Qed.

Lemma fence_hb WF NRMW
  (SBLOC: ⦗W⦘ ⨾ sb |loc ⨾ ⦗W⦘ ⊆ mo)
  (RMW_RB: rmw ⊆ rb) : 
  ⦗F~Sc⦘ ⨾ hb ⨾ ⦗F~Sc⦘ ⊆
    ⦗F~Sc⦘ ⨾ sb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ sb ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ eco ⨾ hb ⨾ ⦗F~Sc⦘.
Proof.
  assert (M: sb ⨾ sb^? ⊆ sb).
    rewrite crE; relsf. 
    assert (T: transitive sb) by (eapply WF).
    by sin_rewrite (rewrite_trans T); eauto with rel.
  unfold hb.
  rewrite ct_begin at 1; rewrite !seqA; relsf.
  rewrite rtE at 1; relsf.
  repeat apply inclusion_union_l; eauto with rel.
  {
    rewrite ct_begin at 1; rewrite !seqA; relsf.
    rewrite rtE at 1; relsf.
    repeat apply inclusion_union_l; eauto with rel.
     assert (T: transitive sb) by (eapply WF).
     by sin_rewrite (rewrite_trans T); eauto with rel.
    by rewrite sb_in_hb at 1; eauto with rel.
   
    rewrite sw_in_sb_eco_sb at 1; try done.
    rewrite (inclusion_seq_eqv_l (dom := F)).
    rewrite (inclusion_seq_eqv_r (dom := F)).
    rewrite !seqA.
    sin_rewrite M.
    rewrite crE; relsf.
    rewrite rtE at 1; relsf.
    arewrite_false (eco ⨾ ⦗F~Sc⦘).
      rewrite eco_dom; try done.
      solve_type_mismatch.
    repeat apply inclusion_union_l; eauto 6 with rel.
    by rewrite ct_begin at 4; relsf; rewrite !seqA; eauto 8 with rel.
    by rewrite ct_begin at 4; relsf; rewrite !seqA; eauto 8 with rel.
  }
  rewrite sw_in_sb_eco_sb at 1; try done.
  rewrite (inclusion_seq_eqv_l (dom := F)).
  rewrite (inclusion_seq_eqv_r (dom := F)).
  rewrite !seqA; rewrite crE at 1; relsf.
  arewrite_false (⦗F~Sc⦘ ⨾ eco).
    rewrite eco_dom; try done.
    solve_type_mismatch.
  relsf.
  rewrite crE; relsf.
  rewrite rtE at 1; relsf.
  arewrite_false (eco ⨾ ⦗F~Sc⦘).
    rewrite eco_dom; try done.
    solve_type_mismatch.
  relsf.
  repeat apply inclusion_union_l; eauto 6 with rel.
  by rewrite ct_begin at 4; relsf; rewrite !seqA; eauto 8 with rel.
Qed. *)

(* Lemma cwr_mo 
    WF
    COH
    a b (A: (hb ⨾ rf⁻¹) a b)
    (Wa : W a) (Wb : W b) 
    (LOC: loc lab a = loc lab b) (NEQ: a <> b):
    mo a b.
Proof.
  unfold seq,transp in A; desc.
  assert (exists l, loc lab a = Some l).
    by eapply rw_has_location; solve_type_mismatch.
  desc.
  ins; eapply tot_ex.
  - eapply WF.
  - unfolder; splits; try edone. eapply rf_acta; eauto. eby rewrite <- LOC.
  - unfolder; splits; try edone. eapply hb_acta; eauto.
  - intro; eapply COH.
    eexists; splits; eauto.
    unfold eco, rb; unfolder; repeat right.
    eexists; splits; eauto.
    apply or_not_and; left; red; ins; desf.
    apply COH with a; basic_solver.
  - intro; subst; auto.
Qed. *)

(* Lemma crr_mo 
    WF
    COH
    a b (A: (rf ⨾ hb ⨾ rf⁻¹) a b)
    (Wa : W a) (Wb : W b) 
    (LOC: loc lab a = loc lab b) (NEQ: a <> b):
    mo a b.
Proof.
  unfolder in A; desc.
  assert (exists l, loc lab a = Some l).
    by eapply rw_has_location; solve_type_mismatch.
  desc.
  ins; eapply tot_ex.
  - eapply WF.
  - unfolder; splits; try edone. eapply rf_acta; eauto. eby rewrite <- LOC.
  - unfolder; splits; try edone. eapply rf_acta; eauto.
  - rewrite hb_eco_r_alt in COH. unfold rb in COH.
    repeat (apply irreflexive_union in COH; desf).
    intro; eapply COH0.
    eexists; splits; eauto.
    exists a; splits; auto.
    unfolder; splits; try basic_solver.
    apply or_not_and; left; red; ins; desf.
    apply COH4 with z; basic_solver.
  - intro; subst; auto.
Qed. *)

(* Lemma crw_mo 
    WF
    COH
    a b (A: (rf ⨾ hb) a b)
    (Wa : W a) (Wb : W b) 
    (LOC: loc lab a = loc lab b) :
    mo a b.
Proof.
  unfold seq in A; desc.
  assert (exists l, loc lab a = Some l).
    by eapply rw_has_location; solve_type_mismatch.
  desc.  
  ins; eapply tot_ex.
  - eapply WF.
  - unfolder; splits; try edone. eapply hb_actb; eauto. eby rewrite <- LOC.
  - unfolder; splits; try edone. eapply rf_acta; eauto.
  - intro; eapply COH.
    eexists; splits; eauto.
    unfold eco, clos_refl, seq, union, eqv_rel; eauto 10.
  - intro; subst; eapply COH.
    eexists; splits; eauto.
    unfold eco, clos_refl, seq, union, eqv_rel; eauto 10.
Qed. *)

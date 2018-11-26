Require Import Classical List Relations Peano_dec.
Require Import Hahn.
Require Import Basic RC11_Events RC11_Model RC11_Threads.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section WriteBefore.

Variable G : execution.

Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'mo'" := G.(mo).
Notation "'sw'" := G.(sw).
Notation "'rmw'" := G.(rmw).
Notation "'rb'" := G.(rb).
Notation "'hb'" := G.(hb).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'deps'" := G.(deps).
Notation "'eco'" := G.(eco).
Notation "'same_loc'" := G.(same_loc).
Notation "rel |loc" := (rel ∩ same_loc) (at level 1).
Notation "'psc'" := G.(psc).
Notation "'psc_base'" := G.(psc_base). 
Notation "'psc_f'" := G.(psc_f).
Notation "'scb'" := G.(scb).

Notation "'E'" := G.(E).
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
Notation "type ~ mode" := (type ∩₁ mode) (at level 1).

Hypothesis NRMW: NO_RMW_EVENTS G.

Definition wb0 := 
  ⦗W⦘ ⨾ (rmw⁻¹ ⨾ rf⁻¹)＊ ⨾ (rf^? ⨾ hb|loc ⨾ rf⁻¹^? \  (rf ⨾ rmw)＊ ) ⨾ ⦗W⦘.
Definition wb :=  rf ⨾ rmw ∪ wb0.

Definition consistent_wb :=
  << WF   : Wf G >> /\
  << WB  : acyclic wb >> /\
  << AT   : functional (rf ⨾ rmw)  >> /\
  << SC   : acyclic psc >> /\
  << SBRF : acyclic (sb ∪ rf) >>.

Lemma con_wb_wf  (CON: consistent_wb) : Wf G.
Proof. cdes CON; done. Qed.

Hint Resolve con_wb_wf.


Lemma wb0_acta (WF: Wf G) : doma wb0 E.
Proof.
cdes WF; unfold wb0.
clear_equivs ⦗W⦘.
rewrite rtE at 1; relsf.
apply union_doma; [| by eauto 12 using rmw_actb with rel].
apply minus_doma.
rewrite inter_inclusion, crE; relsf.
eauto 12 using hb_acta, rf_acta, rmw_actb with rel.
Qed.

Lemma wb_acta (WF: Wf G) : (doma wb (fun x => In x acts)).
Proof.
cdes WF; unfold wb.
apply union_doma.
by eauto 12 using hb_acta, rf_acta, rmw_actb with rel.
by apply wb0_acta.
Qed.

Lemma wb0_actb (WF: Wf G) : (domb wb0 (fun x => In x acts)).
Proof.
cdes WF; unfold wb0.
arewrite_id (⦗W⦘); rels.
apply seq_domb.
apply minus_domb.
rewrite (crE rf⁻¹), inter_inclusion; relsf.
eauto 12 using hb_actb, rf_acta with rel.
Qed.

Lemma wb_actb (WF: Wf G) : (domb wb (fun x => In x acts)).
Proof.
cdes WF; unfold wb.
apply union_domb.
by eauto using rmw_actb with rel.
by apply wb0_actb.
Qed.

Lemma wb0_act (WF: Wf G) : 
  wb0 ⊆ <| fun x => In x acts |> ⨾ wb0 ⨾ <| fun x => In x acts |>. 
Proof.
eapply act_helper; split; [apply wb0_acta| apply wb0_actb]; done.
Qed.

Lemma wb_act (WF: Wf G) : 
  wb ⊆ <| fun x => In x acts |> ⨾ wb ⨾ <| fun x => In x acts |>. 
Proof.
eapply act_helper; split; [apply wb_acta| apply wb_actb]; done.
Qed.

Lemma rmw_functional (WF: Wf  G) :
   functional rmw.
Proof.
cdes WF; cdes WF_RMW; cdes WF_SB.
unfold functional; intros x y z H0 H1.
assert (Ix: I x) by eby eapply no_rmw_from_init.
hahn_rewrite RMW_IMM in H0.
hahn_rewrite RMW_IMM in H1.
apply sb_immediate_adjacent in H0; try done.
apply sb_immediate_adjacent in H1; try done.
desf.
eapply adjacent_uniqe1 with (r:=sb); try edone.
by apply trans_irr_acyclic.
Qed.

Lemma transp_rmw_functional (WF: Wf  G) :
   functional rmw⁻¹.
Proof.
cdes WF; cdes WF_RMW; cdes WF_SB.
unfold functional; intros x y z H0 H1.
unfold transp in *.
assert (Iy: I y) by eby eapply no_rmw_from_init.
assert (Iz: I z) by eby eapply no_rmw_from_init.
hahn_rewrite RMW_IMM in H0.
hahn_rewrite RMW_IMM in H1.
apply sb_immediate_adjacent in H0; try done.
apply sb_immediate_adjacent in H1; try done.
desf.
eapply adjacent_uniqe2 with (r:=sb); try edone.
by apply trans_irr_acyclic.
Qed.

Lemma rf_rmw_wb (WF: Wf G) (FUN: functional (rf ⨾ rmw)) :
  rmw⁻¹ ⨾ rf⁻¹ ⨾ wb ⊆ wb^?.
Proof.
unfold wb; relsf.
apply inclusion_union_l; rels.
- rewrite <- !seqA with (r1 := rmw⁻¹).
 rewrite <- transp_seq.
apply functional_alt in FUN; rewrite FUN; basic_solver.
- unfold wb0 at 1.
arewrite_id (⦗W⦘) at 1; rels.
cdes WF; cdes WF_RMW; rewrite RMW_DOM at 1.
clear_equivs ⦗R⦘; rels.
rewrite transp_seq; rels; rewrite !seqA.
rewrite <- !seqA with (r1 := rmw⁻¹).
rels.
arewrite ((rmw⁻¹⨾ rf⁻¹) ^+ ⊆ (rmw⁻¹⨾ rf⁻¹) ＊).
unfold wb0; eauto with rel.
Qed.

Lemma rfU_successor (WF: Wf G) (FUN: functional (rf ⨾ rmw)) :
    Successor wb^+ (rf ⨾ rmw).
Proof.
red; splits; auto.
- rewrite transp_seq.
  apply functional_seq; [apply transp_rmw_functional; auto | apply WF].
- rewrite transp_seq; rewrite seqA, ct_begin.
  sin_rewrite rf_rmw_wb; [rels| auto| auto].
- unfold wb; eauto with rel.
Qed.

Lemma wb_base:
⦗W⦘ ⨾ rf^? ⨾ hb|loc ⨾ (rf⁻¹)^? ⨾ ⦗W⦘
⊆
wb＊.
Proof.
arewrite (⦗W⦘⨾ rf ^?⨾ hb|loc ⨾ (rf⁻¹)^?⨾ ⦗W⦘ ⊆
 (⦗W⦘⨾ rf^?⨾ hb|loc ⨾ (rf⁻¹)^?⨾ ⦗W⦘ \(rf⨾rmw)＊) ∪ (rf⨾rmw)＊).
by eapply inclusion_union_minus.
unfold wb, wb0.
apply inclusion_union_l; [|eauto with rel].
arewrite (⦗W⦘⨾ rf ^?⨾ hb|loc ⨾ (rf⁻¹)^?⨾ ⦗W⦘ \(rf⨾ rmw) ＊ ⊆
  ⦗W⦘⨾ (rf ^?⨾ hb|loc ⨾ (rf⁻¹)^? \ (rf⨾ rmw) ＊) ⨾ ⦗W⦘).
by rewrite minus_eqv_rel_helper, !seqA.
arewrite (⦗W⦘ ⊆ ⦗W⦘⨾ (rmw⁻¹⨾ rf⁻¹) ＊) at 1.
rewrite rtE; relsf.
Qed.

Lemma mo_wb_coh (WF: Wf G) (SBRF : acyclic (sb ∪ rf))
  (WB: wb ⊆ mo) :
  irreflexive (hb ⨾ eco^?).
Proof.
rewrite eco_alt2; auto.
rewrite crE; relsf.
rewrite !irreflexive_union; splits.
- rewrite hb_in_sb_rf; auto.
- rewrite hb_in_sb_rf; [ |auto].
  arewrite (rf ⊆ (sb ∪ rf)) at 2; rels.
  arewrite ((sb ∪ rf)^+ ⊆ (sb ∪ rf)＊); rels.
- cdes WF; cdes WF_RF; cdes WF_MO.
  eapply funeq_irreflexive.
  by ins; eauto 10 with rel.
  rewrite MO_DOM.
  rewrite <- !seqA, irreflexive_seqC, <- !seqA, irreflexive_seqC, !seqA.
  rewrite <- !seqA with (r3 := mo).
  arewrite (⦗W⦘ ⨾ rf^? ⊆ ⦗W⦘ ⨾ rf^? ;; ⦗RW⦘).
  by rewrite RF_DOM at 1; solve_type_mismatch 10.
  arewrite ( (rf⁻¹)^? ⨾ ⦗W⦘ ⊆ ⦗RW⦘ ;;  (rf⁻¹)^? ⨾ ⦗W⦘).
  by rewrite RF_DOM at 1; unfold RC11_Events.RW; basic_solver 42.
  seq_rewrite restr_eq_rel_same_loc.
  sin_rewrite wb_base.
  rewrite WB; relsf. 
Qed.

Lemma mo_wb_at (WF: Wf G)
  (SUC: Successor mo (rf ⨾ rmw)) :
  irreflexive (rb ⨾ mo ⨾ rmw⁻¹).
Proof.
rewrite NRMW_implies_original_rb; auto.
red in SUC; desc.
rewrite <- irreflexive_seqC, !seqA.
rewrite transp_seq, !seqA in SUC.
rewrite SUC.
cdes WF; cdes WF_MO.
relsf.
Qed.

Lemma two_rmws (WF: Wf G) (COH: irreflexive (hb ⨾ clos_refl eco))
  (AT: irreflexive (rb ⨾ mo ⨾ rmw⁻¹)) :
    functional (rf ⨾ rmw).
Proof.
red; unfold seq, transp; ins; desf; splits; auto.
assert (LOCz: exists l, loc z = Some l).
  eapply rw_has_location.
  eapply rmw_domb in H1; cdes WF; cdes WF_RMW; eauto.
  solve_type_mismatch.
desc.
cdes WF; cdes WF_RF; cdes WF_RMW.
assert (LOCy: loc y = Some l).
  apply RF_LOC in H; try done.
  apply RF_LOC in H0; try done.
  apply RMW_LOC in H1; try done.
  apply RMW_LOC in H2; try done.
  by congruence.
destruct (classic (y=z)) as [X|NEQ]; [eauto| exfalso].
cdes WF; cdes WF_MO; eapply MO_TOT in NEQ; eauto.
- desf; rewrite NRMW_implies_original_rb in AT; auto.
  * apply AT with (x:=z0).
    exists y; splits.
    repeat eexists; eauto.
    eapply rf_rmw_mo; eauto.
    exists z1; eauto.
    repeat eexists; eauto.
  * apply AT with (x:=z1).
    exists z; splits.
    repeat eexists; eauto.
    eapply rf_rmw_mo; eauto.
    exists z0; eauto.
    repeat eexists; eauto.
- unfolder; splits; eauto.
  eapply rmw_actb; eauto.
  eapply rmw_domb; eauto.
- unfolder; splits; eauto.
  eapply rmw_actb; eauto.
  eapply rmw_domb; eauto.
Qed.

Lemma mo_tot_helper (r: relation event)
  (WF: Wf G)
  (IRR: irreflexive r)
  (ACTS: r ⊆ ⦗E⦘ ⨾ (fun _ _ => True) ⨾ ⦗E⦘)
  (WW: r ⊆ ⦗W⦘⨾ (fun _ _ => True) ⨾ ⦗W⦘)
  (LOC: funeq loc r)
  (MO: irreflexive (r ⨾ mo)):
 r ⊆ mo.
Proof.
red; ins.
assert (exists l, loc x = Some l).
by eapply rw_has_location; apply WW in H; generalize H; solve_type_mismatch.
desc.
eapply tot_ex.
eapply WF.
unfolder; splits; eauto.
apply ACTS in H; generalize H; basic_solver.
apply WW in H; generalize H; basic_solver.
eby apply LOC in H;  rewrite <- H.
unfolder; splits; eauto.
apply ACTS in H; generalize H; basic_solver.
apply WW in H; generalize H; basic_solver.
generalize MO; basic_solver 10.
intro; subst; eapply IRR; eauto.
Qed.

Lemma transp_rmw_rf_mo (CON: consistent G) :
(rmw⁻¹⨾ rf⁻¹)⨾ mo ⊆ mo^? .
Proof.
rewrite crE.
apply inclusion_minus_l.
apply mo_tot_helper; auto.
basic_solver 10.
all: arewrite(fun __ => __ \ ⦗fun _ : event => True⦘ ⊆ __).
- cdes CON; cdes WF; cdes WF_SB; cdes WF_MO.
  rewrite rmw_in_sb; auto.
  rewrite SB_ACT, MO_ACT.
  basic_solver.
- cdes CON; cdes WF; cdes WF_RMW; cdes WF_MO.
  rewrite RMW_DOM, MO_DOM.
  basic_solver.
- cdes CON; cdes CON; cdes WF; cdes WF_RMW; cdes WF_RF; cdes WF_MO.
  eauto with rel.
- arewrite (rf⁻¹ ⨾ mo ⊆ rb).
    by cdes CON; apply NRMW_implies_original_rb.
  rotate 2.
  by cdes CON.
Qed.

Lemma transp_rmw_rf_mo1 (CON: consistent G) :
(rmw⁻¹⨾ rf⁻¹)⨾ (mo \ (rf⨾ rmw) ＊) ⊆ mo \ (rf⨾ rmw) ＊.
Proof.
rewrite fun_seq_minus_helper.
2: apply functional_seq; [apply transp_rmw_functional; auto | apply CON].
red; unfold minus_rel; ins;desc.
assert (MO: mo^? x y).
apply transp_rmw_rf_mo; eauto.
destruct MO.
* exfalso; subst; unfold seq in *; desf.
  apply H0; eauto.
  eexists; splits; eauto.
  econs; unfold transp in *; desf; eauto.
* splits; eauto.
  intro.
  apply H0.
  destruct H; desf.
  eexists; splits; eauto.
   unfold transp, seq in H; desf; eauto.
  eapply clos_trans_in_rt, t_step_rt.
  eexists; unfold seq; eauto.
Qed.

Lemma wb0_in_mo (CON: consistent G) : wb0 ⊆ mo \ (rf⨾ rmw) ＊.
Proof.
eapply rt_ind_left with (P:= fun __ => ⦗W⦘⨾ __⨾ 
  (rf ^?⨾ hb|loc ⨾ (rf⁻¹) ^? \ (rf⨾ rmw) ＊)⨾ ⦗W⦘).
- eauto with rel.
- rels.
arewrite ((rf ^?⨾ hb|loc ⨾ (rf⁻¹) ^?) \ (rf⨾ rmw) ＊ ⊆
(rf ^?⨾ hb|loc ⨾ (rf⁻¹) ^?) \ (rf⨾ rmw) ＊ \ (rf⨾ rmw) ＊).
rewrite minus_eqv_rel_helper.
apply inclusion_minus_mon; try done.
 eapply mo_tot_helper; eauto.
  * arewrite_id (⦗W⦘); rels.
     basic_solver.
  * transitivity wb0.
    unfold wb0.
    rewrite rtE with (r:=rmw⁻¹⨾ rf⁻¹); relsf.
    etransitivity; [eapply wb0_act; eauto| basic_solver].
  * basic_solver 10.
  * cdes CON; cdes WF; cdes WF_RF; cdes WF_RMW.
    eauto 10 using loceq_hb_loc with rel.
  * arewrite (fun __ => __\ (rf⨾ rmw) ＊ ⊆ __).
    arewrite_id !(⦗W⦘).
    rels.
    apply irreflexive_seqC.
    rewrite !crE; relsf.
    arewrite (rf⁻¹ ⨾ mo ⊆ rb) by cdes CON; apply NRMW_implies_original_rb.
    rewrite rb_in_eco, mo_in_eco, rf_in_eco; eauto.
    assert (transitive eco).
      by apply eco_trans; eauto.
    relsf.
    arewrite (eco ⊆ eco^?).
    rewrite inter_inclusion.
    by cdes CON.
- ins. rewrite !seqA.
 arewrite (rf⁻¹  ⊆ rf⁻¹ ⨾ ⦗W⦘) at 1.
      by cdes CON; cdes WF; generalize (rf_doma WF_RF); basic_solver 10.
    rewrite H.
    arewrite_id (⦗W⦘) at 1.
    rels.  
  rewrite <- !seqA with (r1 := rmw⁻¹).
by apply transp_rmw_rf_mo1.
Qed.

Lemma wb_in_mo (CON: consistent G) : wb ⊆ mo.
Proof.
apply inclusion_union_l.
apply rf_rmw_mo; eauto; apply CON.
etransitivity; [apply wb0_in_mo; eauto | basic_solver].
Qed.

Lemma wb_consistency : consistent G -> consistent_wb.
Proof.
unfold consistent_wb.
intro CON.
 cdes CON; ins; desf; splits; eauto.
rewrite wb_in_mo; try done.
red; cdes WF; cdes WF_MO; relsf.
apply two_rmws; eauto.
Qed.

End WriteBefore.
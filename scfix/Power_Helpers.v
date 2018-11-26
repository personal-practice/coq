(******************************************************************************)
(** * Helpers for the Power memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Power_Events Power_Model Power_Domains Power_Locations
  Power_Automation Power_Irreflexive Power_Threads.

Set Implicit Arguments.

Section Power_Helpers.

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
Implicit Type CON : PowerConsistent.

(******************************************************************************)
(** ** Basic *)
(******************************************************************************)
Lemma internal_in_sb CON (r: relation event) : 
  (r = mo) \/ (r = rb) \/ (r = rf) -> r∙ ⊆ sb.
Proof.
  unfolder; ins; desf; cycle_detector.
Qed.

Lemma rf_rf: rf ⨾ rf ⊆ ∅₂.
Proof.
  arewrite (rf ⊆ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘) by domain_solver.
  type_solver.
Qed.

Lemma rf_mo: rf ⨾ mo ⊆ ∅₂.
Proof.
  arewrite (rf ⊆ rf ⨾ ⦗R⦘) by domain_solver.
  arewrite (mo ⊆ ⦗W⦘ ⨾ mo) by domain_solver.
  type_solver.
Qed.

Lemma rf_rb_in_mo CON : rf ⨾ rb ⊆ mo.
Proof. unfolder; ins; cycle_detector. Qed.

Lemma mo_mo: mo ⨾ mo ⊆ mo.
Proof. by unfold_wf; apply rewrite_trans. Qed.

Lemma rb_mo: rb ⨾ mo ⊆ rb.
Proof. by unfold Power_Model.rb; rewrite seqA, mo_mo. Qed.

Lemma mo_rb: mo ⨾ rb ⊆ ∅₂.
Proof.
  arewrite (mo ⊆ mo ⨾ ⦗W⦘) by domain_solver.
  arewrite (rb ⊆ ⦗R⦘ ⨾ rb) by domain_solver.
  type_solver.
Qed.

Lemma rb_rb: rb ⨾ rb ⊆ ∅₂.
Proof.
  arewrite (rb ⊆ rb ⨾ ⦗W⦘) at 1 by domain_solver.
  arewrite (rb ⊆ ⦗R⦘ ⨾ rb) at 2 by domain_solver.
  type_solver.
Qed.

(******************************************************************************)
(** ** Domains *)
(******************************************************************************)
Lemma ppo_components_dom :
  doma ii RW /\ doma ic RW /\ doma ci RW /\ doma cc RW /\
  domb ii RW /\ domb ic RW /\ domb ci RW /\ domb cc RW.
Proof.
  remember (fun x y => RW x /\ RW y) as P.
  assert (forall x y : event,
    (ii x y -> P x y) /\
    (ic x y -> P x y) /\
    (ci x y -> P x y) /\
    (cc x y -> P x y)).
    by (apply ppo_comp_ind; subst; ins; vauto; desf;
        red in H; unfolder in H; desf; type_solver).
  unfold doma, domb; splits; ins; specialize (H x y); desf; intuition.
Qed.

Lemma ii_doma : doma ii RW. Proof. apply ppo_components_dom. Qed.
Lemma ic_doma : doma ic RW. Proof. apply ppo_components_dom. Qed.
Lemma ci_doma : doma ci RW. Proof. apply ppo_components_dom. Qed.
Lemma cc_doma : doma cc RW. Proof. apply ppo_components_dom. Qed.
Lemma ii_domb : domb ii RW. Proof. apply ppo_components_dom. Qed.
Lemma ic_domb : domb ic RW. Proof. apply ppo_components_dom. Qed.
Lemma ci_domb : domb ci RW. Proof. apply ppo_components_dom. Qed.
Lemma cc_domb : domb cc RW. Proof. apply ppo_components_dom. Qed.

Lemma ii0_doma : doma ii0 RW.
Proof. (arewrite (ii0 ⊆ ii) by vauto); apply ii_doma. Qed.
Lemma ci0_doma : doma ci0 RW.
Proof. (arewrite (ci0 ⊆ ci) by vauto); apply ci_doma. Qed.
Lemma cc0_doma : doma cc0 RW.
Proof. (arewrite (cc0 ⊆ cc) by vauto); apply cc_doma. Qed.
Lemma ii0_domb : domb ii0 RW.
Proof. (arewrite (ii0 ⊆ ii) by vauto); apply ii_domb. Qed.
Lemma ci0_domb : domb ci0 RW.
Proof. (arewrite (ci0 ⊆ ci) by vauto); apply ci_domb. Qed.
Lemma cc0_domb : domb cc0 RW.
Proof. (arewrite (cc0 ⊆ cc) by vauto); apply cc_domb. Qed.

(******************************************************************************)
(** ** Alternative Definitions *)
(******************************************************************************)
Lemma lwsync_alt : lwsync ≡ 
  ⦗R⦘ ⨾ sb ⨾ ⦗F_lwsync⦘ ⨾ sb ⨾ ⦗RW⦘ ∪ ⦗W⦘ ⨾ sb ⨾ ⦗F_lwsync⦘ ⨾ sb ⨾ ⦗W⦘.
Proof.
  unfold Power_Model.lwsync; red; split.
  - repeat (rewrite ?seq_eqv_r, ?seq_eqv_l). unfolder; ins; desf.
    apply not_and_or in H0. destruct H, H4; desf;
    (left+right); repeat (eexists; splits; eauto); type_solver.
  - unionL;
    repeat (rewrite ?seq_eqv_r, ?seq_eqv_l); unfolder; ins; desf; splits;
    try (repeat eexists; splits; eauto; type_solver);
    try (red; ins; type_solver).
Qed.

Lemma eco_alt CON : eco ⊆ ⦗RW⦘ ⨾ sb ∪ rf∘ ∪ mo ⨾ rf^? ∪ rb∘ ⨾ rf^? ∪ rb∙ ⨾ rf∘.
Proof.
  unfold Power_Model.eco.
  rewrite internal_or_external with (r := rf) at 1.
  rewrite internal_or_external with (r := rb) at 1.
  rewrite seq_union_l, <- unionA.
  arewrite (rb∙ ⨾ rf^? ⊆ ⦗RW⦘ ⨾ sb ∪ rb∙ ⨾ rf∘).
  { case_refl rf.
    - unionR left.
      arewrite (rb∙ ⊆ ⦗RW⦘ ⨾rb∙) by domain_solver.
      by rewrite internal_in_sb; auto.
    - rewrite internal_or_external with (r := rf) at 1.
      case_union_2 _ rf∘.
      + arewrite (rb∙ ⊆ ⦗RW⦘ ⨾rb∙) by domain_solver.
        rewrite internal_in_sb at 1; eauto.
        rewrite internal_in_sb at 1; eauto.
        arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
        by unionR left.
      + by unionR right.
  }
  arewrite (rf∙ ⊆ ⦗RW⦘ ⨾ rf∙) by domain_solver.
  arewrite (rf∙ ⊆ sb) by eapply internal_in_sb; eauto.
  rewrite <- unionA.
  basic_solver 42.
Qed.

(******************************************************************************)
(** ** Orders *)
(******************************************************************************)
Lemma sb_spo : strict_partial_order sb.
Proof. by red; splits; unfold_wf. Qed.

(******************************************************************************)
(** ** Transitivity *)
(******************************************************************************)

Lemma sb_trans : transitive sb.
Proof. by unfold_wf. Qed.

Lemma mo_trans : transitive mo.
Proof. by unfold_wf. Qed.

Lemma irrefl_trans : forall (A: Type) (r: relation A), 
  irreflexive r⁺ -> irreflexive r.
Proof.
  ins. apply irreflexive_inclusion with (r':=r⁺); auto using ct_step.
Qed.

Lemma ii_trans : transitive ii.
Proof. vauto. Qed.

Lemma same_loc_trans : transitive same_loc.
Proof. unfold Power_Model.same_loc; red; ins; desf; split; loc_solver. Qed.

Lemma sbloc_trans : transitive sb|loc.
Proof.
  red; ins.
  unfolder in *; desf; split.
  - unfold_wf; eapply SB_T; eauto.
  - apply same_loc_trans with y; auto.
Qed.

Lemma psbloc_trans : transitive psbloc.
Proof.
apply transitiveI.
unfold Power_Model.psbloc. arewrite_id ⦗I⦘ at 2; rels.
unfold inclusion, seq, minus_rel, eqv_rel.
ins; desf; split; rename z1 into x.
- exists x; split; eauto.
  exists y; split; eauto.
  eapply sbloc_trans; eauto.
- red; ins; desf.
  (* sb-totality for <z,z1> *)
  assert (Z_Z1: sb z z1 \/ sb z1 z).
  { cdes WF; cdes WF_SB.
    assert (same_thread z z1) by
      (unfolder in *; desf; eapply sb_diamond_implies_st; eauto).
    assert (exists i, tid z = Some i /\ tid z1 = Some i) by 
      by apply st_implies_tid.
    desf.
    eapply SB_TOT;
      try (by red; split; eauto; act_solver);
      red; type_solver. 
  }
  desf; cdes WF; cdes WF_SB; unfold restr_eq_rel in *.
  + (* sb z z1 *)
    contradict H1.
    exists z1; splits; eauto.
    red; split; auto; red; split; auto; loc_solver.
  + (* sb z1 z *)
    contradict H4.
    exists z1; splits; eauto.
Qed.

Lemma eco_trans CON : transitive eco.
Proof.
  apply transitiveI.
  unfold Power_Model.eco.
  rewrite crE.
  relsf.
  unionL; repeat rewrite ?seq_union_l, ?seq_union_r, ?seqA;
  (try sin_rewrite (rf_rb_in_mo CON));
  (try sin_rewrite mo_mo);
  (try sin_rewrite rb_mo);
  (try by sin_rewrite rf_rf; rels; eauto 10 with rel);
  (try by sin_rewrite rf_mo; rels; eauto 10 with rel);
  (try by sin_rewrite mo_rb; rels; eauto 10 with rel);
  (try by sin_rewrite rb_rb; rels; eauto 10 with rel);
  by eauto 20 with rel.
Qed.

Hint Resolve sb_trans mo_trans irrefl_trans ii_trans same_loc_trans psbloc_trans
eco_trans : rel_full.

(******************************************************************************)
(** ** Irreflexiveness *)
(******************************************************************************)

Lemma eco_irr CON : irreflexive eco.
Proof.
  unfold Power_Model.eco.
  unionL; try case_refl rf;
  try solve_irreflexive;
  (unfolder; ins; desf; cycle_detector0 x z).
Qed.

(******************************************************************************)
(** ** Acyclicity *)
(******************************************************************************)

Lemma sb_acyclic : acyclic sb.
Proof. unfold_wf; by apply trans_irr_acyclic. Qed.

(******************************************************************************)
(** ** Completeness *)
(******************************************************************************)

Lemma complete_exists
  x b (INB: In b acts) (B: (restrict_location R x) b) : 
  exists d, (restrict_location W x) d /\ rf d b.
Proof.
  cdes WF; cdes WF_RF; cdes B.
  destruct (RF_TOT b INB B0); subst.
  exists x0.
  splits; auto.
  red; split.
  type_solver.
  loc_solver.
Qed.

(******************************************************************************)
(** ** Inclusion *)
(******************************************************************************)
Lemma ci_in_ii : ci ⊆ ii.
Proof. unfolder; vauto. Qed.
Lemma ci_in_ic : ci ⊆ ic.
Proof. unfolder; vauto. Qed.
Lemma ii_in_ic : ii ⊆ ic.
Proof. unfolder; vauto. Qed.
Lemma ci_in_cc : ci ⊆ cc.
Proof. unfolder; vauto. Qed.
Lemma cc_in_ic : cc ⊆ ic.
Proof. unfolder; vauto. Qed.

Lemma icci_in_ii : ic ⨾ ci ⊆ ii.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma iiii_in_ii : ii ⨾ ii ⊆ ii.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma iccc_in_ic : ic ⨾ cc ⊆ ic.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma iiic_in_ic : ii ⨾ ic ⊆ ic.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma ciii_in_ci : ci ⨾ ii ⊆ ci.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma ccci_in_ci : cc ⨾ ci ⊆ ci.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma ciic_in_cc : ci ⨾ ic ⊆ cc.
Proof. unfolder; ins; desf; vauto. Qed.
Lemma cccc_in_cc : cc ⨾ cc ⊆ cc.
Proof. unfolder; ins; desf; vauto. Qed.

Hint Resolve ci_in_ii ci_in_ic ii_in_ic ci_in_cc cc_in_ic icci_in_ii iiii_in_ii
  iccc_in_ic iiic_in_ic ciii_in_ci ccci_in_ci ciii_in_ci cccc_in_cc
: rel_full.

Lemma ppo_components_in_sb (SC: acyclic (sb|loc ∪ rf ∪ rb ∪ mo)) : 
  ii ⊆ sb /\ ic ⊆ sb /\ ci ⊆ sb /\ cc ⊆ sb.
Proof.
  assert (IC_IN_SB: ic ⊆ sb).
  { cdes WF; cdes WF_SB; cdes WF_DEPS; cdes WF_RF.
    clear - WF SC SB_T DATA_IN_SB ADDR_IN_SB CTRL_IN_SB CTRLI_IN_SB.
    red; eapply ic_rec with (P:=sb) (P0:=sb) (P1:=sb) (P2:=sb); ins; eauto.
    - (* ii0 *) 
      red in H; unfolder in H; desf; eauto using rf_st_implies_sb.
      do 2 red in H; unfolder in H; desf.
      assert (~ sb y x).
      { red; ins. apply SC with x.
        apply t_trans with y.
        - apply t_trans with z; apply t_step; unfold union; auto.
        - apply t_step; unfolder; repeat left; splits; auto; loc_solver.
      }
      assert (sb x y \/ sb y x).
      { apply st_implies_sb; auto; try act_solver.
        red; ins; subst. apply SC with y.
        apply t_trans with z; apply t_step; unfold union; auto.
      }
      desf.
    - (* ci0 *) repeat red in H; desf; eauto with rel.
      + (* ctrl_isync *)
        red in H; unfolder in H; desf.
        assert (I x) by type_solver.
        apply CTRLI_IN_SB in H.
        assert (~ sb y x).
        { red; ins; assert (sb x x) by (by unfold_wf; apply SB_T with y).
          solve_irreflexive. }
        assert (sb x y \/ sb y x).
        { apply st_implies_sb; auto; try act_solver; try thread_solver.
          red; ins; subst; contradiction. }
        desf.
      + (* detour *)
        red in H; unfolder in H; desf.
        assert (~ sb y x).
        { red; ins; apply SC with x; apply t_trans with y.
          - apply t_trans with z; apply t_step; unfold union; auto.
          - apply t_step; unfolder; repeat left; splits; auto; loc_solver.
        }
        assert (sb x y \/ sb y x).
        { apply st_implies_sb; auto; try act_solver.
          red; ins; subst; apply SC with y.
          apply t_trans with z; apply t_step; unfold union; auto. }
        desf.
    - (* cc0 *) unfold Power_Model.cc0 in H; unfolder in H; desf; eauto with rel.
  }
  splits; auto.
  - by rewrite ii_in_ic.
  - by rewrite ci_in_ic.
  - by rewrite cc_in_ic.
Qed.

Lemma psbloc_in_sb : psbloc ⊆ sb.
Proof. unfold Power_Model.psbloc; unfolder; ins; desf. Qed.

Lemma ppo_in_sb CON : ppo ⊆ sb.
Proof.
  unfold Power_Model.ppo.
  clear_equivs ⦗R⦘.
  clear_equivs ⦗W⦘.
  by cdes CON; apply inclusion_union_l; apply ppo_components_in_sb.
Qed.

Lemma rdw_in_ppo : rdw ⊆ ppo.
Proof.
  arewrite (rdw ⊆ ⦗R⦘ ⨾ rdw ⨾ ⦗R⦘).
    by domain_solver.
  arewrite (rdw ⊆ ii).
    by red; ins; apply II0; red; basic_solver.
  unfold Power_Model.ppo.
  basic_solver.
Qed.

Lemma deps_in_sb : deps ⊆ sb.
Proof.
  cdes WF; cdes WF_DEPS.
  unfold Power_Model.deps.
  repeat apply inclusion_union_l; auto.
Qed.

Lemma addrsb_in_sb : addr ⨾ sb ⊆ sb.
Proof.
  cdes WF; cdes WF_DEPS; cdes WF_SB.
  arewrite (addr ⊆ sb).
  by apply (rewrite_trans SB_T).
Qed.

Lemma rfi_in_ii : rf∙ ⊆ ii.
Proof.
  red; ins. apply II0. do 2 red. by right.
Qed.

Lemma detour_in_ii : detour ⊆ ii.
Proof.
  red. ins. apply CI. apply CI0. do 2 red. by right.
Qed.

Lemma data_in_Rii : data ⊆ ⦗R⦘ ⨾ ii.
Proof.
cdes WF; cdes WF_DEPS; rewrite DATA.
hahn_frame; unfolder; ins; apply II0; econs; unfolder; tauto.
Qed.

Lemma data_in_iiW : data ⊆ ii ⨾ ⦗W⦘.
Proof.
cdes WF; cdes WF_DEPS; rewrite DATA.
hahn_frame; unfolder; ins; apply II0; econs; unfolder; tauto.
Qed.

Lemma data_in_RiiW : data ⊆ ⦗R⦘ ⨾ ii ⨾ ⦗W⦘.
Proof.
cdes WF; cdes WF_DEPS; rewrite DATA.
hahn_frame; unfolder; ins; apply II0; econs; unfolder; tauto.
Qed.

Lemma addr_in_Rii : addr ⊆ ⦗R⦘ ⨾ ii.
Proof.
cdes WF; cdes WF_DEPS; rewrite ADDR.
hahn_frame; unfolder; ins; apply II0; econs; unfolder; tauto.
Qed.

Lemma ctrl_in_Rcc : ctrl ⨾ ⦗RW⦘ ⊆ ⦗R⦘ ⨾ cc.
Proof.
  arewrite (ctrl ⊆ ⦗R⦘ ⨾ ctrl) by domain_solver.
  arewrite (ctrl ⨾ ⦗RW⦘ ⊆ cc).
  { rewrite cc_alt; unionR left -> left -> left.
    by unfold Power_Model.cc0; unionR left -> right. }
  done.
Qed.

Lemma depsW_in_ppo : deps ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  unfold Power_Model.deps; rewrite !seq_union_l; unionL;
  unfold Power_Model.ppo; unionR right.
    by rewrite data_in_Rii; auto; arewrite (ii ⊆ ic).
    by rewrite addr_in_Rii; auto; arewrite (ii ⊆ ic).
    arewrite (⦗W⦘ ⊆ ⦗RW⦘ ⨾ ⦗W⦘) at 1 by domain_solver.
    by sin_rewrite ctrl_in_Rcc; auto; arewrite (cc ⊆ ic).
Qed.

Lemma addrsbW_in_ppo : addr ⨾ sb ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  cdes WF; cdes WF_DEPS.
  rewrite ADDR.
  right; unfold seq, eqv_rel in *; desf; repeat eexists; eauto.
  apply CC, CC0.
  red; unfolder; eauto; right.
  repeat (eexists; splits; eauto); do 2 red; auto.
Qed.

Lemma depsUaddrsbW_in_ppo : (deps ∪ addr ⨾ sb) ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  unfold inclusion; ins.
  apply seq_union_l in H; unfold union in H; desf.
    by apply depsW_in_ppo.
    by apply seqA in H; apply addrsbW_in_ppo.
Qed.

Lemma addr_rbi_in_addr_sb CON : addr ⨾ rb∙ ⊆ addr ⨾ sb.
Proof.
  unfolder; ins; desf.
  exists z; split; auto.
  cycle_detector.
Qed.

Lemma rdw_rbi_in_rbi CON : rdw ⨾ rb∙ ⊆ rb∙.
Proof.
  unfold Power_Model.rdw; unfold Power_Model.rb at 1; unfolder.
  intros a c. ins; desf.
  rename z1 into w, z0 into w', z into b.
  split.
    by red; unfolder; exists w; split; auto; cycle_detector.
    thread_solver.
Qed.

Lemma rbi_in_sb CON : rb∙ ⊆ sb.
Proof. unfolder; ins; cycle_detector. Qed.

Lemma detour_rbi_in_mo CON : detour ⨾ rb∙ ⊆ mo.
Proof.
  unfold Power_Model.detour; unfolder; ins; desf.
  apply mo_trans with z0; auto.
  cycle_detector.
Qed.

Lemma ctrli_rbi_in_ci0 CON: 
  ctrl_isync ⨾ rb∙ ⊆ ci0.
Proof.
  arewrite (rb∙ ⊆ rb∙ ⨾ ⦗RW⦘) by domain_solver.
  rewrite rbi_in_sb; auto.
  cdes WF; cdes WF_DEPS.
  sin_rewrite CTRLI_SB.
  vauto.
Qed.

Lemma R_ci0_W_in_ppo : ⦗R⦘ ⨾ ci0 ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  unfold Power_Model.ppo; apply inclusion_union_r; right.
  unfolder; ins; desf.
  repeat (eexists; splits; eauto).
  by apply II, CI, CI0.
Qed.

(******************************************************************************)
(** ** L <-> PPO components *)
(******************************************************************************)
Lemma L_in_union : L ⊆ ii ∪ ic ∪ ci ∪ cc.
Proof.
  red; ins.
  apply L_rec with (G:=G) (x:=x) 
  (P:=fun y => (ii ∪ ic ∪ ci ∪ cc) x y) (P0:=fun y => (ii ∪ ci) x y);
  auto; ins; try vauto; try (by unfolder in *; desf; (right + left); vauto).
  - left; left; right; unfolder in *; desf; vauto.
    assert (ci ⊆ ic) by (unfolder; vauto).
    apply H3 in H1; vauto.
Qed.

Lemma seq_alt A (r r' r'' : relation A) :
  (forall x y, r' x y -> forall z, r z x -> r'' z y) <->
  r ⨾ r' ⊆ r''.
Proof.
  split.
  - ins; red; ins; unfold seq in H0; desf; eapply H; eauto; edone.
  - unfolder; ins; apply H; eexists; splits; eauto.
Qed.

Lemma basic_to_transitional : 
  (Li^? ⨾ ii ⊆ Li) /\
  (Li^? ⨾ ic ⊆ L) /\
  (L^? ⨾ ci ⊆ Li) /\
  (L^? ⨾ cc ⊆ L).
Proof.
  rewrite <- !seq_alt.
  cut (forall x y, 
    (ii x y -> forall z, Li^? z x -> Li z y) /\ 
    (ic x y -> forall z, Li^? z x -> L z y) /\
    (ci x y -> forall z, L^? z x -> Li z y) /\
    (cc x y -> forall z, L^? z x -> L z y)).
  { ins; splits; ins; desf;
    specialize (H x y); desf; eauto. }
  apply ppo_comp_ind with 
  (*ii*) (P:=fun x y => forall z, (Li^?) z x -> Li z y)
  (*ic*) (P0:=fun x y => forall z, (Li^?) z x -> L z y)
  (*ci*) (P1:=fun x y => forall z, (L^?) z x -> Li z y)
  (*cc*) (P2:=fun x y => forall z, (L^?) z x -> L z y);
  rewrite ?seq_alt;
  (* base cases *)
  try (by unfolder; ins; desf; vauto);
  ins;
  (* single derivations *)
  try (by apply H2; right; apply H0);
  (* double derivations *)
  try (by apply H0; red in H1; desf; (left + right); vauto);
  by apply L_Li, H0.
Qed.

Lemma L_Li_in_ppo_components : Li ⊆ ii ∪ ci /\ L ⊆ ii ∪ ic ∪ ci ∪ cc.
Proof.
  unfolder.
  assert (forall x y,
    (L x y -> ii x y \/ ic x y \/ ci x y \/ cc x y) /\ 
    (Li x y -> ii x y \/ ci x y)
  ).
  { ins; apply L_comb with
      (P := fun y => ii x y \/ ic x y \/ ci x y \/ cc x y)
      (P0 := fun y => ii x y \/ ci x y);
    auto; ins.
    all: try by vauto.
    all: try by (desf; by (left + right); vauto).
    all: try by (desf; by repeat right; vauto).
    desf; by (right; left + (repeat right)); vauto.
  }
  split; ins; specialize (H x y); desf; intuition.
Qed.

Lemma Li_is_ii : Li ≡ ii.
Proof.
  split.
  - arewrite (Li ⊆ ii ∪ ci) by apply L_Li_in_ppo_components.
    arewrite (ci ⊆ ii).
    basic_solver.
  - red; ins.
    assert (Li^? ⨾ ii ⊆ Li) by apply basic_to_transitional.
    apply H0; eexists; splits; eauto.
Qed.

Lemma L_in_ii_ic : L ⊆ ii ∪ ic.
Proof.
  arewrite (L ⊆ ii ∪ ic ∪ ci ∪ cc) by apply L_Li_in_ppo_components.
  arewrite (ci ⊆ ic); arewrite (cc ⊆ ic); basic_solver.
Qed.

Lemma L_is_ic : L ≡ ic.
Proof.
  split.
  - arewrite (L ⊆ ii ∪ ic ∪ ci ∪ cc) by apply L_Li_in_ppo_components.
    arewrite (ii ⊆ ic); arewrite (ci ⊆ ic); arewrite (cc ⊆ ic).
    basic_solver.
  - red; ins.
    assert (Li^? ⨾ ic ⊆ L) by apply basic_to_transitional.
    apply H0; eexists; splits; eauto.
Qed.

Lemma L_doma : doma L RW.
Proof. rewrite L_is_ic; apply ic_doma. Qed.
Lemma L_domb : domb L RW.
Proof. rewrite L_is_ic; apply ic_domb. Qed.
Lemma Li_doma : doma Li RW.
Proof. rewrite Li_is_ii; apply ii_doma. Qed.
Lemma Li_domb : domb Li RW.
Proof. rewrite Li_is_ii; apply ii_domb. Qed.

Hint Resolve L_doma L_domb Li_doma Li_domb : domains.


Lemma L_in_ppo : ⦗R⦘ ⨾ L ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  arewrite (L ⊆ ic).
  { rewrite L_in_union.
    arewrite (ii ⊆ ic).
    arewrite (ci ⊆ ic).
    arewrite (cc ⊆ ic).
    rels.
  }
  unfold Power_Model.ppo.
  by unionR right.
Qed.

Lemma L_in_ppo2 : ⦗R⦘ ⨾ Li ⊆ ppo.
Proof.
  arewrite (Li ⊆ Li ⨾ ⦗RW⦘) by domain_solver.
  unfold Power_Model.ppo.
  rewrite Li_is_ii.
  arewrite (⦗RW⦘ ⊆ ⦗R⦘ ∪ ⦗W⦘) by domain_solver.
  case_union_2 _ ⦗W⦘.
  - by unionR left.
  - unionR right.
    by arewrite (ii ⊆ ic).
Qed.

Lemma Li_in_L : Li ⊆ L.
Proof. vauto. Qed.

Lemma ppo_in_L : ppo ⊆ ⦗R⦘ ⨾ L.
Proof.
  unfold Power_Model.ppo.
  arewrite (ii ⊆ ic).
  unionL; rewrite L_is_ic; basic_solver.
Qed.

Lemma ppo_R_in_R_Li : ppo ⨾ ⦗R⦘ ⊆ ⦗R⦘ ⨾ Li.
Proof.
  arewrite (ppo ⊆ ⦗R⦘ ⨾ ppo) by domain_solver.
  red; ins.
  unfolder in *; desf.
  eexists; splits; eauto.
  unfold Power_Model.ppo in H0; unfolder in H0; desf.
  - by apply Li_is_ii.
  - type_solver.
Qed.

Lemma ppo_W_in_R_L : ppo ⨾ ⦗W⦘ ⊆ ⦗R⦘ ⨾ L.
Proof.
  arewrite (ppo ⊆ ⦗R⦘ ⨾ ppo) by domain_solver.
  red; ins.
  unfolder in *; desf.
  eexists; splits; eauto.
  unfold Power_Model.ppo in H0; unfolder in H0; desf; apply L_is_ic; vauto.
Qed.

(******************************************************************************)
(** ** Extra *)
(******************************************************************************)
Lemma rfe_rbi_in_mo CON : 
   rf∘ ⨾ rb∙ ⊆ mo.
Proof. unfolder; ins; desf; cycle_detector. Qed.

Lemma rbi_in_sb_RW CON : 
  rb∙ ⊆ sb ⨾ ⦗RW⦘.
Proof.
  arewrite (rb∙ ⊆ rb∙ ⨾ ⦗RW⦘) at 1 by domain_solver.
  by rewrite rbi_in_sb; auto.
Qed.

Lemma sync_rbi_in_sync CON : 
  sync ⨾ rb∙ ⊆ sync.
Proof.
  arewrite (rb∙ ⊆ sb ⨾ ⦗RW⦘) by apply rbi_in_sb_RW.
  unfold Power_Model.sync.
  arewrite_id ⦗RW⦘ at 2; rels.
  arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
Qed.

Lemma lwsync_rbi_in_lwsync CON : 
  lwsync ⨾ rb∙ ⊆ lwsync.
Proof.
  unfold Power_Model.lwsync, Power_Model.RW.
  rewrite id_union at 1; relsf.
  rewrite minus_union_l.
  rewrite seq_union_l.
  unionL.
  + (* starts with [R] *)
    arewrite (⦗R⦘ ⨾ sb ⨾ ⦗F_lwsync⦘ ⨾ sb ⨾ ⦗RW⦘ \ W✕R ⊆ 
                                      ⦗R⦘ ⨾ sb ⨾ ⦗F_lwsync⦘ ⨾ sb ⨾ ⦗RW⦘).
    { unfolder; ins; desf; splits.
      - eexists; splits; auto; try type_solver.
        exists z0; splits; auto.
        exists z0; splits; auto; try type_solver.
        cdes WF; cdes WF_SB; apply SB_T with z2; auto.
        apply rbi_in_sb; unfolder; auto.
      - red; ins; desf; type_solver.
    }
  + (* starts with [W] *)
    arewrite ((⦗W⦘ ⨾ sb ⨾ ⦗F_lwsync⦘ ⨾ sb ⨾ ⦗RW⦘ \ W✕R) ⊆ ⦗W⦘ ⨾ sb ⨾ ⦗F_lwsync⦘ ⨾ sb ⨾ ⦗W⦘).
    { unfolder; ins; desf.
      repeat (eexists; splits; eauto).
      unfold Power_Model.RW, set_union in H4.
      intuition. }
    arewrite (rb∙ ⊆ ⦗R⦘ ⨾ rb∙) by domain_solver.
    type_solver.
Qed.

Lemma fence_rbi_in_fence CON : 
  fence ⨾ rb∙ ⊆ fence.
Proof.
  unfold Power_Model.fence; relsf; unionL.
  - (* sync *) by unionR left; apply sync_rbi_in_sync.
  - (* lwsync *) by unionR right; apply lwsync_rbi_in_lwsync.
Qed.

Lemma lwsync_in_RW_sb_RW : lwsync ⊆ ⦗RW⦘ ⨾ sb ⨾ ⦗RW⦘.
Proof.
  unfold Power_Model.lwsync.
  rewrite inclusion_minus_rel.
  arewrite_id ⦗F_lwsync⦘.
  rels.
  arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
Qed.

Lemma sync_in_sb : sync ⊆ sb.
Proof.
  unfold Power_Model.sync; arewrite_id ⦗F_sync⦘; arewrite_id ⦗RW⦘.
  rels; arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
Qed.

Lemma lwsync_in_sb : lwsync ⊆ sb.
Proof.
  unfold Power_Model.lwsync; arewrite_id ⦗F_lwsync⦘; arewrite_id ⦗RW⦘.
  rels; rewrite inclusion_minus_rel.
  arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
Qed.

Lemma fence_in_sb : fence ⊆ sb.
Proof.
  unfold Power_Model.fence.
  arewrite (sync ⊆ sb) by apply sync_in_sb.
  arewrite (lwsync ⊆ sb) by apply lwsync_in_sb.
  eauto with rel.
Qed.

Lemma fence_sbW_in_fence : fence ⨾ sb ⨾ ⦗W⦘ ⊆ fence ⨾ ⦗W⦘.
Proof.
  unfold Power_Model.fence.
  relsf.
  repeat apply inclusion_union_l.
  - apply inclusion_union_r; left.
    unfold Power_Model.sync.
    arewrite_id ⦗RW⦘ at 2; rels.
    arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
    arewrite (⦗W⦘ ⊆ ⦗RW⦘ ⨾ ⦗W⦘) at 1.
      by (unfold Power_Model.RW; rewrite id_union; relsf).
    done.
  - apply inclusion_union_r; right.
    unfold Power_Model.lwsync.
    rewrite inclusion_minus_rel at 1.
    arewrite_id ⦗RW⦘ at 2; rels.
    arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
    unfolder; ins; desf.
    repeat (eexists; splits; eauto);
    unfold Power_Model.RW, set_union in *; auto.
    red; ins; desf; type_solver.
Qed.

Lemma RW_sb_sync_in_sync : ⦗RW⦘ ⨾ sb ⨾ sync ⊆ sync.
Proof.
  unfold Power_Model.sync.
  arewrite_id ⦗RW⦘ at 2; rels.
  arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
Qed.

Lemma ends_with_W (r : relation event) : r ⨾ ⦗W⦘ ⊆ r \ W✕R.
Proof.
  unfolder; ins; desf; splits; auto.
  red; ins; desf; type_solver.
Qed.

Lemma RW_sb_lwsync_in_lwsync : ⦗RW⦘ ⨾ sb ⨾ lwsync ⨾ ⦗W⦘ ⊆ lwsync.
Proof.
  unfold Power_Model.lwsync.
  rewrite inclusion_minus_rel at 1.
  arewrite_id ⦗RW⦘ at 2; rels.
  arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
  rewrite <- !seqA.
  remember ((((⦗RW⦘ ⨾ sb) ⨾ ⦗F_lwsync⦘) ⨾ sb) ⨾ ⦗RW⦘) as r.
  rewrite ends_with_W.
  basic_solver.
Qed.

Lemma RW_sb_fence_in_fence : ⦗RW⦘ ⨾ sb ⨾ fence ⨾ ⦗W⦘ ⊆ fence.
Proof.
  unfold Power_Model.fence.
  relsf.
  unionL.
  - sin_rewrite RW_sb_sync_in_sync; auto; basic_solver.
  - sin_rewrite RW_sb_lwsync_in_lwsync; auto; basic_solver.
Qed.

Lemma eco_refl : eco^? ⊆ ((mo ∪ rb∘)^? ⨾ rf^?) ∪ rb∙ ⨾ rf∙^? ∪ rb∙ ⨾ rf∘.
Proof.
  unfold Power_Model.eco.
  rewrite internal_or_external with (r:=rb) at 1.
  rewrite crE.
  relsf.
  unionL; try (unionR left; basic_solver 10).
  - (* rb∙ ; rf? *)
    rewrite internal_or_external with (r:=rf) at 1.
    rewrite cr_union_l; relsf; unionL;
    (by (unionR left -> right) + by (unionR right)).
Qed.

Lemma internal_in_RW_sb CON (r: relation event) : 
  (r = mo) \/ (r = rb) \/ (r = rf) -> r∙ ⊆ ⦗RW⦘ ⨾ sb.
Proof.
  unfolder; ins; desf; eexists; splits; eauto;
  try type_solver; cycle_detector.
Qed.

Lemma ecoi_in_sb CON : eco∙ ⊆ sb.
Proof.
  unfold Power_Model.eco.
  repeat rewrite inter_union_l.
  unionL.
  - eapply internal_in_sb; eauto.
  - rewrite crE; relsf; repeat rewrite inter_union_l; unionL.
    + eapply internal_in_sb; eauto.
    + unfolder; ins; desf; cycle_detector.
  - rewrite crE; relsf; repeat rewrite inter_union_l; unionL.
    + eapply internal_in_sb; eauto.
    + unfolder; ins; desf; cycle_detector.
Qed.

Lemma RW_sb_F_sb_W_in_fence : 
  ⦗RW⦘ ⨾ sb ⨾ ⦗F⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ fence.
Proof.
  setoid_rewrite id_union at 2.
  relsf; unionL.
  - (* sync *)
    arewrite (⦗W⦘ ⊆ ⦗RW⦘) by domain_solver.
    by unionR left.
  - (* lwsync *)
    arewrite (⦗W⦘ ⊆ ⦗RW⦘ ⨾ ⦗W⦘) by domain_solver.
    rewrite <- !seqA.
    remember ((((⦗RW⦘ ⨾ sb) ⨾ ⦗F_lwsync⦘) ⨾ sb) ⨾ ⦗RW⦘) as r.
    rewrite ends_with_W.
    by subst; unionR right; rewrite !seqA.
Qed.

Lemma rmw_in_ic : rmw ⊆ ic.
Proof.
  arewrite (rmw ⊆ data ∪ addr ⨾ ⦗RW⦘ ∪ ctrl ⨾ ⦗RW⦘).
  { arewrite (rmw ⊆ rmw ⨾ ⦗RW⦘) by domain_solver.
    arewrite (rmw ⊆ data ∪ addr ∪ ctrl) by (by unfold_wf).
    basic_solver 42. }
  unfolder; ins; desf; apply CC, CC0; red; basic_solver 42.
Qed.

Lemma rmw_sb_in_ic : rmw ⨾ sb ⨾ ⦗W⦘ ⊆ ic.
Proof.
  arewrite (rmw ⨾ sb ⊆ ctrl) by (by unfold_wf).
  unfolder; ins; desf; apply CC, CC0; red.
  unfolder; left; right. repeat (eexists; splits; eauto).
  type_solver.
Qed.

Lemma rmw_sb_W_in_ppo : rmw ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  unionR right.
  arewrite (rmw ⊆ ⦗R⦘ ⨾ rmw) by domain_solver.
  rewrite crE; relsf; unionL.
  - by arewrite (rmw ⊆ ic) by apply rmw_in_ic.
  - rewrite <- seq_eqvK with (dom := W) at 1.
    by arewrite (rmw ⨾ sb ⨾ ⦗W⦘ ⊆ ic) by apply rmw_sb_in_ic.
Qed.

Lemma R_sb_F_sb_RW_in_fence : ⦗R⦘ ⨾ sb ⨾ ⦗F⦘ ⨾ sb ⨾ ⦗RW⦘ ⊆ fence.
Proof.
  unfolder; ins; desf.
  red. unfolder.
  red in H4; unfold set_union in H4; desf;
  (left + right); red; unfold eqv_rel, seq;
  repeat eexists; splits; eauto; try type_solver;
  red; ins; desf; type_solver.
Qed.

Lemma rmw_in_cc : rmw ⊆ cc.
Proof.
  arewrite (rmw ⊆ rmw ⨾ ⦗RW⦘) by domain_solver.
  arewrite (rmw ⊆ data ∪ addr ∪ ctrl) by unfold_wf.
  unionL; red; ins; unfolder in H; desf; apply CC0; red; basic_solver 42.
Qed.

Lemma rmw_in_ppo : rmw ⊆ ppo.
Proof.
  arewrite (rmw ⊆ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘) by domain_solver.
  unfold Power_Model.ppo; unionR right.
  hahn_frame.
  rewrite rmw_in_cc.
  red; ins; vauto.
Qed.

Lemma rmw_in_ppo_W : rmw ⊆ ppo ⨾ ⦗W⦘.
Proof.
  arewrite (rmw ⊆ rmw ⨾ ⦗W⦘) by domain_solver.
  hahn_frame; apply rmw_in_ppo.
Qed.

Lemma rmw_sb_RW_in_cc : rmw ⨾ sb ⨾ ⦗RW⦘ ⊆ ic.
Proof.
  arewrite (rmw ⨾ sb ⊆ ctrl) by unfold_wf.
  by red; ins; apply CC, CC0; red; left; right.
Qed.

Lemma rmw_in_sb : rmw ⊆ sb.
Proof.
  arewrite (rmw ⊆ sb|imm) by unfold_wf.
  eauto with rel.
Qed.

Lemma rfi_rmw_in_sb CON : rf∙ ⨾ rmw ⊆ sb.
Proof.
  arewrite (rf∙ ⊆ sb) by eapply internal_in_sb; eauto.
  rewrite rmw_in_sb.
  eauto with rel_full.
Qed.

Lemma rmw_rfi_ppo_W_in_ppo CON : rmw ⨾ rf∙ ⨾ ppo ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  arewrite (rmw ⊆  ⦗R⦘ ⨾ rmw) by domain_solver.
  rewrite ppo_in_sb at 1; auto.
  arewrite (rf∙ ⊆ sb) by eapply internal_in_sb; eauto.
  arewrite (sb ⨾ sb ⊆ sb).
  arewrite (⦗W⦘ ⊆ ⦗W⦘ ⨾ ⦗W⦘) by rewrite seq_eqvK.
  sin_rewrite rmw_sb_in_ic; unfold Power_Model.ppo; eauto with rel.
Qed.

Lemma rmw_in_st CON : rmw ⊆ same_thread.
Proof.
  arewrite (rmw ⊆ ⦗R⦘ ⨾ rmw) by domain_solver.
  rewrite rmw_in_sb.
  unfolder; ins; desf.
  thread_solver.
Qed.

Lemma rfi_rmw_t_internal CON : (rf∙ ⨾ rmw)⁺ ⊆ (rf∙ ⨾ rmw)⁺∙.
Proof.
  apply inclusion_t_ind_left.
  - unfolder; ins; desf; split.
    + vauto.
    + apply st_trans with z; auto.
      by apply rmw_in_st.
  - unfolder; ins; desf; split.
    + apply t_trans with z0; vauto.
    + apply st_trans with z; auto.
      apply st_trans with z0; auto.
      by apply rmw_in_st.
Qed.

Lemma rf_rmw_external CON : 
  ((rf ⨾ rmw)⁺ ⨾ rf)∘ ⊆
    ((rf∙ ⨾ rmw)＊ ⨾ (rf∘ ⨾ rmw) ⨾ (rf ⨾ rmw)＊ ⨾ rf) ∪
    ((rf∙ ⨾ rmw)⁺ ⨾ rf∘).
Proof.
  rewrite internal_or_external with (r := rf) at 1.
  rewrite seq_union_l, path_ut_first, seq_union_l.
  rewrite minus_union_l.
  unionL.
  - unionR right.
    rewrite rfi_rmw_t_internal at 1; auto.
    unfolder; ins; desf.
    eexists; splits; eauto.
    red; ins; thread_producer; contradiction.
  - unionR left.
    rewrite <- seq_union_l, <- internal_or_external, !seqA.
    apply inclusion_minus_rel.
Qed.

Lemma rmw_ctrli : rmw^? ⨾ ctrl_isync ⊆ ctrl_isync.
Proof.
  arewrite (rmw ≡ rmw ⨾ ⦗W⦘) by domain_solver.
  arewrite (ctrl_isync ≡ ⦗R⦘ ⨾ ctrl_isync) at 1 by domain_solver.
  type_solver.
Qed.

Lemma ctrli_RW_in_hb : ctrl_isync ⨾ ⦗RW⦘ ⊆ hb.
Proof.
  arewrite (ctrl_isync ≡ ⦗R⦘ ⨾ ctrl_isync) at 1 by domain_solver.
  unfold Power_Model.RW, Power_Model.hb.
  unionR left -> left.
  rewrite id_union.
  case_union_2 _ _.
  - rewrite <- seq_eqvK at 2.
    arewrite (ctrl_isync ⨾ ⦗R⦘ ⊆ ii) by
      red; ins; apply CI, CI0; red; left; firstorder.
    eauto with rel.
  - rewrite <- seq_eqvK with (dom := W).
    arewrite (ctrl_isync ⨾ ⦗W⦘ ⊆ ic) by
      arewrite (⦗W⦘ ⊆ ⦗RW⦘); red; ins; apply II, CI, CI0; red; left; firstorder.
    eauto with rel.
Qed.

Lemma ctrli_types : ctrl_isync ⊆ ctrl_isync ⨾ ⦗F⦘ ∪ ctrl_isync ⨾ ⦗RW⦘.
Proof.
  unfolder; ins; desf; splits; auto.
  assert (sb x y) by by unfold_wf; apply CTRLI_IN_SB.
  assert (E y) by act_solver.
  type_solver.
Qed.

Lemma sb_types : sb ⊆ sb ⨾ ⦗F⦘ ∪ sb ⨾ ⦗RW⦘.
Proof.
  unfolder; ins; desf; splits; auto.
  assert (E y) by act_solver.
  type_solver.
Qed.

Lemma rfe_hb_rt : rf∘ ⨾ hb＊ ⊆ rf∘ ⨾ hb＊ ⨾ ⦗RW⦘.
Proof.
  case_rt _; 
  [arewrite (rf∘ ⊆ rf∘ ⨾ ⦗RW⦘) at 1 by domain_solver |
   (arewrite (hb ⊆ hb ⨾ ⦗RW⦘) at 1 by domain_solver);
   rewrite inclusion_ct_seq_eqv_r]; eauto with rel rel_full.
Qed.

Lemma rf_rmw_rt_rf CON : ((rf ⨾ rmw)＊ ⨾ rf)∘ ⊆ sb^? ⨾ rf∘ ⨾ (rmw ⨾ rf)＊.
Proof.
  rewrite rtE; relsf; rewrite !minus_union_l; unionL; [basic_solver 42|].
  rewrite rf_rmw_external; eauto with rel; unionL.
  - arewrite ((rf∙ ⨾ rmw)＊ ⊆ sb^?) at 1.
    { arewrite (rf∙ ⊆ sb) by eapply internal_in_sb; eauto.
      arewrite (rmw ⊆ sb) by red; ins; unfold_wf; apply RMW_IMM.
      unfold_wf; relsf. }
    hahn_frame.
    rewrite <- clos_trans_rotl.
    basic_solver 42.
  - arewrite ((rf∙ ⨾ rmw)⁺ ⊆ sb^?) at 1 by rewrite rfi_rmw_in_sb.
    basic_solver 42.
Qed.

Lemma rmw_rf_ct CON : (rmw ⨾ rf)⁺ ⊆ (ppo ⨾ ⦗W⦘ ∪ rf∘)⁺ ⨾ rf.
Proof.
  apply inclusion_t_ind_left.
  - hahn_frame.
    arewrite (rmw ⊆ rmw ⨾ ⦗W⦘) by domain_solver.
    assert (RMW_IN_PPO := rmw_in_ppo).
    eauto with rel.
  - rewrite ct_begin; hahn_frame.
    rewrite internal_or_external with (r := rf) at 1; relsf; unionL.
    + rewrite <- seq_eqvK at 1; rewrite !seqA.
      sin_rewrite rmw_rfi_ppo_W_in_ppo; eauto with rel.
    + arewrite (rf∙ ⊆ rf); arewrite (rf∘ ⊆ rf) at 1.
      sin_rewrite rf_rf; rels.
    + rewrite rmw_in_ppo_W; eauto with rel.
      unionR left; hahn_frame.
      remember (ppo ⨾ ⦗W⦘ ∪ rf∘) as r.
      arewrite (rf∘ ⊆ r) at 1 by subst.
      arewrite (ppo ⨾ ⦗W⦘ ⊆ r) by subst.
      rewrite <- ct_begin; eauto with rel rel_full.
    + arewrite (rf∘ ⊆ rf) at 1; arewrite (rf∘ ⊆ rf) at 1.
      sin_rewrite rf_rf; rels.
Qed.

Lemma rmw_rf_rt_1 CON : (rmw ⨾ rf)＊ ⊆ hb＊ ⨾ rf∙^?.
Proof.
  case_rt _; [eauto with rel rel_full|].
  rewrite (rmw_rf_ct CON).
  rewrite internal_or_external with (r := rf) at 2.
  arewrite (ppo ⨾ ⦗W⦘ ⊆ hb).
  case_union_2 _ _.
  + arewrite (rf∘ ⊆ hb); relsf.
  + arewrite ((hb ∪ rf∘)⁺ ⨾ rf∘ ⊆ (hb ∪ rf∘)⁺).
    arewrite (rf∘ ⊆ hb); eauto with rel rel_full.
Qed.

Lemma rmw_sb_ct : (rmw ⨾ sb)⁺ ⊆ rmw ⨾ sb.
Proof.
  rewrite ct_begin; hahn_frame; rewrite rmw_in_sb; unfold_wf; relsf.
Qed.

Lemma rmw_sb_rt : (rmw ⨾ sb)＊ ⊆ (rmw ⨾ sb)^?.
Proof. case_rt _; rewrite ?rmw_sb_ct; eauto with rel. Qed.

Lemma rmw_sb_trans: transitive (rmw ⨾ sb).
Proof.
  apply transitiveI; unfold_wf.
  arewrite (rmw ⊆ sb) at 2 by rewrite RMW_IMM; eauto with rel.
  relsf.
Qed.

Lemma rmw_rf_rt CON :
  (rmw ⨾ rf)＊ ⊆
  (rmw ⨾ rf∘)＊ ⨾ (rmw ⨾ sb ⨾ (rmw ⨾ rf∘)⁺)＊ ⨾ (rmw ⨾ sb)^?.
Proof.
  rewrite internal_or_external with (r := rf) at 1.
  rewrite seq_union_r, unionC.
  arewrite (rf∙ ⊆ sb) at 1 by eapply internal_in_sb; eauto.
  rewrite path_ut; [|apply rmw_sb_trans].
  by rewrite !seqA.
Qed.

Lemma rmw_in_hb : rmw ⊆ hb.
Proof. rewrite rmw_in_ppo; eauto with rel. Qed.

Lemma rmw_rfe_ct: (rmw ⨾ rf∘)⁺ ⊆ hb⁺ ⨾ ⦗R⦘.
Proof.
  arewrite (rf∘ ⊆ rf∘ ⨾ ⦗R⦘) at 1 by domain_solver.
  rewrite <- seqA, inclusion_ct_seq_eqv_r; hahn_frame.
  arewrite (rmw ⊆ hb) by apply rmw_in_hb.
  arewrite (rf∘ ⊆ hb).
  eauto with rel rel_full.
Qed.

Lemma rmw_sb_rmw_in_hb: rmw ⨾ sb ⨾ rmw ⊆ hb.
Proof.
  arewrite (rmw ⊆ rmw ⨾ ⦗W⦘) at 2 by domain_solver.
  unfold_wf.
  arewrite (rmw ⊆ sb) at 2 by rewrite RMW_IMM; eauto with rel.
  relsf.
  arewrite (sb ⊆ sb^?); rewrite rmw_sb_W_in_ppo; vauto.
Qed.

Lemma rmw_sb_rmw_rfe_ct : rmw ⨾ sb ⨾ (rmw ⨾ rf∘)⁺ ⊆ hb⁺ ⨾ ⦗R⦘.
Proof.
  arewrite (rf∘ ⊆ rf∘ ⨾ ⦗R⦘) at 1 by domain_solver.
  rewrite <- !seqA, inclusion_ct_seq_eqv_r, !seqA.
  hahn_frame.
  rewrite ct_begin, seqA; sin_rewrite rmw_sb_rmw_in_hb.
  arewrite (rmw ⊆ hb) by apply rmw_in_hb.
  arewrite (rf∘ ⊆ hb); arewrite (hb ⊆ hb^?) at 2.
  rewrite <- crt_double; eauto with rel rel_full.
Qed.

Lemma rmw_sb_rmw_rfe_ct_rt : (rmw ⨾ sb ⨾ (rmw ⨾ rf∘)⁺)⁺ ⊆ hb⁺ ⨾ ⦗R⦘.
Proof.
  rewrite rmw_sb_rmw_rfe_ct, inclusion_ct_seq_eqv_r; eauto with rel rel_full.
Qed.

Lemma R_rmw_rf_rt CON : ⦗R⦘ ⨾ (rmw ⨾ rf)＊ ⊆ hb＊ ⨾  ⦗R⦘ ⨾ (rmw ⨾ sb)^?.
Proof.
  rewrite (rmw_rf_rt CON); hahn_frame.
  case_rt _; case_rt _; rewrite ?rmw_sb_rmw_rfe_ct_rt, ?rmw_rfe_ct;
  hahn_frame; eauto with rel rel_full.
Qed.

Lemma ctrl_ctrli_in_ii: ctrl ⨾ ctrl_isync ⨾ ⦗RW⦘ ⊆ ii.
Proof.
  arewrite (ctrl_isync ⊆ ⦗RW⦘ ⨾ ctrl_isync) by domain_solver.
  unfolder; ins; desf.
  apply CI, CC_CI with z; by 
    (apply CC0 + apply CI0); red; left; try right; unfolder; split.
Qed.

Lemma rmw_sb_ctrli_RW_in_hb: rmw ⨾ sb ⨾ ctrl_isync ⨾ ⦗RW⦘ ⊆ hb.
Proof.
  arewrite (rmw ⨾ sb ⊆ ctrl) by unfold_wf.
  arewrite (ctrl ⊆ ⦗R⦘ ⨾ ctrl) by domain_solver.
  arewrite (⦗RW⦘ ⊆ ⦗RW⦘ ⨾ ⦗RW⦘) by rewrite seq_eqvK.
  sin_rewrite ctrl_ctrli_in_ii.
  unfold Power_Model.RW.
  rewrite id_union; case_union_2 _ _.
  - by unionR left -> left -> left.
  - unionR left -> left -> right; hahn_frame.
    red; ins; vauto.
Qed.

Lemma rmw_in_sbloc : rmw ⊆ sb|loc.
Proof.
  red; ins; red; split.
  - by unfold_wf; apply RMW_IMM.
  - red; split; clear - WF H; loc_solver.
Qed.

Lemma rf_rmw_in_mo CON : rf ⨾ rmw ⊆ mo.
Proof.
  unfold_wf; clear - WF CON MO_TOT.
  unfolder; ins; desf.
  assert (Wx: W x) by type_solver; assert (Wy: W y) by type_solver.
  assert (Ex: E x) by act_solver; assert (Ey: E y) by act_solver.
  assert (LOC: loc lab x = loc lab y) by loc_solver.
  assert (exists l, loc lab x = Some l).
  { apply not_none_implies_some; unfold loc in *.
    repeat autounfold with type_unfold in *.
    repeat autounfold with basic_type_unfold in *.
    desf. }
  apply rmw_in_sbloc in H0.
  assert (mo x y \/ mo y x) by cycle_detector.
  assert (~ mo y x) by (red; ins; cycle_detector0 x y).
  desf.
Qed.

Lemma rf_rmw_ct_in_mo CON : (rf ⨾ rmw)⁺ ⊆ mo.
Proof. by rewrite rf_rmw_in_mo, (ct_of_trans mo_trans). Qed.

Lemma rf_rmw_rt_in_mo CON : (rf ⨾ rmw)＊ ⊆ mo^?.
Proof. by rewrite rf_rmw_in_mo, (rt_of_trans mo_trans). Qed.

End Power_Helpers.

(* Export Hints *)
Hint Resolve ii_doma ic_doma ci_doma cc_doma ii_domb ic_domb ci_domb cc_domb
  ii0_doma ci0_doma cc0_doma ii0_domb ci0_domb cc0_domb
: domains.

Hint Resolve ci_in_ii ci_in_ic ii_in_ic ci_in_cc cc_in_ic icci_in_ii iiii_in_ii
  iccc_in_ic iiic_in_ic ciii_in_ci ccci_in_ci ciii_in_ci cccc_in_cc
  ppo_components_in_sb psbloc_in_sb ppo_in_sb rdw_in_ppo deps_in_sb 
  addrsb_in_sb rfi_in_ii detour_in_ii data_in_Rii data_in_iiW data_in_RiiW 
  addr_in_Rii ctrl_in_Rcc depsW_in_ppo addrsbW_in_ppo depsUaddrsbW_in_ppo
  rfe_rbi_in_mo rbi_in_sb_RW sync_rbi_in_sync lwsync_rbi_in_lwsync 
  fence_rbi_in_fence lwsync_in_RW_sb_RW sync_in_sb lwsync_in_sb fence_in_sb
  internal_in_sb internal_in_RW_sb RW_sb_F_sb_W_in_fence rmw_in_ic rmw_sb_in_ic
  rmw_sb_W_in_ppo rmw_in_cc rmw_in_ppo rmw_in_ppo_W rmw_sb_RW_in_cc rmw_in_sb
  rfi_rmw_in_sb rmw_rfi_ppo_W_in_ppo ecoi_in_sb
: rel_full.

Hint Resolve sb_trans mo_trans irrefl_trans ii_trans same_loc_trans psbloc_trans
: rel_full.

Hint Resolve eco_irr : irreflexiveDb.
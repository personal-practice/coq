(******************************************************************************)
(** * Compilation correctness of the Power memory model. *)
(******************************************************************************)
Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic.
Require Import Power_Events Power_Model Power_Domains Power_Locations
  Power_Automation Power_Irreflexive Power_Threads Power_Helpers
  Power_Additional_Properties Power_Executions.
Require Import RC11_Events RC11_Model RC11_PSC.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Power_Compilation.

Variables G : execution.
Variables Gp : power_execution.

(* RC11 notation *)
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'valr'" := (valr lab).
Notation "'valw'" := (valw lab).
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

Notation "'F_not_sc'" := (F ∩₁ (set_compl Sc)).

(* Power notation *)
Notation "'acts`'" := Gp.(Power_Model.acts).
Notation "'lab`'" := Gp.(Power_Model.lab).
Notation "'loc`'" := (Power_Events.loc lab`).
Notation "'val`'" := (Power_Events.val lab`).
Notation "'sb`'" := Gp.(Power_Model.sb).
Notation "'rf`'" := Gp.(Power_Model.rf).
Notation "'mo`'" := Gp.(Power_Model.mo).
Notation "'rmw`'" := Gp.(Power_Model.rmw).
Notation "'rb`'" := Gp.(Power_Model.rb).
Notation "'data`'" := Gp.(Power_Model.data).
Notation "'addr`'" := Gp.(Power_Model.addr).
Notation "'ctrl`'" := Gp.(Power_Model.ctrl).
Notation "'ctrli`'" := Gp.(Power_Model.ctrl_isync).
Notation "'hb`'" := Gp.(Power_Model.hb).
Notation "'sync`'" := Gp.(sync).
Notation "'fence`'" := Gp.(Power_Model.fence).
Notation "'eco`'" := Gp.(Power_Model.eco).
Notation "'same_loc`'" := Gp.(Power_Model.same_loc).
Notation "rel |loc`" := (rel ∩ same_loc`) (at level 1).

Notation "'ii`'" := Gp.(Power_Model.ii).
Notation "'ic`'" := Gp.(Power_Model.ic).
Notation "'ci`'" := Gp.(Power_Model.ci).
Notation "'cc`'" := Gp.(Power_Model.cc).
Notation "'ppo`'" := Gp.(Power_Model.ppo).

Notation "'Wf`'" := Gp.(Power_Model.Wf).
Notation "'init_label`'" := (Power_Events.init_label).

Notation "'E`'" := Gp.(Power_Model.E).
Notation "'F`'" := Gp.(Power_Model.F).
Notation "'R`'" := Gp.(Power_Model.R).
Notation "'W`'" := Gp.(Power_Model.W).
Notation "'RW`'" := Gp.(Power_Model.RW).
Notation "'F_sy`'" := Gp.(Power_Model.F_sync).
Notation "'F_lw`'" := Gp.(Power_Model.F_lwsync).

Notation "'S'" := Gp.(S).

(* Lemma H.1 *)
Definition compile_lab label :=
  match label with
  | Astore l v _ => Power_Events.Astore l v
  | Aload l v _ => Power_Events.Aload l v
  | Afence Fsc => Power_Events.Afence_sync
  | Afence _ => Power_Events.Afence_lwsync
  | (* BOGUS *) Armw _ _ _ _ => Power_Events.Afence_lwsync
  end.

Hypothesis NRMW : NO_RMW_EVENTS G.
Hypothesis NO_W_REL : W∩₁Rel ≡₁ ∅₁.
Hypothesis SB       : sb` ≡ sb.
Hypothesis RF       : rf` ≡ rf.
Hypothesis MO       : mo` ≡ mo.
Hypothesis Rmw      : rmw` ≡ rmw.
Hypothesis NO_SC    : RW∩₁Sc ≡₁ ∅₁.
Hypothesis DATA     : data` ≡ data.
Hypothesis ADDR     : addr` ≡ addr.
Hypothesis CTRL     : ctrl ⊆ ctrl`.
Hypothesis CTRL_SB  : ctrl ⨾ sb ⊆ ctrl.
Hypothesis RMW_DEPS : rmw ⊆ deps.
Hypothesis RMW_SB   : rmw ⨾ sb ⊆ ctrl`.
Hypothesis R_ACQ_SB : (⦗R∩₁Acq⦘ ⨾ sb) ⊆ rmw` ∪ ctrli`.
Hypothesis ACTS     : acts` = acts.
Hypothesis LAB      : forall a, lab` a = compile_lab (lab a).

Tactic Notation "unfold_types" := repeat(
  unfold set_compl, Power_Model.F in *;
  unfolder in *; type_unfolder; mode_unfolder;
  unfold set_compl, RC11_Events.mod,
    Power_Model.R, Power_Model.W, Power_Model.F_lwsync, Power_Model.F_sync,
    Power_Model.RW, is_f_sync, is_f_lwsync, Power_Events.is_r,
    Power_Events.is_w, set_union, compile_lab in *
).

Ltac fold_types := fold E R W RW F Sc Rel Acq Rlx.

Lemma TYPE_ASSUMPTIONS :
  ⟪SAME_E: E` ≡₁ E⟫ /\
  ⟪SAME_R: R` ≡₁ R⟫ /\
  ⟪SAME_W: W` ≡₁ W⟫ /\
  ⟪F_LW: F_lw` ≡₁ F_not_sc⟫ /\
  ⟪F_SY: F_sy` ≡₁ F∩₁Sc⟫ /\
  ⟪F_ALL: F` ≡₁ F⟫ /\
  ⟪R_ACQ_IN_R: R∩₁Acq ⊆₁ R`⟫.
Proof.
  splits; only 1: (by unfold RC11_Model.E, Power_Model.E; rewrite ACTS).
  all: try (red; ins; red; split).
  all: try red; splits; ins; specialize (LAB x); specialize (NRMW x);
       unfold_types; desf; intuition.
Qed.

Lemma SAME_LOC : loc` = loc.
Proof.
  unfold RC11_Events.loc, Power_Events.loc.
  exten; ins; specialize (LAB x); specialize (NRMW x).
  unfold_types; rewrite LAB; destruct (lab x); desf; intuition.
Qed.

Lemma SAME_LOC' : same_loc` = same_loc.
Proof.
  assert (SL := SAME_LOC).
  unfold RC11_Model.same_loc, Power_Model.same_loc.
  by rewrite SL.
Qed.

Lemma SAME_VAL : val` = val.
Proof.
  unfold RC11_Events.val, Power_Events.val.
  exten; ins; specialize (LAB x); specialize (NRMW x).
  unfold_types; rewrite LAB; destruct (lab x); desf; intuition.
Qed.

Hypothesis CON: PowerConsistent Gp.
Hypothesis LAB_INIT: forall l, lab (Init l) = init_label l.
Hypothesis RMW_MOD: forall a b (RMW_AB: rmw a b),
      (Rlx a /\ Rlx b) \/ (Acq a /\ Rlx b) \/ (Rlx a /\ Rel b) \/ (Acq a /\ Rel b) \/ (Sc a /\ Sc b).

Tactic Notation "cassert" uconstr(H) :=
  let ID := fresh in try (assert (ID := H); crewrite ID).

Ltac oto_basic :=
  assert (_TA := TYPE_ASSUMPTIONS);
  destruct _TA as (_SE & _SR & _SW & _SF1 & _SF2 & _SF3 & _RA); unnw;
  assert (_SL := SAME_LOC);
  assert (_SV := SAME_VAL);
  crewrite ACTS; crewrite SB; crewrite RF; crewrite MO; crewrite Rmw;
  crewrite DATA; crewrite ADDR; crewrite CTRL; crewrite RMW_SB;
  crewrite _SE; crewrite _SR; crewrite _SW; crewrite _SL; crewrite _SV;
  crewrite _SF1; crewrite _SF2; crewrite _SF3.

Lemma wf_compilation : Wf G.
Proof.
  assert (TA := TYPE_ASSUMPTIONS).
  destruct TA as (SE & SR & SW & SF1 & SF2 & SF3 & RA); unnw.
  assert (SL := SAME_LOC).
  assert (SV := SAME_VAL).
  
  assert (RF_DOM: rf ⊆ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘) by by oto_basic; cdes CON; unfold_wf.
  red; splits; unnw; red; splits; unnw; auto.
  all: try by fold_types; oto_basic; cdes CON; unfold_wf.
  - ins. cdes CON; cdes WF. cdes WF_SB.
    rewrite <- SB.
    red; ins; unfolder in IWa; unfolder in IWb; desf.
    apply SE in IWa; apply SE in IWb; apply (SB_TOT i a); basic_solver.
  - apply (NRMW_implies_rf_irr NRMW RF_DOM).
  - cdes CON; cdes WF; cdes WF_RF.
    red in RF_VAL.
    ins; apply RF in H. specialize (RF_VAL a b H).
    unfold Power_Events.val in RF_VAL.
    unfold RC11_Events.valr, RC11_Events.valw.
    rewrite (LAB a) in RF_VAL.
    rewrite (LAB b) in RF_VAL.
    apply RF_DOM0 in H; unfolder in H.
    assert (Wa: W a) by (apply SW; desf).
    assert (Rb: R b) by (apply SR; desf).
    clear - NRMW RF_VAL Wa Rb.
    unfold_types; desf.
    exfalso; do 2 red in NRMW.
    apply (NRMW b); red; desf.
  - ins; apply SE in IN; apply SR in READ.
    cdes CON; cdes WF; cdes WF_RF.
    specialize (RF_TOT _ IN READ); desf.
    by exists a; apply RF.
  - cdes CON; cdes WF; cdes WF_MO.
    unfold is_total in *; ins.
    clear - MO SE SW SL MO_TOT IWa IWb NEQ.
    assert (mo` a b \/ mo` b a).
    { unfolder in IWa; unfolder in IWb; desf.
      apply SE in IWa; apply SE in IWb; apply SW in IWa1; apply SW in IWb1.
      eapply MO_TOT; eauto; desf; rewrite SL in *; splits; eauto. }
    desf; (left + right); by apply MO.
  - assert (SRW: RW` ≡₁ RW) by
      by unfold RC11_Events.RW, Power_Model.RW; rewrite SR, SW.
    cdes CON; cdes WF; cdes WF_DEPS; rewrite_cartesian_products.
    by rewrite <- ADDR, <- SR, <- SRW.
  - fold_types; cdes CON; cdes WF; cdes WF_DEPS; rewrite_cartesian_products.
    apply doma_helper; rewrite CTRL, <- SR; domain_solver.
Qed.

Ltac assert_all :=
  assert (TA := TYPE_ASSUMPTIONS);
  destruct TA as (SE & SR & SW & SF1 & SF2 & SF3 & RA); unnw;
  assert (SL := SAME_LOC);
  assert (SL' := SAME_LOC');
  assert (SV := SAME_VAL);
  assert (WF := wf_compilation);
  assert (SB_T: transitive sb`) by (by cdes CON; unfold_wf).

Lemma RB: rb` ≡ rb.
Proof.
  assert_all.
  rewrite NRMW_implies_original_rb; auto.
  by unfold Power_Model.rb; rewrite RF, MO.
Qed.

Lemma ECO: eco` ≡ eco.
Proof.
  unfold RC11_Model.eco, Power_Model.eco.
  by rewrite RF, MO, RB.
Qed.

Lemma W_SL_W: ⦗W⦘ ⨾ same_loc ⨾ ⦗W⦘ ⊆ ⦗W`⦘ ⨾ same_loc` ⨾ ⦗W`⦘.
Proof.
  assert_all; unfold RC11_Model.same_loc, Power_Model.same_loc.
  by rewrite SW, SL; hahn_frame.
Qed.

Lemma sw_transform :
  sw ⊆ ⦗F`⦘ ⨾ sb` ⨾ sb`^? ⨾ (rf` ⨾ rmw`)＊ ⨾ rf` ⨾ (⦗R∩₁Acq⦘ ∪ sb` ⨾ ⦗F`⦘).
Proof.
  assert_all.
  unfold RC11_Model.sw, release, rs.
  rewrite (NRMW_implies_original_useq WF NRMW).
  fold_types.
  rewrite <- SB, <- RF, <- SL', <- Rmw, <- SE, <- SW.
  rewrite SW at 1.
  arewrite (⦗W∩₁Rel⦘ ≡ ∅₂) by rewrite NO_W_REL; unfolder; split; ins; desf.
  arewrite (⦗F∩₁Rel⦘ ⊆ ⦗F`⦘).
  { arewrite (⦗F∩₁Rel⦘ ⊆ ⦗F⦘) by unfold_types; basic_solver.
    by rewrite SF3. }
  clear_equivs ⦗E`⦘.
  clear_equivs ⦗W`⦘.
  clear_equivs ⦗W`∩₁Rlx⦘.
  clear_equivs ⦗R∩₁Rlx⦘.
  arewrite (sb`|loc` ⊆ sb`).
  arewrite (⦗F∩₁Acq⦘ ⊆ ⦗F`⦘).
  { arewrite (⦗F∩₁Acq⦘ ⊆ ⦗F⦘) by unfold_types; basic_solver.
    by rewrite SF3. }
  rels.
  by rewrite !seqA.
Qed.

Lemma external_helper : 
  (⦗F`⦘ ⨾ sb` ⨾ sb`^? ⨾ (rf` ⨾ rmw`)＊ ⨾ rf` ⨾ (⦗R∩₁Acq⦘ ∪ sb` ⨾ ⦗F`⦘))∘
    ⊆ ⦗F`⦘ ⨾ sb` ⨾ ((rf` ⨾ rmw`)＊ ⨾ rf`)∘ ⨾ (⦗R∩₁Acq⦘ ∪ sb` ⨾ ⦗F`⦘).
Proof.
  clear - CON.
  relsf; rewrite !minus_union_l; unionL.
  - unionR left; relsf.
    unfolder; ins; desf; splits; auto.
    + eexists; splits; eauto.
      assert (same_thread x z0).
      { cdes CON; eapply sb_not_init_implies_st; eauto.
        eapply F_in_I; eauto. }
      red; ins; thread_producer; contradiction.
    + exists z0; splits; eauto.
      by cdes CON; unfold_wf; apply SB_T with z.
      assert (same_thread x z0).
      { cdes CON; eapply sb_not_init_implies_st; eauto.
        by cdes CON; unfold_wf; apply SB_T with z.
        eapply F_in_I; eauto. }
      red; ins; thread_producer; contradiction.
  - unionR right;relsf.
    unfolder; ins; desf; splits; auto.
    + exists z0; splits; auto.
      eexists; splits; eauto.
      assert (same_thread x z0).
      { cdes CON; eapply sb_not_init_implies_st; eauto.
        eapply F_in_I; eauto. }
      red; ins.
      assert (same_thread z2 y).
      { cdes CON.
        assert (R` z2).
        { clear - H4 CON WF; type_solver. }
          eapply sb_not_init_implies_st; eauto.
          eapply R_in_I; eauto. }
      thread_producer; contradiction.
    + exists z0; splits; eauto.
      by cdes CON; unfold_wf; apply SB_T with z.
      eexists; splits; eauto.
      assert (same_thread x z0).
      { cdes CON; eapply sb_not_init_implies_st; eauto.
        by cdes CON; unfold_wf; apply SB_T with z.
        eapply F_in_I; eauto. }
      red; ins.
      assert (same_thread z2 y).
      { cdes CON.
        assert (R` z2).
        { clear - H4 CON; type_solver. }
          eapply sb_not_init_implies_st; eauto.
          eapply R_in_I; eauto. }
      thread_producer; contradiction.
Qed.

Lemma sw_in_S:
  sw∘ ⊆ S.
Proof.
  assert_all; prepare_wf as WF'.
  unfold Power_Additional_Properties.S.
  rewrite sw_transform, external_helper, (rf_rmw_rt_rf WF' CON).
  apply leading_refl.
  sin_rewrite (rmw_rf_rt_1 WF' CON).
  rewrite !seqA.
  arewrite (sb` ⨾ sb`^? ⊆ sb`) by relsf.
  case_union_2 ⦗R∩₁Acq⦘ _; case_refl _.
  + (* [R_acq] *) clear; basic_solver 42.
  + (* rf∙;[R_acq] *)
    arewrite (rf` ⊆ eco`) at 2.
    clear; basic_solver 42.
  + (* sb;[F] *) clear; basic_solver 42.
  + (* rf∙;sb;[F] *)
    arewrite (rf`∙ ⊆ sb`) by relsf.
    relsf; clear; basic_solver 42.
Qed.

Lemma sw_sb_in_S:
  sw∘ ⨾ sb ⊆ S.
Proof.
  assert_all; prepare_wf as WF'.
  unfold Power_Additional_Properties.S.
  rewrite sw_transform, <- SB.
  rewrite external_helper.
  rewrite (rf_rmw_rt_rf WF' CON).
  apply leading_refl.
  arewrite (rf`∘ ⊆ rf`∘ ⨾ ⦗R`⦘) at 1 by cdes CON; domain_solver.
  sin_rewrite (R_rmw_rf_rt WF' CON).
  rewrite !seqA.
  arewrite (sb` ⨾ sb`^? ⊆ sb`) by relsf.
  case_union_2 ⦗R∩₁Acq⦘ _; case_refl _.
  1, 2: (rewrite SB at 2 + rewrite SB at 3); sin_rewrite R_ACQ_SB; case_union_2 rmw` _.
  5: rewrite (sb_types WF') at 3; case_union_2 _ _.
  7: rewrite (sb_types WF') at 4; case_union_2 _ _.
  1, 2, 3, 4, 5: clear_equivs ⦗R`⦘.
  + (* rmw *)
    rewrite (rmw_in_ppo WF').
    arewrite (ppo` ⊆ hb`).
    rewrite rt_unit; eauto with rel rel_full.
  + (* ctrli *)
    rewrite (ctrli_types WF'); case_union_2 (ctrli` ⨾ ⦗F`⦘) _.
    * arewrite (ctrli` ⊆ sb`) by unfold_wf.
      clear; basic_solver 42.
    * rewrite (ctrli_RW_in_hb WF'), rt_unit; eauto with rel rel_full.
  + (* rmw;sb;rmw *)
    rewrite (rmw_sb_rmw_in_hb WF'), rt_unit; eauto with rel rel_full.
  + (* rmw;sb;ctrli *)
    rewrite (ctrli_types WF').
    relsf; unionL.
    * (* rmw;sb;ctrli;[F] *)
      arewrite (ctrli` ⊆ sb`) by unfold_wf.
      arewrite (rmw` ⊆ sb`).
      relsf; clear; basic_solver 42.
    * (* rmw;sb;ctrli;[RW] *)
      rewrite (rmw_sb_ctrli_RW_in_hb WF'), rt_unit; eauto with rel rel_full.
  + (* sb;[F];sb;[F] *)
    arewrite_id ⦗F`⦘ at 2; relsf; clear; basic_solver 42.
  + (* sb;[F];sb;[RW] *)
    rewrite R_sb_F_sb_RW_in_fence.
    arewrite (fence` ⊆ hb`).
    rewrite rt_unit; eauto with rel rel_full.
  + (* rmw;sb;sb;[F];sb;[F] *)
    arewrite (rmw` ⊆ sb`).
    arewrite_id ⦗F`⦘ at 2; relsf.
    clear; basic_solver 42.
  + (* rmw;sb;sb;[F];sb;[RW] *)
    arewrite (rmw` ⊆ sb`); relsf.
    rewrite R_sb_F_sb_RW_in_fence; arewrite (fence` ⊆ hb`).
    rewrite rt_unit; eauto with rel rel_full.
Qed.

Lemma sw_sb_r_in_S:
  sw∘ ⨾ sb^? ⊆ S.
Proof. case_refl _; [apply sw_in_S | apply sw_sb_in_S]. Qed.

Lemma swi_in_sb : sw∙ ⊆ sb.
Proof.
  assert_all; prepare_wf as WF'.
  rewrite sw_transform.
  clear RMW_MOD LAB_INIT LAB ACTS.
  rewrite <- SB, (rf_rmw_rt_in_mo WF' CON).
  relsf.
  rewrite inter_union_l; unionL.
  - rewrite RA, crE; relsf; rewrite inter_union_l; unionL.
    + clear_equivs ⦗R`⦘.
      unfolder; ins; desf.
      prepare_wf as WF'; clear - WF' CON H H1 H2 H0.
      assert (sb` z y).
      { eapply internal_in_sb; eauto.
        red; split; auto.
        assert (same_thread x z)
          by (eapply sb_not_init_implies_st; eauto; type_solver).
        by thread_producer. }
      by unfold_wf; apply SB_T with z.
    + clear_equivs ⦗R`⦘.
      unfolder; ins; desf.
      prepare_wf as WF'; clear - WF' CON H H1 H2 H3 H0.
      assert (sb` z y).
      { assert (~ sb` y z) by cycle_detector.
        assert (sb` z y \/ sb` y z).
        { apply st_implies_sb; auto; try act_solver.
          - apply st_trans with x; auto.
            apply st_inv.
            eapply sb_not_init_implies_st; eauto; type_solver.
          - red; ins; desf.
            cdes CON; apply SC_PER_LOC with y.
            apply t_trans with z0.
            + by left; right.
            + by do 3 left; right.
        }
        desf. }
      by unfold_wf; apply SB_T with z.
  - rewrite crE; relsf; rewrite inter_union_l; unionL.
    + unfolder; ins; desf.
      prepare_wf as WF'; clear - WF' CON H H1 H2 H3 H0.
      assert (sb` z z0).
      { eapply internal_in_sb; eauto.
        red; split; auto.
        apply st_trans with x.
        - apply st_inv; eapply sb_not_init_implies_st; eauto; type_solver.
        - apply st_trans with y; auto.
          apply st_inv. eapply sb_not_init_implies_st; eauto.
          assert (R` z0) by type_solver.
          eapply R_in_I; eauto. }
      by unfold_wf; apply SB_T with z; auto; apply SB_T with z0.
    + unfolder; ins; desf.
      prepare_wf as WF'; clear - WF' CON H H1 H2 H3 H4 H0.
      assert (sb` z z1).
      { assert (~ sb` z1 z) by cycle_detector.
        assert (sb` z z1 \/ sb` z1 z).
        { apply st_implies_sb; auto; try act_solver.
          - apply st_trans with x; auto.
            apply st_inv.
            eapply sb_not_init_implies_st; eauto; type_solver.
            apply st_trans with y; auto.
            apply st_inv.
            eapply sb_not_init_implies_st; eauto.
            assert (R` z1) by type_solver.
            eapply R_in_I; eauto.
          - red; ins; desf.
            cdes CON; apply SC_PER_LOC with z1.
            apply t_trans with z0.
            + by left; right.
            + by do 3 left; right.
        }
        desf. }
      by unfold_wf; apply SB_T with z; auto; apply SB_T with z1.
Qed.

Lemma hb_in_sb_swe : hb ⊆ (sb ∪ sw∘)⁺.
Proof.
  unfold RC11_Model.hb.
  rewrite internal_or_external with (r := sw) at 1.
  arewrite (sw∙ ⊆ sb) at 1 by apply swi_in_sb.
  eauto with rel.
Qed.

Lemma hb_in_sb_S:
  hb ⊆ sb` ∪ S.
Proof.
  assert (WF := wf_compilation).
  rewrite hb_in_sb_swe.
  rewrite path_union.
  assert (SB_T: transitive sb) by by cdes WF; cdes WF_SB.
  assert (S_T: transitive S) by by cdes CON; apply S_trans.
  rewrite (rt_of_trans SB_T).
  rewrite (ct_of_trans SB_T).
  unionL.
  - rewrite SB; eauto with rel.
  - unionR right.
    arewrite ((sb^? ⨾ sw∘ ⨾ sb^?)⁺ ⊆ sb^? ⨾ (sw∘ ⨾ sb^?)⁺).
    { rewrite clos_trans_rotl.
      hahn_frame.
      arewrite (sb^? ⨾ sb^? ⊆ sb^?) by relsf.
      by rewrite <- ct_end. }
    cdes CON.
    rewrite sw_sb_r_in_S, (ct_of_trans S_T).
    assert (SB_T': transitive sb`) by by cdes CON; unfold_wf.
    unfold Power_Additional_Properties.S.
    rewrite <- SB.
    arewrite (sb`^? ⨾ sb`^? ⊆ sb`^?) by relsf.
Qed.

Lemma rw_sb_hb :
  ⦗RW⦘ ⨾ (sb \ rmw) ⨾ hb^? ⊆ sb` ∪ fence` ⨾ hb`＊ ⨾ (sb` ⨾ ⦗F`⦘ ∪ eco`∙)^?.
Proof.
  assert_all.
  case_refl hb.
  - rewrite inclusion_minus_rel, SB.
    clear_equivs ⦗RW⦘.
    by unionR left.
  - rewrite hb_in_sb_S.
    case_union_2 sb` _.
    + rewrite inclusion_minus_rel, SB.
      clear_equivs ⦗RW⦘.
      unionR left.
      assert (SB_T': transitive sb) by by cdes WF; cdes WF_SB.
      relsf.
    + unionR right.
      unfold Power_Additional_Properties.S.
      cdes CON; arewrite (rf`∘ ⊆ ⦗W`⦘ ⨾ rf`∘) by domain_solver.
      arewrite (rf`∘ ⊆ hb`) by unfold Power_Model.hb; eauto with rel.
      hahn_frame.
      relsf.
      arewrite (⦗RW⦘ ⨾ (sb \ rmw) ⨾ sb`^? ⨾ ⦗F`⦘ ⨾ sb` ⨾ ⦗W`⦘ ⊆ fence`).
      { rewrite inclusion_minus_rel, <- SB.
        arewrite (sb` ⨾ sb`^? ⊆ sb`) by relsf.
        arewrite (RW ≡₁ RW`) by
          by unfold RC11_Events.RW, Power_Model.RW; rewrite SR, SW.
        by apply RW_sb_F_sb_W_in_fence. }
      eauto with rel rel_full.
Qed.

Lemma F_hb_RW : ⦗F∩₁Sc⦘ ⨾ hb ⨾ ⦗RW⦘ ⊆ ⦗F_sy`⦘ ⨾ sb` ⨾ hb`＊ ⨾ eco`^? ⨾ ⦗RW`⦘.
Proof.
  assert_all.
  rewrite <- SF2.
  arewrite (RW ≡₁ RW`) by
    by unfold RC11_Events.RW, Power_Model.RW; rewrite SR, SW.
  rewrite hb_in_sb_S.
  case_union_2 _ _; eauto with rel rel_full.
  unfold Power_Additional_Properties.S.
  case_refl (sb` ⨾ ⦗F`⦘ ∪ eco`∙).
  - arewrite (rf`∘ ⊆ hb`) by unfold Power_Model.hb; eauto with rel.
    seq_rewrite <- ct_begin.
    basic_solver 42.
  - case_union_2 _ _.
    + clear; type_solver.
    + clear_equivs ⦗F`⦘.
      arewrite (rf`∘ ⊆ hb`) by unfold Power_Model.hb; eauto with rel.
      relsf.
      hahn_frame.
      rewrite inter_inclusion.
      seq_rewrite <- ct_begin.
      eauto with rel rel_full.
Qed.

Lemma W_sbloc_W : ⦗W⦘ ⨾ sb|loc ⨾ ⦗W⦘ ⊆ mo.
Proof.
  assert_all.
  rewrite <- SB.
  unfolder; ins; desf.
  assert ((⦗W`⦘ ⨾ same_loc` ⨾ ⦗W`⦘) x y) by (apply W_SL_W; unfolder; desf).
  unfolder in H3; desf.
  hahn_rewrite <- MO.
  prepare_wf as WF'; clear - WF' CON H2 H0 H H1 H6 H4 H5.
  cycle_detector.
Qed.

Lemma rmw_in_rb : rmw ⊆ rb.
Proof.
  assert_all.
  rewrite <- Rmw, <- RB.
  unfold Power_Model.rb.
  arewrite (rmw` ⊆ ⦗R`⦘ ⨾ rmw` ⨾ ⦗W`⦘) by domain_solver.
  unfolder; ins; desf.
  unfold_wf; clear - CON H H0 H1 RF_TOT RMW_IMM.
  assert (In x (acts`)) by act_solver.
  specialize (RF_TOT _ H2 H); desf.
  exists a; splits; auto.
  remember (loc` a) as l.
  assert (sb` x y) by by apply RMW_IMM.
  prepare_wf; cycle_detector.
Qed.

(* Coherence *)
Proposition COH: Coherent G.
Proof.
  assert_all; cdes CON.
  assert (RMW_IN_RB := rmw_in_rb).
  assert (W_SBLOC_W := W_sbloc_W).
  red; rotate; case_refl eco.
  + rewrite hb_in_sb_S.
    unionL.
    * by unfold_wf.
    * by apply sb_F_sb_spo.
  + rewrite eco_seq_hb; auto.
    apply_unionL_once.
    * rewrite <- ECO.
      by apply eco_irr.
    * arewrite (eco ⊆ eco ⨾ ⦗RW⦘) by apply domb_helper, eco_domb.
      rewrite rw_sb_hb, <- ECO.
      arewrite (eco`∙ ⊆ eco`).
      by apply eco_sb_fence_hb_eco_R_irr.
Qed.

(* Atomicity *)
Proposition ATOM: irreflexive (rb ⨾ mo ⨾ rmw⁻¹).
Proof.
  cdes CON.
  apply atomicity_equiv.
  rewrite <- RB, <- MO, <- Rmw.
  by apply rmw_atomic.
Qed.

(* SC *)
Definition R1 := ⦗F∩₁Sc⦘ ⨾ hb ⨾ eco ⨾ hb ⨾ ⦗F∩₁Sc⦘.
Definition R2 := ⦗F∩₁Sc⦘ ⨾ hb ⨾ ⦗F∩₁Sc⦘.

Lemma sc_is_f : ⦗Sc⦘ ⊆ ⦗F∩₁Sc⦘.
Proof.
  clear - NO_SC.
  unfold_types; ins; specialize (NO_SC x); desf; intuition.
Qed.

Lemma hb_t : hb⁺ ≡ hb.
Proof. apply ct_of_trans, hb_trans. Qed.

Lemma psc_no_sc : psc ⊆ R1 ∪ R2.
Proof.
  assert_all.
  rewrite psc_sc, sc_is_f; try done.
  rewrite psc_f_f; try done.
  unfold RC11_Model.psc_f, R1, R2.
  basic_solver 12.
Qed.

Lemma R2_irr: irreflexive R2.
Proof.
  unfold R2; clear_equivs ⦗F∩₁Sc⦘.
  apply irr_hb, COH.
Qed.

Lemma R2_acyc: acyclic R2.
Proof.
  red.
  unfold R2; clear_equivs ⦗F∩₁Sc⦘.
  rewrite hb_t.
  apply irr_hb, COH.
Qed.

Lemma R2_t_R1_in_R1: R2⁺ ⨾ R1 ⊆ R1.
Proof.
  unfold R1, R2; do 2 arewrite_id ⦗F∩₁Sc⦘ at 2; rels.
  rewrite inclusion_ct_seq_eqv_l, hb_t, !seqA.
  by sin_rewrite hb_hb.
Qed.

Lemma R2_R1_in_R1: R2 ⨾ R1 ⊆ R1.
Proof.
  unfold R1, R2; do 2 arewrite_id ⦗F∩₁Sc⦘ at 2; rels.
  by sin_rewrite hb_hb.
Qed.

Lemma rewrite_sc :
  eco` ⨾ (sb` ∪ fence` ⨾ hb`＊ ⨾ (sb` ⨾ ⦗F`⦘ ∪ eco`∙)^?) 
       ⨾ ⦗F_sy`⦘ ⨾ sb` ⨾ hb`＊ ⨾ eco`^? ⨾ ⦗RW`⦘ ⊆
  eco` ⨾ (fence` ⨾ hb`＊)^? ⨾ sb` ⨾ ⦗F_sy`⦘ ⨾ sb` ⨾ hb`＊ ⨾ eco`^? ⨾ ⦗RW`⦘.
Proof.
  case_union_2 sb` _.
  - eauto with rel rel_full.
  - case_refl (sb` ⨾ ⦗F`⦘ ∪ eco`∙).
    + arewrite (fence` ⨾ hb`＊ ⊆ fence` ⨾ hb`＊ ⨾ ⦗RW`⦘).
      { cdes CON; case_rt _.
        - arewrite (fence` ⊆ fence` ⨾ ⦗RW`⦘) by apply domb_helper, fence_domb.
          eauto with rel rel_full.
        - rewrite ct_end.
          arewrite (hb` ⊆ hb` ⨾ ⦗RW`⦘) at 2 by domain_solver.
          by sin_rewrite rt_unit.
      }
      type_solver.
    + case_union_2 _ _.
      * clear_equivs ⦗F`⦘. basic_solver 42.
      * assert_all.
        cdes CON; rewrite ecoi_in_sb; auto.
        basic_solver 42.
Qed.

Proposition SC: acyclic psc.
Proof.
  assert_all; cdes CON.
  assert (R2_R1 := R2_R1_in_R1).
  assert (ACYC_R2 := R2_acyc).
  assert (RMW_IN_RB := rmw_in_rb).
  assert (W_SBLOC_W := W_sbloc_W).
  rewrite psc_no_sc.
  apply acyclic_absorb; auto.
  unfold R1.
  arewrite (eco ⊆ ⦗RW⦘ ⨾ eco) by by cdes WF; apply doma_helper, eco_doma.
  rotate 3.
  sin_rewrite eco_seq_hb; auto.
  arewrite (eco ⊆ eco ⨾ ⦗RW⦘) by by cdes WF; apply domb_helper, eco_domb.
  arewrite ((eco ⨾ ⦗RW⦘ ∪ eco ⨾ ⦗RW⦘ ⨾ (sb \ rmw) ⨾ hb^?) ⨾ ⦗F∩₁Sc⦘ ⨾ ⦗F∩₁Sc⦘ ⨾ hb ⨾ ⦗RW⦘ ⊆
    eco ⨾ ⦗RW⦘ ⨾ (sb \ rmw) ⨾ hb^? ⨾ ⦗F∩₁Sc⦘ ⨾ hb ⨾ ⦗RW⦘).
  { case_union_2 _ _; [unfold_types; ins; desf | by rewrite !seqA]. }
  sin_rewrite rw_sb_hb.
  rewrite <- ECO.
  sin_rewrite F_hb_RW.
  rewrite rewrite_sc.
  arewrite (eco` ⨾ (fence` ⨾ hb`＊)^? ⊆ eco` ⨾ (fence` ⨾ hb`＊)^? ⨾ ⦗RW`⦘).
  { clear - CON; case_refl _.
    - arewrite (eco` ⊆ eco` ⨾ ⦗RW`⦘).
      { apply domb_helper.
        unfold Power_Model.eco; rewrite crE; relsf.
        assert (domb rf` RW`) by domain_solver.
        repeat simplify_domains; auto; domain_solver.
      }
      eauto with rel rel_full.
    - case_rt hb`.
      + arewrite (fence` ⊆ fence` ⨾ ⦗RW`⦘) by apply domb_helper, fence_domb.
        eauto with rel rel_full.
      + rewrite ct_end.
        arewrite (hb` ⊆ hb` ⨾ ⦗RW`⦘) at 2 by domain_solver.
        seq_rewrite <- ct_end.
        basic_solver 42.
  }
  arewrite (eco`^? ⨾ ⦗RW`⦘ ⊆ ⦗RW`⦘ ⨾ eco`^?).
  { arewrite (eco` ⊆ ⦗RW`⦘ ⨾ eco`) by domain_solver.
    case_refl _; basic_solver. }
  rotate.
  arewrite (eco`^? ⨾ eco` ⊆ eco`)
    by apply rewrite_trans_seq_cr_l, Power_Helpers.eco_trans.
  arewrite (hb`＊ ⨾ ⦗RW`⦘ ⊆ ⦗RW`⦘ ⨾ hb`＊).
  { case_rt hb`.
    - eauto with rel rel_full.
    - rewrite ct_begin.
      arewrite (hb` ⊆ ⦗RW`⦘ ⨾ hb`) at 1 by unfold Power_Model.hb; domain_solver.
      seq_rewrite <- ct_begin.
      basic_solver 42.
  }
  arewrite (eco` ⨾ (fence` ⨾ hb`＊)^? ⨾ ⦗RW`⦘ ⨾ sb` ⨾ ⦗F_sy`⦘ ⨾ sb` ⨾ ⦗RW`⦘ ⨾ hb`＊
    ⊆ eco` ⨾ (fence` ⨾ hb`＊)^? ⨾ sync` ⨾ hb`＊).
  { hahn_frame.
    unfold Power_Model.sync.
    basic_solver 42. }
  prepare_wf as WF'; clear - WF' CON.
  arewrite (eco` ⊆ eco`^?).
  by apply eco_fench_hb_acyclic.
Qed.

Proposition power_to_rc11 : wconsistent G.
Proof.
  assert_all; cdes CON.
  red; splits; auto.
  - (* Coherence *) apply COH.
  - (* Atomicity *) apply ATOM.
  - (* Atomicity2 *) by apply NRMW_implies_atomic2.
  - (* SC *) apply SC.
Qed.

End Power_Compilation.

(* Outcome *)
(* Notation "'mo_loc'" := G.(mo_loc).
Notation "'mo_loc`'" := Gp.(Power_Model.mo_loc).

Definition rc11_outcome l v :=
  exists a, (max_elt (mo_loc l) a) /\ (val a = v).
Definition power_outcome l v :=
  exists a, (max_elt (mo_loc` l) a) /\ (val` a = v).

Lemma MOLOC: forall l, mo_loc` l ≡ mo_loc l.
Proof.
  unfold RC11_Model.mo_loc, Power_Model.mo_loc.
  assert_all; ins.
  by rewrite MO, SL.
Qed.

Lemma max_elt_same_rel A (r r' : relation A) (EQ: r ≡ r') a: 
  max_elt r a <-> max_elt r' a.
Proof.
  clear - EQ.
  split; by unfold max_elt; ins; apply H with b, EQ.
Qed.

Proposition OUT: forall l v, rc11_outcome l v <-> power_outcome l v.
Proof.
  assert_all; assert (MOLOC := MOLOC).
  unfold rc11_outcome, power_outcome.
  ins; split.
  - ins; desf.
    exists a; split.
    + by apply max_elt_same_rel with (r' := mo_loc l).
    + by rewrite SV.
  - ins; desf.
    exists a; split.
    + by apply max_elt_same_rel with (r' := mo_loc` l); try symmetry.
    + by rewrite SV.
Qed. *)



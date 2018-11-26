(******************************************************************************)
(** * Properties of the Power memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Power_Events Power_Model Power_Domains Power_Locations
  Power_Automation Power_Irreflexive Power_Threads Power_Helpers
  Power_Properties.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Power_Additional_Properties.

Variable G : power_execution.

(* Basic *)
Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'tid'" := G.(tid).
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
Hypothesis CON: PowerConsistent.

(* Proposition F.8 *)
Proposition rmw_atomic :
  rmw ∩ (rb ⨾ mo) ⊆ ∅₂.
Proof.
  rewrite internal_or_external with (r := rb).
  rewrite internal_or_external with (r := mo).
  relsf.
  rewrite !inter_union_r.
  repeat apply inclusion_union_l.
  - (* rb∙ ⨾ mo∙ *)
    rewrite rbi_in_sb; auto.
    arewrite (mo∙ ⊆ sb) by (unfolder; ins; desf; cycle_detector).
    cdes WF; cdes WF_RMW; rewrite RMW_IMM.
    unfold immediate; unfolder; ins; desf.
    specialize (H2 z); desf; intuition.
  - (* rb∘ ⨾ mo∙ *) unfolder; ins; desf; thread_solver. 
  - (* rb∙ ⨾ mo∘ *) unfolder; ins; desf; thread_solver.
  - (* rb∘ ⨾ mo∘ *) by cdes CON.
Qed.

(* Proposition F.9 *)
Lemma sync_hb_rbi : 
  sync ⨾ hb＊ ⨾ rb∙ ⊆ sync ⨾ hb＊ ⨾ mo^?.
Proof.
  rewrite rtEE at 1; relsf; unionL; ins.
  induction x.
  - (* x = 0 *)
    simpl; rels; arewrite (sync ⨾ rb∙ ⊆ sync); basic_solver 10.
  - (* x > 0 *)
    simpl; rewrite seqA; unfold Power_Model.hb at 2; relsf; unionL.
    + (* ppo *)
      rewrite ppo_rbi; auto; arewrite (ppo ⊆ hb).
      relsf; unionL; try (by rewrite IHx); rewrite pow_rt.
      * (* hb *) by rewrite rt_unit, <- seqA; apply trailing_refl.
      * (* hb;mo *) 
        by sin_rewrite rt_unit; arewrite (mo ⊆ mo^?) at 1.
      * (* mo *) by arewrite (mo ⊆ mo^?) at 1.
    + (* fence *)
      arewrite (fence ⨾ rb∙ ⊆ fence).
      arewrite (fence ⊆ hb).
      rewrite pow_seq, pow_rt, <- seqA; apply trailing_refl.
      eauto with rel_full.
    + (* rf∘ *)
      arewrite (rf∘ ⨾ rb∙ ⊆ mo).
      by rewrite pow_rt; rels.
Qed.

Proposition fence_hb_rbi : 
  fence ⨾ hb＊ ⨾ rb∙ ⊆ fence ⨾ hb＊ ⨾ mo^?.
Proof.
  rewrite rtEE at 1; relsf; unionL; ins.
  induction x.
  - (* n = 0 *)
    simpl; rels; arewrite (fence ⨾ rb∙ ⊆ fence); basic_solver 10.
  - (* n > 0 *)
    simpl; rewrite seqA; unfold Power_Model.hb at 2.
    relsf; unionL.
    + (* ppo *)
      rewrite ppo_rbi; auto; arewrite (ppo ⊆ hb).
      relsf; unionL; try (by rewrite IHx); rewrite pow_rt.
      * (* hb *) by rewrite rt_unit, <- seqA; apply trailing_refl.
      * (* hb;mo *) by sin_rewrite rt_unit; arewrite (mo ⊆ mo^?) at 1.
      * (* mo *) by arewrite (mo ⊆ mo^?) at 1.
    + (* fence *)
      arewrite (fence ⨾ rb∙ ⊆ fence).
      arewrite (fence ⊆ hb) at 2.
      rewrite pow_seq, pow_rt, <- seqA; apply trailing_refl.
      eauto with rel_full.
    + (* rf∘ *)
      arewrite (rf∘ ⨾ rb∙ ⊆ mo).
      by rewrite pow_rt; rels.
Qed.

(* Proposition F.10 *)
Proposition fence_trans : transitive fence.
Proof.
  apply transitiveI.
  unfold Power_Model.fence; relsf; repeat apply inclusion_union_l.
  - (* sync ; sync *)
    apply inclusion_union_r; left.
    unfold Power_Model.sync; unfolder; ins; desf.
    repeat eexists; splits; eauto.
    unfold_wf; eauto using SB_T.
  - (* lwsync ; sync *)
    unionR left.
    rewrite lwsync_in_RW_sb_RW at 1; auto.
    unfold Power_Model.sync.
    do 2 arewrite_id ⦗RW⦘ at 2.
    rels.
    arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
  - (* sync ; lwsync *)
    apply inclusion_union_r; left.
    rewrite lwsync_in_RW_sb_RW at 1; auto.
    unfold Power_Model.sync.
    do 2 arewrite_id ⦗RW⦘ at 2.
    rels.
    arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
  - (* lwsync ; lwsync *)
    unionR right.
    unfold Power_Model.lwsync; unfolder; ins; desf; splits; try type_solver.
    repeat (eexists; splits; eauto).
    unfold_wf; eauto using SB_T.
Qed.

(* Proposition F.11 *)
Proposition fence_hb : 
  fence ⨾ hb＊ ⊆ sb ∪ fence ⨾ ⦗W⦘ ⨾ hb＊.
Proof.
  rewrite rtE at 1. relsf.
  apply inclusion_union_l.
  - apply inclusion_union_r; left. by apply fence_in_sb.
  - unfold Power_Model.hb.
    rewrite path_ut_first with (r:=ppo ∪ fence) (r':=rf∘).
    relsf; apply inclusion_union_l.
    + rewrite fence_in_sb at 1 2; auto.
      rewrite ppo_in_sb at 1; auto.
      rels.
      apply inclusion_union_r; left.
      cdes WF; cdes WF_SB.
      rewrite ct_of_trans; auto.
      basic_solver.
    + arewrite (rf∘ ⊆ ⦗W⦘ ⨾ rf∘) at 1 by domain_solver.
      arewrite (rf∘ ⊆ (ppo ∪ fence ∪ rf∘)＊) at 1.
      rewrite rt_rt.
      apply inclusion_union_r; right.
      rewrite ppo_in_sb at 1; auto.
      rewrite fence_in_sb at 2; auto.
      rels.
      rewrite rtE at 1; relsf.
      apply inclusion_union_l.
      * basic_solver.
      * rewrite ct_of_trans.
        2: by unfold_wf.
        sin_rewrite fence_sbW_in_fence; auto.
        basic_solver.
Qed.

(* Proposition F.12 *)
Proposition RW_sb_fence_hb_sync :
  ⦗RW⦘ ⨾ sb ⨾ (fence ⨾ hb＊)^? ⨾ sync ⊆ (fence ⨾ hb＊)^? ⨾ sync.
Proof.
  rewrite fence_hb at 1; auto.
  rewrite cr_union_r.
  relsf.
  apply inclusion_union_l.
  - arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
    rewrite RW_sb_sync_in_sync; auto; basic_solver.
  - rewrite crE; relsf; unionL.
    + rewrite RW_sb_sync_in_sync; auto; basic_solver.
    + rewrite !seqA; sin_rewrite RW_sb_fence_in_fence; auto; basic_solver 10.
Qed.

(* Proposition F.13 *)
Proposition eco_fench_hb_acyclic :
  acyclic (eco^? ⨾ (fence ⨾ hb＊)^? ⨾ sync ⨾ hb＊).
Proof with (auto; basic_solver 25).
  rewrite eco_refl, seq_union_l.
  remember (((mo ∪ rb∘)^? ⨾ rf^? ∪ rb∙ ⨾ (rf∙)^?) ⨾ (fence ⨾ hb＊)^? ⨾ sync ⨾ hb＊) as A.
  remember ((rb∙ ⨾ rf∘) ⨾ (fence ⨾ hb＊)^? ⨾ sync ⨾ hb＊) as B.
  assert (A ⨾ B ⊆ A ⨾ A /\ B ⨾ B ⊆ B ⨾ A).
  { split; subst; rewrite !seqA;
    sin_rewrite sync_hb_rbi; auto;
    rewrite !seqA;
    (arewrite (mo^? ⨾ rf∘ ⊆ (mo ∪ rb∘)^? ⨾ rf^? ∪ rb∙ ⨾ (rf∙)^?) 
      by (unionR left; arewrite (mo^? ⊆ (mo ∪ rb∘)^?); 
          arewrite (rf∘ ⊆ rf^?); done));
    done.
  }
  destruct H.
  apply acyclic_specific_absorb; try done.
  - (* acyclic A *)
    cdes CON.
    arewrite (A ⊆ mo^? ⨾ prop2).
    { subst. unfold Power_Model.prop2.
      rewrite cr_union_l.
      rewrite internal_or_external with (r := rf) at 1.
      relsf; unionL.
      - rewrite cr_union_r; relsf; unionL.
        + arewrite (rf∙ ⊆ ⦗RW⦘ ⨾ sb).
          sin_rewrite RW_sb_fence_hb_sync...
        + basic_solver 25.
      - rewrite cr_union_r; relsf; unionL.
        + arewrite (rf∙ ⊆ ⦗RW⦘ ⨾ sb).
          sin_rewrite RW_sb_fence_hb_sync...
        + basic_solver 25.
      - arewrite (rb∙ ⊆ ⦗RW⦘ ⨾ sb).
        rewrite crE.
        relsf; unionL.
        + sin_rewrite RW_sb_fence_hb_sync...
        + arewrite (rf∙ ⊆ sb).
          arewrite (sb ⨾ sb ⊆ sb) by unfold_wf.
          sin_rewrite RW_sb_fence_hb_sync...
    }
    arewrite (prop2 ⊆ prop).
    arewrite (mo^? ⨾ prop ⊆ (mo ∪ prop)⁺).
    red; relsf.
  - (* irreflexive B *)
    cdes CON; subst.
    rewrite irreflexive_seqC, !seqA.
    sin_rewrite sync_hb_rbi; try done.
    rewrite <- !seqA, <- irreflexive_seqC, !seqA.
    arewrite (rf∘ ⨾ (fence ⨾ hb＊)^? ⨾ sync ⨾ hb＊ ⊆ prop)
      by unfold Power_Model.prop, Power_Model.prop2; unionR right; basic_solver 25.
    rewrite irreflexive_seqC.
    arewrite (mo^? ⨾ prop ⊆ (mo ∪ prop)⁺).
    red; relsf.
Qed.

(* Proposition F.14 *)
Definition S := sb^? ⨾ ⦗F⦘ ⨾ sb ⨾ rf∘ ⨾ hb＊ ⨾ (sb ⨾ ⦗F⦘ ∪ eco∙)^?.

Proposition sb_F_sb_spo: strict_partial_order S.
Proof.
  assert (H1': fence ⨾ rf∘ ⊆ hb⁺).
  { arewrite (fence ⊆ hb).
    arewrite (rf∘ ⊆ hb).
    unfolder; ins; desf; vauto. }
  assert (H2': rf∘ ⨾ hb＊ ⨾ fence ⨾ rf∘ ⊆ rf∘ ⨾ hb＊)
    by (by rewrite H1', rt_ct, inclusion_t_rt).
  assert (H1: ⦗RW⦘ ⨾ sb ⨾ ⦗F⦘ ⨾ sb^? ⨾ ⦗F⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ fence).
  { arewrite_id ⦗F⦘ at 1; rels.
    arewrite (sb ⨾ sb^? ⊆ sb) by (unfold_wf; basic_solver).
    by sin_rewrite RW_sb_F_sb_W_in_fence.
  }
  assert (H2: rf∘ ⨾ hb＊ ⨾ sb^? ⨾ ⦗F⦘ ⨾ sb ⨾ rf∘ ⊆ rf∘ ⨾ hb＊ ⨾ fence ⨾ rf∘).
  { rewrite rtE at 1; rewrite crE; relsf; unionL.
    - arewrite (rf∘ ⊆ rf∘ ⨾ ⦗R⦘) at 1 by domain_solver.
      type_solver.
    - arewrite (rf∘ ⊆ rf∘ ⨾ ⦗RW⦘) at 1 by domain_solver.
      arewrite (rf∘ ⊆ ⦗W⦘ ⨾ rf∘) at 2 by domain_solver.
      sin_rewrite RW_sb_F_sb_W_in_fence; try done.
      basic_solver 25. 
    - arewrite (hb⁺ ⊆ hb⁺ ⨾ ⦗RW⦘) at 1 by domain_solver.
      type_solver.
    - arewrite (hb⁺ ⊆ hb⁺ ⨾ ⦗RW⦘) at 1 by domain_solver.
      arewrite (rf∘ ⊆ ⦗W⦘ ⨾ rf∘) at 2 by domain_solver.
      sin_rewrite RW_sb_F_sb_W_in_fence; auto.
      by rewrite inclusion_t_rt.
  }
  assert (H: ⦗RW⦘ ⨾ sb ⨾ ⦗F⦘ ⨾ sb ⨾ ⦗W⦘ ⨾ rf∘ ⨾ hb＊ ⊆ hb⁺) by
    by sin_rewrite RW_sb_F_sb_W_in_fence; auto; sin_rewrite H1'; rels.
  assert (IRR: irreflexive (⦗RW⦘ ⨾ sb ⨾ ⦗F⦘ ⨾ sb ⨾ ⦗W⦘ ⨾ rf∘ ⨾ hb＊)) by
    by rewrite H; cdes CON.

  red; splits.
  - (* irreflexive S *)
    unfold S.
    arewrite (rf∘ ⨾ hb＊ ⊆ rf∘ ⨾ hb＊ ⨾ ⦗RW⦘) by domain_solver.
    arewrite (eco∙ ⊆ sb).
    arewrite (rf∘ ⊆ ⦗W⦘ ⨾ rf∘) by domain_solver.
    rewrite !crE; relsf; unionL.
    + rotate; type_solver.
    + by rotate.
    + by rotate 3; seq_rewrite seq_eqvK.
    + arewrite (sb ⊆ sb^?) at 1.
      rotate 5; sin_rewrite H1.
      rotate; sin_rewrite H1'; rels; by cdes CON.
    + by rotate 2.
    + by rotate 2; arewrite (sb ⨾ sb ⊆ sb).
  - (* transitive S *)
    apply transitiveI.
    unfold S.
    case_refl (sb ⨾ ⦗F⦘ ∪ eco∙).
    + sin_rewrite H2; sin_rewrite H2'; rewrite !seqA; relsf.
    + 
      arewrite (rf∘ ⨾ hb＊ ⊆ rf∘ ⨾ hb＊ ⨾ ⦗RW⦘) by domain_solver.
      arewrite (rf∘ ⊆ ⦗W⦘ ⨾ rf∘) at 2 by domain_solver.
      hahn_frame; case_union_2 _ _.
      * arewrite (⦗RW⦘ ⨾ sb ⨾ ⦗F⦘ ⨾ sb^? ⨾ ⦗F⦘ ⨾ sb ⨾ ⦗W⦘ ⨾ rf∘ ⨾ hb＊ ⊆ hb＊).
        { rewrite <- !seqA.
          arewrite (((((((⦗RW⦘ ⨾ sb) ⨾ ⦗F⦘) ⨾ sb^?) ⨾ ⦗F⦘) ⨾ sb) ⨾ ⦗W⦘) ⊆ fence) by rewrite !seqA, H1.
          sin_rewrite H1'.
          eauto with rel_full. }
        eauto with rel_full.
      * arewrite (eco∙ ⊆ sb) at 1.
        arewrite (sb ⨾ sb^? ⊆ sb) by case_refl sb; eauto with rel_full.
        rewrite H; rels; by cdes CON.
Qed.

Lemma S_trans : transitive S.
Proof. by cdes CON; apply sb_F_sb_spo. Qed.

(* Proposition F.15 *)
Lemma eco_alt : eco ⊆ ⦗RW⦘ ⨾ sb ∪ rf∘ ∪ mo ⨾ rf^? ∪ rb∘ ⨾ rf^? ∪ rb∙ ⨾ rf∘.
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
  arewrite (rf∙ ⊆ ⦗RW⦘ ⨾ sb).
  rewrite <- unionA.
  basic_solver 42.
Qed.

Lemma rf_fence_W_in_fence : rf^? ⨾ fence ⨾ ⦗W⦘ ⊆ rf∘^? ⨾ fence ⨾ ⦗W⦘.
Proof.
  rewrite internal_or_external with (r := rf) at 1; rewrite cr_union_r.
  arewrite (rf∙ ⊆ ⦗RW⦘ ⨾ rf∙) by domain_solver.
  arewrite (rf∙ ⊆ sb).
  generalize (RW_sb_fence_in_fence WF).
  basic_solver 42.
Qed.

Lemma eco_sb_irr : irreflexive (eco ⨾ sb).
Proof.
  apply irreflexive_seqC.
  apply funeq_irreflexive with (f := (loc lab)).
  + by red; eapply eco_loc.
  + red; unfold Power_Model.eco; unfold union, clos_refl, seq.
    ins; desf; cycle_detector0 x z.
Qed.

Lemma eco_fence_hb_irr : irreflexive (eco ⨾ fence ⨾ hb＊).
Proof.
  rewrite Power_Additional_Properties.fence_hb.
  case_union_2 _ _; [apply eco_sb_irr|].
  cdes CON; rewrite eco_alt.
  case_union_5 _ _ (mo ⨾ rf^?) (rb∘ ⨾ rf^?) (rb∙ ⨾ rf∘); simpl_rels.
  + (* ⟪a,b⟫ ∈ sb *)
    sin_rewrite RW_sb_fence_in_fence; auto.
    arewrite (fence ⊆ hb).
    by rewrite <- ct_begin.
  + (* ⟪a,b⟫ ∈ rf∘ *)
    arewrite (rf∘ ⊆ hb); arewrite (fence ⊆ hb); arewrite_id ⦗W⦘; simpl_rels.
    by rewrite <- ct_begin, ct_step with (r := hb) at 1; rewrite ct_ct.
  + (* ⟪a,b⟫ ∈ mo;rf? *)
    sin_rewrite rf_fence_W_in_fence; simpl_rels.
    arewrite (mo ⊆ ⦗W⦘ ⨾ mo ⨾ ⦗W⦘) by domain_solver.
    apply irreflexive_seqC; simpl_rels.
    arewrite (⦗W⦘ ⨾ rf∘^? ⨾ fence ⨾ ⦗W⦘ ⨾ hb＊ ⨾ ⦗W⦘ ⊆ prop1).
    arewrite (prop1 ⊆ prop).
    by arewrite (mo ⨾ prop ⊆ (mo ∪ prop)^+).
  + (* ⟪a,b⟫ ∈ rb∘;rf? *)
    sin_rewrite rf_fence_W_in_fence; simpl_rels.
    arewrite (rb∘ ⊆ rb∘ ⨾ ⦗W⦘) by domain_solver.
    arewrite (⦗W⦘ ⨾ rf∘^? ⨾ fence ⨾ ⦗W⦘  ⊆ prop1).
    { unfold Power_Model.prop1.
      arewrite (⦗W⦘ ⊆ hb＊ ⨾ ⦗W⦘) at 2 by basic_solver 42. }
    by arewrite (prop1 ⊆ prop).
  + (* ⟪a,b⟫ ∈ rb∙;rf∘ *)
    arewrite (rf∘ ⊆ ⦗W⦘ ⨾ rf∘) by domain_solver.
    apply irreflexive_seqC.
    arewrite_id ⦗W⦘ at 2; simpl_rels.
    sin_rewrite fence_hb_rbi.
    rewrite <- seq_eqvK, !seqA.
    apply irreflexive_seqC; simpl_rels.
    arewrite (mo^? ⨾ ⦗W⦘ ⊆ ⦗W⦘ ⨾ mo^?) by
      case_refl mo;
      [|arewrite (mo ⊆ ⦗W⦘ ⨾ mo) by domain_solver]; basic_solver 42.
    arewrite (⦗W⦘ ⨾ rf∘ ⨾ fence ⨾ hb＊ ⨾ ⦗W⦘ ⊆ prop1).
    arewrite (prop1 ⊆ prop).
    case_refl mo.
    * by arewrite (prop ⊆ mo ∪ prop); auto with rel_full.
    * by arewrite (prop ⨾ mo ⊆ (mo ∪ prop)^+).
Qed.

Proposition eco_sb_fence_hb_irr : 
  irreflexive (eco ⨾ (sb ∪ fence ⨾ hb＊)).
Proof.
  case_union_2 sb _.
  - apply eco_sb_irr.
  - apply eco_fence_hb_irr.
Qed.

Proposition eco_sb_fence_hb_eco_R_irr : 
  irreflexive (eco ⨾ (sb ∪ (fence ⨾ hb＊ ⨾ (sb ⨾ ⦗F⦘ ∪ eco)^?))).
Proof.
  case_union_2 sb _; [apply eco_sb_irr|].
  case_refl (sb ⨾ ⦗F⦘ ∪ eco).
  - apply eco_fence_hb_irr.
  - case_union_2 _ _.
    + arewrite (eco ⊆ ⦗RW⦘ ⨾ eco) by domain_solver.
      unfolder; ins; desf; type_solver.
    +rotate.
      arewrite (eco ⨾ eco ⊆ eco) by
        apply rewrite_trans, Power_Helpers.eco_trans.
      apply eco_fence_hb_irr.
Qed.

End Power_Additional_Properties.

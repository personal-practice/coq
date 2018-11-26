(******************************************************************************)
(** * Properties of the Power memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Power_Events Power_Model Power_Domains Power_Locations
  Power_Automation Power_Irreflexive Power_Threads Power_Helpers.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Power_Properties.

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

(******************************************************************************)
(** ** Propositions *)
(******************************************************************************)

(* Proposition F.1 *)
Proposition ppo_trans : transitive ppo.
Proof.
  unfold transitive, Power_Model.ppo, union, seq, eqv_rel.
  ins; desf;
  (* Rule out impossible cases *)
  try type_solver.
  (* ⦗R⦘ ; ii ; ⦗R⦘ *)
  - left; exists z2; split; auto; exists z; vauto.
  (* ⦗R⦘ ; ic ; ⦗W⦘ *)
  - right; exists z2; split; auto; exists z; splits; vauto.
Qed.

(* Proposition F.2 *)
Proposition Wpsbloc_in_ii (WF: Wf) (CON: PowerConsistent) : ⦗W⦘ ⨾ psbloc ⊆ ii.
Proof.
  unfold inclusion.
  intros a b psb_ab.
  remember (⦗W⦘ ⨾ psbloc) as w_psb eqn:Eq_Wpsb.
  remember (loc lab a) as x eqn:Eq_LocX.

  assert (PSBLOC_SB: w_psb ⊆ sb) by 
    (unfold Power_Model.psbloc in *; unfolder in *; ins; desf).
  assert (DOM: (restrict_location W x) a /\ (restrict_location R x) b)
    by (split; type_solver).
  assert (SB_AB: sb a b) by (by apply PSBLOC_SB).
  assert (SBLOC_AB: sb|loc a b) by (split; auto; loc_solver).
  assert (PSBLOC_AB: psbloc a b) by (unfolder in *; desf).
  assert (N_INIT_A: I a) by type_solver.
  assert (NO_C: ~ exists c, W⌇x c /\ sb a c /\ sb c b).
  { red; ins; desf.
    unfold Power_Model.psbloc, minus_rel in PSBLOC_AB.
    destruct PSBLOC_AB as [PSBLOC_AB NO_W].
    contradict NO_W.
    unfolder; eexists; splits; eauto; [loc_solver | type_solver].
  }
  assert (EX_D: exists d, W⌇x d /\ rf d b) by 
    (apply complete_exists; desf; act_solver).
  destruct EX_D as [d HD].
  destruct (classic(d = a)) as [EQ | NEQ].
  - (* d = a*)
    apply rfi_in_ii; subst; red; split; desf; thread_solver.
  - (* d <> a *)
    cdes CON; cdes SC_PER_LOC; 
    clear OBSERVATION PROPAGATION POWER_ATOMICITY POWER_NO_THIN_AIR.
    remember (sb |loc ∪ rf ∪ rb ∪ mo) as trans.
    assert (R_DB: (sb ∪ rf ∪ mo) d b).
      by unfolder; left; right.
    assert (IRR_SC: irreflexive trans).
      by apply irrefl_trans.
    assert (MO_AD: mo a d).
    { cdes WF; cdes WF_MO.
      assert (exists l, loc lab d = Some l) by 
        by apply not_none_implies_some, Wa_implies_some_loc; type_solver.
      desf; eapply tot_ex; eauto;
      try (by clear - WF CON HD DOM SBLOC_AB H;
           splits; [act_solver | type_solver | loc_solver]).
      red; ins.
      assert (RB_BA: rb b a) by (by red; unfolder; exists d; split).
      clear - WF CON SBLOC_AB RB_BA; cycle_detector0 a b.
    }
    assert (N_SB_DA: ~ sb d a) by (clear - WF CON MO_AD; cycle_detector).
    assert (N_SB_BD: ~ sb b d) by (clear - WF CON HD0; cycle_detector).
    assert (MOE_AD: mo∘ a d).
    { red; split; auto.
      contradict NO_C.
      assert (exists i, tid d = Some i /\ tid a = Some i) by thread_solver.
      desf.
      exists d; splits; auto; cdes WF; cdes WF_SB; desf.
      - (* sb a d *)
        eapply tot_ex; eauto; red; split; eauto; try act_solver.
      - (* sb d b *)
        eapply tot_ex; eauto;
          try (red; split; try act_solver; thread_solver).
          solve_irreflexive.
    }
    assert (RFE_DB: rf∘ d b).
    { red; split; auto; red; ins.
      red in MOE_AD; desf.
      contradict MOE_AD0.
      thread_solver. }
    subst; apply detour_in_ii.
    red; unfold seq; red; split; auto.
    by exists d.
    thread_solver.
Qed.

(* Proposition F.3 *)
Proposition deps_W_in_ppo (WF: Wf) (CON: PowerConsistent) : (deps ∪ addr ⨾ sb) ⨾ ⦗W⦘ ⨾ psbloc ⨾ ppo ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  unfold Power_Model.deps.
  remember (data ∪ addr) as dep.
  relsf; repeat apply inclusion_union_l; subst.
  - (* ⟪a,b⟫ ∈ data ∪ addr *)
    arewrite (data ∪ addr ⊆ ⦗R⦘ ⨾ ii).
    sin_rewrite Wpsbloc_in_ii; try done.
    arewrite (ii ⨾ ii ⊆ ii).
    unfold Power_Model.ppo; relsf.
    rewrite !seqA.
    arewrite_false (⦗R⦘ ⨾ ⦗W⦘).
      by type_solver.
    rels.
    arewrite_id ⦗R⦘ at 2; rels.
    arewrite (ii ⨾ ic ⊆ ic).
    by unionR right.
  - (* ⟪a,b⟫ ∈ ctrl *)
    arewrite (psbloc ⊆ sb).
    arewrite (ppo ⊆ sb).
    cdes WF; cdes WF_DEPS; cdes WF_SB.
    arewrite_id ⦗W⦘ at 1; relsf.
    sin_rewrite CTRL_SB.
    arewrite (ctrl ⊆ ⦗R⦘ ⨾ ctrl) by domain_solver.
    clear; right; unfold seq, eqv_rel in *; desf; repeat eexists; eauto.
    assert (RW y) by type_solver.
    apply CC, CC0; red; unfold union; left; right; vauto.
  - (* ⟪a,b⟫ ∈ addr ⨾ sb *)
    arewrite (psbloc ⊆ sb).
    arewrite (ppo ⊆ sb).
    cdes WF; cdes WF_DEPS; cdes WF_SB.
    arewrite_id ⦗W⦘ at 1; relsf.
    arewrite (addr ⊆ ⦗R⦘ ⨾ addr) by domain_solver.
    clear; right; unfold seq, eqv_rel in *; desf; repeat eexists; eauto.
    apply CC, CC0; red; unfolder; right.
    repeat (eexists; splits; eauto); type_solver.
Qed.

(* Proposition F.4 *)
Proposition deps_R_in_ppo (WF: Wf) : (deps ∪ addr ⨾ sb) ⨾ ⦗R⦘ ⨾ sb ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  cdes WF; cdes WF_DEPS; cdes WF_SB.
  arewrite ((deps ∪ addr ⨾ sb) ⨾ ⦗R⦘ ⊆ ctrl ∪ addr ⨾ sb^?).
  { unfold Power_Model.deps; relsf.
    repeat apply inclusion_union_l; apply inclusion_union_r;
    try (by arewrite_id ⦗R⦘; rels).
    - rewrite DATA. rewrite !seqA. left. type_solver.
    - right; arewrite_id ⦗R⦘; rels.
      unfolder; ins; eexists; eauto.
  }
  relsf. apply inclusion_union_l.
  - (* ⟪a,b⟫ ∈ ctrl *)
    arewrite (ctrl ⨾ sb ⊆ ctrl).
    arewrite (ctrl ⊆ ⦗R⦘ ⨾ ctrl) by apply doma_helper, ctrl_doma.
    clear; right; unfold seq, eqv_rel in *; desf; repeat eexists; eauto.
    apply CC, CC0; red; unfolder; left; right.
    repeat (eexists; splits; eauto); type_solver.
  - (* ⟪a,b⟫ ∈ addr ; sb? *)
    rewrite seqA.
    arewrite (sb^? ⨾ sb ⊆ sb) by apply (rewrite_trans_seq_cr_l SB_T).
    by apply addrsbW_in_ppo.
Qed.

(* Proposition F.5 *)
Definition ℜ := deps ∪ addr ⨾ sb ∪ psbloc.

Proposition deps_R_W_in_ppo (WF: Wf) (CON: PowerConsistent) : (deps ∪ addr⨾sb) ⨾ ℜ＊ ⨾ ⦗W⦘ ⊆ ppo.
Proof.
  remember (deps ∪ addr ⨾ sb) as d.
  rewrite rtEE; relsf; apply inclusion_Union_l; intros n _; subst d.
  induction n using (well_founded_ind Wf_nat.lt_wf).

  arewrite (ℜ ⊆ ⦗R ∪₁ W⦘ ⨾ ℜ) at 1 by (unfold ℜ; domain_solver).
  destruct n.
  - (* n = 0 *) by simpl; rels; apply depsUaddrsbW_in_ppo.
  - (* n > 0 *)
  simpl; rewrite seq_pow_l.
  rewrite !seqA.
  remember (deps ∪ addr ⨾ sb) as r1.
  remember (ℜ ⨾ (⦗R ∪₁ W⦘ ⨾ ℜ)^^n ⨾ ⦗W⦘) as r2.
  rewrite id_union; relsf.
  unionL; subst; arewrite_id ⦗R ∪₁ W⦘; arewrite (⦗fun _ => True⦘ ⨾ ℜ ⊆ ℜ).
  + (* c ∈ R *)
    arewrite (ℜ ⊆ sb) by unfold_wf; unfold ℜ; unionL; eauto with rel_full.
    cdes WF; cdes WF_SB; arewrite (sb ⨾ sb^^n ⊆ sb) by apply pow_t.
    by apply deps_R_in_ppo.
  + (* c ∈ W *)
    unfold ℜ at 1.
    rewrite <- seqA.
    remember ((deps ∪ addr ⨾ sb) ⨾ ⦗W⦘) as r1.
    remember (ℜ ^^ n ⨾ ⦗W⦘) as r2.
    remember (deps ∪ addr ⨾ sb) as d.
    relsf; apply inclusion_union_l; subst.
    { (* we can only have psbloc on the first unfolding of ℜ *)
      arewrite ((deps ∪ addr ⨾ sb) ⊆ ⦗R⦘ ⨾ (deps ∪ addr ⨾ sb)) 
        by apply doma_helper, depsUaddrsb_doma.
      type_solver.
    }
    rewrite !seqA.
    
    unfold ℜ.
    remember (deps ∪ addr ⨾ sb) as D.
    remember psbloc as P.
    rewrite pow_union_decomposition.
    relsf; unionL; subst.
    { (* cannot end with psbloc *)
      arewrite (psbloc ⨾ psbloc ^^ n ⊆ psbloc ^^ n ⨾ psbloc) by rewrite seq_pow_l.
      arewrite (psbloc ⊆ psbloc ⨾ ⦗R⦘) by domain_solver.
      type_solver.
    }
    ins; rewrite !seqA.
    arewrite (psbloc ⨾ psbloc ^^ x ⊆ psbloc) by apply pow_t, psbloc_trans.
    remember (n - x - 1) as y.
    assert (LT: y < S n) by omega.
    specialize (H y LT).
    unfold ℜ in H.
    remember ((deps ∪ addr ⨾ sb) ⨾ (deps ∪ addr ⨾ sb ∪ psbloc) ^^ y ⨾ ⦗W⦘) as r.
    arewrite (r ⊆ r ⨾ ⦗W⦘) by subst; domain_solver.
    by rewrite H; apply deps_W_in_ppo.
Qed.

Lemma deps_R_W_in_ppo_pow (WF: Wf) (CON: PowerConsistent) (n: nat) : 
  (deps ∪ addr⨾sb) ⨾ ℜ^^n ⨾ ⦗W⦘ ⊆ ppo.
Proof. 
  arewrite (ℜ ^^ n ⊆ ℜ＊) by apply pow_rt.
  by apply deps_R_W_in_ppo.
Qed.

(* Proposition F.6 *)
Proposition rfe_R_W_in_ppo (WF: Wf) (CON: PowerConsistent) : rf∘ ⨾ ℜ⁺ ⨾ ⦗W⦘ ⊆ rf∘ ⨾ ppo.
Proof.
  arewrite (ℜ⁺ ⊆ ℜ ⨾ ℜ＊) at 1 by apply ct_begin.
  unfold ℜ at 1.
  remember (deps ∪ addr ⨾ sb) as D.
  relsf; apply inclusion_union_l; subst.
  - (* ⟪b,c⟫ ∈ (deps ∪ addr⨾sb) ⨾ ℜ＊ *)
    by arewrite ((deps ∪ addr ⨾ sb) ⨾ ℜ＊ ⨾ ⦗W⦘ ⊆ ppo) at 1 by apply deps_R_W_in_ppo.
  - (* ⟪b,c⟫ ∈ psbloc ⨾ ℜ＊ *)
    rewrite rtEE; relsf; apply inclusion_Union_l; intros n _.
    unfold ℜ.
    rewrite pow_union_decomposition.
    relsf; apply inclusion_union_l.
    { (* cannot end with psbloc *)
      arewrite (psbloc ⨾ psbloc ^^ n ⊆ psbloc ^^ n ⨾ psbloc) by rewrite seq_pow_l.
      arewrite (psbloc ⊆ psbloc ⨾ ⦗R⦘) by domain_solver.
      type_solver. }
    apply inclusion_Union_l; intros n' H.
    rewrite !seqA.
    arewrite (psbloc ⨾ psbloc ^^ n' ⊆ psbloc) by apply pow_t, psbloc_trans.
    rewrite deps_R_W_in_ppo_pow; try done.

    arewrite (rf∘ ⨾ psbloc ⊆ rf∘ ⨾ rdw^?).
    { unfold inclusion. clear H.
      intros a c H.
      cdes WF; cdes WF_RF; cdes WF_MO; cdes WF_SB; cdes CON.
      clear - WF CON n n' H RF_LOC RF_TOT MO_LOC MO_IRR MO_TOT SB_IRR SB_TOT SC_PER_LOC.

      unfold Power_Model.psbloc, Power_Model.rdw, Power_Model.rb, 
      seq, restr_eq_rel, minus_rel, clos_refl, eqv_rel in H |- *; desf.

      rename z0 into b.

      forward eapply (RF_TOT c) as [w RFc]; ins.
        act_solver.
      red in H2; desf.
      destruct ((classic(w = a))) as [|NEQ]; desf.
        by eexists; splits; eauto; thread_solver.
      exists b; splits; eauto.
       right; split; ins; try thread_solver.

      assert (ACTS: In a acts /\ In b acts /\ In c acts /\ In w acts)
        by (splits; act_solver).
      
      assert (MO_aw: mo a w).
      { assert (LOC_aw: loc lab a = loc lab w) by loc_solver.
        assert (LOC_a: exists l, loc lab a = Some l)
          by (eapply not_none_implies_some, Wa_implies_some_loc; type_solver).
        destruct LOC_a as [l].

        apply MO_TOT with l in NEQ; desf; try (splits; try type_solver; loc_solver).
        (* mo a w *)
        destruct SC_PER_LOC with c; unfold Power_Model.rb; unfolder.
          eapply t_trans with a; eauto 8 using t_step.
          eapply t_trans with b; eauto 8 using t_step.
      }
      
      assert (RB_bw: rb b w) 
        by (red; unfolder; eexists; splits; eauto; apply MO_aw).

      assert (N_SB_cw: ~ sb c w) by cycle_detector.

      assert (N_SB_wb: ~ sb w b) by cycle_detector.

      assert (N_SB_bw: ~ sb b w).
      { red; ins.
        assert (ST_cw: same_thread c w) by thread_solver.
        assert (SB_wc_cw: sb w c \/ sb c w) by thread_solver.
        desf; contradict H1.
        exists w; splits; auto.
        red; split; auto.
        loc_solver.
        by eexists; splits; eauto; type_solver.
      }

      exists w; splits; ins; thread_solver.
    }
    arewrite (rdw ⊆ ppo).
    by rewrite (rewrite_trans_seq_cr_l ppo_trans).
Qed.

(* Proposition F.7 *)
Proposition ppo_rbi (WF: Wf) (CON: PowerConsistent) : 
  ppo ⨾ rb∙ ⊆ ppo ∪ ppo ⨾ mo ∪ mo ∪ rb∙.
Proof.
  arewrite (rb∙ ⊆ ⦗R⦘ ⨾ rb∙) by domain_solver.
  sin_rewrite ppo_R_in_R_Li; auto.
  red; ins. unfold seq in H; desf.
  unfolder in H; desf; subst.
  rename y into c, z0 into a, z into b.
  apply Li_rec with (P:=L a)
  (P0:=(fun b => rb∙ b c -> (ppo ∪ ppo ⨾ mo ∪ mo ∪ rb∙) a c)) in H1; eauto; ins; vauto.
  - (* ci0 *)
    red in H; unfolder in H; desf.
    + (* ctrl_isync *)
      do 3 left.
      apply L_in_ppo.
      unfolder; repeat (eexists; splits; eauto; splits); try type_solver.
      assert (ctrl_isync ⨾ rb∙ ⊆ L) by (rewrite ctrli_rbi_in_ci0; auto; vauto).
      revert H5; basic_solver.
    + (* detour *)
      left; right.
      apply detour_rbi_in_mo; auto.
      basic_solver.
  - (* ii0 *)
    red in H; unfolder in H; desf.
    + (* addr *)
      do 3 left.
      apply L_in_ppo.
      unfolder; repeat (eexists; splits; eauto; splits); try type_solver.
      assert (addr ⨾ rb∙ ⊆ L).
      { arewrite (rb∙ ⊆ rb∙ ⨾ ⦗RW⦘) by domain_solver.
        rewrite rbi_in_sb; auto.
        arewrite (addr ⨾ sb ⨾ ⦗RW⦘ ⊆ cc0) by vauto.
        red; ins; vauto. }
      revert H4; basic_solver.
    + (* data *)
      assert (W y) by type_solver.
      assert (R y) by type_solver.
      type_solver.
    + (* rdw *)
      right. apply rdw_rbi_in_rbi; basic_solver.
    + (* rf∙ *)
      left; right.
      apply rewrite_internal in H3.
      apply rf_rb_in_mo; basic_solver.
  - (* ci0 *)
    red in H4; unfolder in H4; desf.
    + (* ctrl_isync *)
      do 3 left.
      apply L_in_ppo.
      assert (W c) by type_solver.
      unfolder; splits; auto.
      apply L_L_cc with z; auto.
      left; right.
      unfolder; eexists; splits; eauto; try type_solver.
      cdes WF; cdes WF_DEPS; apply CTRL_SB.
      apply CTRL_CTLRI in H4.
      apply rbi_in_sb in H5; auto.
      basic_solver.
    + (* detour *)
      do 2 left; right.
      exists z.
      split.
      * apply L_in_ppo.
        assert (W z) by type_solver.
        unfolder; eexists; splits; eauto.
      * apply detour_rbi_in_mo; auto; basic_solver.
  - red in H4; unfolder in H4; desf.
    + (* addr *)
      assert (rb∙ ⊆ rb∙ ⨾ ⦗RW⦘) by domain_solver.
      apply H6 in H5; unfold seq in H5; desf.
      do 3 left.
      apply L_in_ppo.
      unfolder. splits; auto; only 2:type_solver.
      apply rbi_in_sb in H5; auto.
      apply L_L_cc with z; vauto.
      right; unfolder in *; basic_solver 42.
    + (* data *)
      assert (W y) by type_solver.
      assert (R y) by type_solver.
      type_solver.
    + (* rdw *)
      apply H3.
      apply rdw_rbi_in_rbi; auto.
      basic_solver.
    + (* rf∙ *)
      apply L_Li in H.
      do 2 left; right.
      exists z.
      split.
      * apply L_in_ppo.
        unfolder; repeat (eexists; splits; eauto).
        type_solver.
      * apply rewrite_internal in H5.
        apply rf_rb_in_mo; basic_solver.
Qed.

End Power_Properties.

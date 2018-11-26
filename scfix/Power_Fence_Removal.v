(******************************************************************************)
(** * Removing Redundant Fences *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Power_Events  Power_Model Power_Domains Power_Locations
  Power_Automation Power_Irreflexive Power_Threads Power_Helpers
  Power_Executions.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Power_Fences.

Variables G G' : power_execution.

(* Lemma F.1 *)
Definition filter_fence_events G P : power_execution :=
  let acts' := (filterP P G.(acts)) in
  let E := ⦗fun a => In a acts'⦘ in
  {|  acts        := acts';
      lab         := G.(lab);
      sb          := E ⨾ G.(sb) ⨾ E;
      rf          := G.(rf);
      mo          := G.(mo);
      rmw         := G.(rmw);
      data        := G.(data);
      addr        := G.(addr);
      ctrl        := G.(ctrl) ⨾ E;
      ctrl_isync  := G.(ctrl_isync) ⨾ E
  |}.

Definition FP b := ~
  (is_f_lwsync G.(lab) b /\
  exists a, is_f_sync G.(lab) a /\ G.(sb)|imm a b).

Lemma F_sb_Flw (WF: Wf G) (FG: G' = (filter_fence_events G FP)): 
  PowerConsistent G' -> PowerConsistent G.
Proof.

  assert (FE_RW: ⦗fun a => In a (filterP FP (acts G))⦘ ⨾ ⦗RW G⦘ ≡ ⦗E G⦘ ⨾ ⦗RW G⦘).
  { red; split; unfolder; ins; desf;
    assert (~ is_f_lwsync (lab G) y) by (red; ins; type_solver).
    - eexists; splits; eauto; apply in_filterP_iff in H0; desf.
    - eexists; splits; eauto.
      apply in_filterP_iff; splits; auto.
      unfold FP; red; ins; desf. }
  assert (RW_FE: ⦗RW G⦘ ⨾ ⦗fun a => In a (filterP FP (acts G))⦘ ≡ ⦗RW G⦘ ⨾ ⦗E G⦘).
  { red; split; unfolder; ins; desf;
    assert (~ is_f_lwsync (lab G) y) by (red; ins; type_solver).
    - eexists; splits; eauto; apply in_filterP_iff in H1; desf.
    - eexists; splits; eauto.
      apply in_filterP_iff; splits; auto.
      unfold FP; red; ins; desf. }

assert (SB_IN: 
⦗RW G⦘ ;; sb G ;; ⦗RW G⦘ ⊆ 
⦗fun a : event => In a (filterP FP (acts G))⦘
  ⨾ sb G ⨾ ⦗fun a : event => In a (filterP FP (acts G))⦘).
{ unfold_wf.
rewrite SB_ACT at 1; rewrite !seqA.
arewrite (⦗RW G⦘ ⨾ ⦗E G⦘ ⊆ ⦗E G⦘ ;; ⦗RW G⦘) by basic_solver.
seq_rewrite <- !FE_RW.
basic_solver 10. }

  apply consistent_alt2; splits; auto.
  { (* Wf G' *)
    repeat autounfold with wf_unfold; unnw; splits;
    subst; unfold filter_fence_events; unfold_all; simpl;
    try (by unfold_wf; desf).
    - hahn_frame; unfold_wf; desf.
    - surround <R> ctrl {G}; unfolder; ins; desf.
    - surround <R> ctrl_isync {G}; unfolder; ins; desf.
- unfold_wf; revert CTRL_SB; basic_solver.
- unfold_wf; revert CTRLI_SB; basic_solver.
    - cdes WF; cdes WF_DEPS.
      surround rmw <W> {G}.
      rewrite RMW_DEPS.
      case_union_3 _ _ (ctrl G).
      + by clear_equivs ⦗W G⦘; unionR left -> left.
      + by clear_equivs ⦗W G⦘; unionR left -> right.
      + unionR right.
        unfolder; ins; desf.
        eexists; splits; eauto.
        apply in_filterP_iff; splits.
        * act_solver.
        * red. apply or_not_and. left. red; ins; type_solver.
    - unfold_wf; revert RMW_SB; basic_solver.
    - rewrite <- SB_IN; unfold_wf; rewrite DATA, DATA_IN_SB; type_solver.
    - rewrite <- SB_IN; unfold_wf; rewrite ADDR, ADDR_IN_SB; type_solver.
    - unfold_wf. rewrite CTRL_RE, CTRL_IN_SB.
       rewrite SB_ACT at 1; rewrite !seqA.
       arewrite (⦗R G⦘ ⨾ ⦗E G⦘ ⊆ ⦗E G⦘ ;; ⦗RW G⦘) by type_solver.
       seq_rewrite <- FE_RW; basic_solver 8.
    - unfold_wf. rewrite CTRLI_RE, CTRLI_IN_SB.
       rewrite SB_ACT at 1; rewrite !seqA.
       arewrite (⦗R G⦘ ⨾ ⦗E G⦘ ⊆ ⦗E G⦘ ;; ⦗RW G⦘) by type_solver.
       seq_rewrite <- FE_RW; basic_solver 8.
    - ins; apply in_filterP_iff; split.
      + by unfold_wf; auto.
      + red; apply or_not_and; left.
        red; ins.
        unfold is_init, init_label, is_f_lwsync in *; desf.
        cdes WF; cdes WF_ACTS; rewrite LAB_INIT in Heq; desf.
    - basic_solver 42.
    - rewrite <- seq_eqvK at 1.
      hahn_frame.
      arewrite (⦗fun a => In a (filterP FP (acts G))⦘ ⊆ ⦗E G⦘) at 1 by
        unfolder; ins; desf; splits; auto; rewrite in_filterP_iff in H0; desf.
      arewrite (init_pair ⊆ ⦗fun x => ~ is_f_lwsync (lab G) x⦘ ⨾ init_pair).
      { red; ins. unfolder; eexists; splits; eauto.
        unfold init_pair, is_init, init_label, is_f_lwsync in *; desf.
        cdes WF; cdes WF_ACTS; rewrite LAB_INIT in Heq; desf. }
      cdes WF; cdes WF_SB; rewrite SB_INIT.
      unfolder; unfold is_init, init_label; ins; desf.
      eexists; splits; eauto.
      apply in_filterP_iff; split.
      + act_solver.
      + by red; apply or_not_and; left.
    - apply irreflexive_seqC.
      rewrite !seqA.
      rewrite seq_eqvK.
      apply irreflexive_inclusion with (r' := sb G).
        by basic_solver 42.
      by unfold_wf.
    - apply transitiveI.
      rewrite !seqA.
      arewrite_id ⦗fun a => In a (filterP FP (acts G))⦘ at 2; simpl_rels.
      arewrite_id ⦗fun a => In a (filterP FP (acts G))⦘ at 2; simpl_rels.
      arewrite (sb G ⨾ sb G ⊆ sb G) by unfold_wf.
    - cdes WF; cdes WF_SB.
      rewrite SB_TID at 1.
      case_union_2 _ (init_pair).
      + by unionR left; rewrite <- dom_inter at 1; unfold same_thread; simpl.
      + unionR right; basic_solver 42.
    - cdes WF; cdes WF_SB.
      ins; specialize (SB_TOT i).
      remember (fun a : event => In a (filterP FP (acts G))) as FF.
      remember (fun a : event => tid a = Some i) as T.
      assert (FF ∩₁ T ⊆₁ E G ∩₁ T) by 
        (unfolder; ins; desf; split; auto; red; in_simp).
      assert (is_total (FF ∩₁ T) (sb G)).
        by rewrite H.
      unfolder; ins; desf; apply H0 in NEQ; desf; auto.
    - surround <RW> rf <RW> {G}.
      surround <E> rf <E> {G}.
      rewrite <- FE_RW, <- seqA, <- RW_FE.
      by clear_equivs ⦗RW G⦘.
    - ins.
      assert (In b (acts G)) by
        (unfold FP in IN; apply in_filterP_iff in IN; desf).
      by cdes WF; cdes WF_RF; by apply RF_TOT.
    - surround <RW> mo <RW> {G}.
      surround <E> mo <E> {G}.
      rewrite <- FE_RW, <- seqA, <- RW_FE.
      by clear_equivs ⦗RW G⦘.
    - cdes WF; cdes WF_MO.
      ins; specialize (MO_TOT l).
      assert (H: set_subset (fun a : event =>
         In a (filterP FP (acts G)) /\ is_w (lab G) a /\ loc (lab G) a = Some l) 
        (fun a => E G a /\ W G a /\ loc (lab G) a = Some l)).
        by red; ins; desf; splits; auto; red; in_simp.
      by rewrite H.
    - surround <RW> rmw <RW> {G}.
      arewrite (rmw G ⊆ ⦗E G⦘ ⨾ rmw G ⨾ ⦗E G⦘) by domain_solver.
      rewrite <- FE_RW, <- seqA, <- RW_FE.
      clear_equivs ⦗RW G⦘.
      arewrite (rmw G ⊆ (sb G)|imm) by unfold_wf.
      apply dom_imm.
  }
  { (* consistency_iso G G' *)
    assert {LAB} (G [lab] G').
    assert {MO}   (G ⟪mo⟫ G').
    assert {RF}   (G ⟪rf⟫ G').
    assert {RMW}  (G ⟪rmw⟫ G').
    assert {II0}  (G ⟪ii0⟫ G').
    assert {DETOUR}    (G ⟪detour⟫ G').
    assert {DATA}    (G ⟪data⟫ G').
    assert {ADDR}    (G ⟪data⟫ G').

    assert (SB_ACT: sb G ≡ ⦗E G⦘ ⨾ sb G ⨾ ⦗E G⦘) by domain_solver.
    assert (RW_E: ⦗RW G⦘ ⨾ ⦗E G⦘ ⊆ ⦗RW G⦘) by (unfolder; ins; desf).
    assert (CTRL_E: ctrl G ≡ ctrl G ⨾ ⦗E G⦘) by domain_solver.
    assert (CTRLI_E: ctrl_isync G ≡ ctrl_isync G ⨾ ⦗E G⦘) by domain_solver.
    assert (E_SB_E: sb G ≡ ⦗E G⦘ ⨾ sb G ⨾ ⦗E G⦘) by domain_solver.
    assert (ADDR_RW: addr G ≡ addr G ⨾ ⦗RW G⦘) by domain_solver.
    
    remember ⦗fun a => In a (filterP FP (acts G))⦘ as FF.
    
    assert (FE_F: FF ⨾ ⦗F_sync G⦘ ≡ ⦗E G⦘ ⨾ ⦗F_sync G⦘).
    { subst; red; split; unfolder; ins; desf;
      assert (~ is_f_lwsync (lab G) y) by (red; ins; type_solver);
      eexists; splits; eauto.
      - apply in_filterP_iff in H0; desf.
      - apply in_filterP_iff; splits; auto; unfold FP; red; ins; desf. }
    assert (F_FE: ⦗F_sync G⦘ ⨾ FF ≡ ⦗F_sync G⦘ ⨾ ⦗E G⦘).
    { subst; red; split; unfolder; ins; desf;
      assert (~ is_f_lwsync (lab G) y) by (red; ins; type_solver);
      eexists; splits; eauto.
      - apply in_filterP_iff in H1; desf.
      - apply in_filterP_iff; splits; auto; unfold FP; red; ins; desf. }
    assert (ADDR_E: addr G ≡ addr G ⨾ ⦗E G⦘).
    { red; split.
      + cdes WF; cdes WF_DEPS; cdes WF_SB.
        red; ins; desf.
        assert (sb G x y) by (by apply ADDR_IN_SB).
        assert ((⦗E G⦘ ⨾ sb G ⨾ ⦗E G⦘) x y) by (by apply SB_ACT).
        unfolder in *; desf; eexists; splits; eauto.
      + by clear_equivs ⦗E G⦘. }
    assert (ADDR_SB_E: addr G ⨾ (sb G)^? ≡ addr G ⨾ ⦗E G⦘ ⨾ (sb G)^? ⨾ ⦗E G⦘).
    { red; split.
      + case_refl (sb G).
        - rewrite ADDR_E at 1; basic_solver 42.
        - cdes WF; cdes WF_SB; rewrite SB_ACT at 1.
          basic_solver 42.
      + by clear_equivs ⦗E G⦘. }
    assert (CTRLI: G ⟪(fun g => ctrl_isync g ⨾ ⦗RW g⦘)⟫ G').
    { subst.
      unfold filter_fence_events; autounfold with type_unfold; simpl.
      rewrite CTRLI_E at 1.
      by autounfold with type_unfold in FE_RW; rewrite !seqA, FE_RW. }
    assert (CTRL: G ⟪(fun g => ctrl g ⨾ ⦗RW g⦘)⟫ G').
    { subst.
      unfold filter_fence_events; autounfold with type_unfold; simpl.
      rewrite CTRL_E at 1.
      by autounfold with type_unfold in FE_RW; rewrite !seqA, FE_RW. }
    assert (ADDR_SB: G ⟪(fun g => addr g ⨾ (sb g)^? ⨾ ⦗RW g⦘)⟫ G').
    { subst.
      unfold filter_fence_events; autounfold with type_unfold; simpl.
      red; split.
      - case_refl (sb G).
        + basic_solver 42.
        + arewrite (
          addr G ⨾ sb G ⨾ ⦗is_r (lab G) ∪₁ is_w (lab G)⦘
          ⊆ addr G ⨾ (⦗fun a => In a (filterP FP (acts G))⦘
            ⨾ sb G ⨾ ⦗fun a => In a (filterP FP (acts G))⦘)
            ⨾ ⦗is_r (lab G) ∪₁ is_w (lab G)⦘).
          { rewrite ADDR_RW.
            rewrite !seqA; seq_rewrite RW_FE.
            seq_rewrite FE_RW.
            rewrite !seqA.
            rewrite SB_ACT at 1.
            rewrite !seqA.
            autounfold with type_unfold.
            basic_solver 42. }
        basic_solver 42.
      - basic_solver 42. }
    assert (SYNC: G ⟪sync⟫ G').
    { unfold sync.
      subst; simpl; splits; auto.
      unfold filter_fence_events; autounfold with type_unfold; simpl.
      rewrite !seqA.
      seq_rewrite RW_FE.
      seq_rewrite FE_F.
      rewrite !seqA.
      seq_rewrite F_FE.
      seq_rewrite FE_RW.
      rewrite SB_ACT at 1 2.
      autounfold with type_unfold.
      basic_solver 42. }

    unfold consistency_iso2; splits; auto.
    - (* ci0 *) by unfold ci0; rewrite DETOUR, CTRLI.
    - (* cc0 *) by unfold cc0; rewrite DATA, CTRL, ADDR_SB.
    - (* fence *)
      unfold fence; red; split.
      + unionL.
        * by rewrite SYNC; unionR left.
        * unfold lwsync.
          subst; unfold filter_fence_events; unfold_all; simpl.
          rewrite !seqA; seq_rewrite RW_FE; seq_rewrite FE_RW; seq_rewrite RW_FE;
          seq_rewrite FE_F; rewrite !seqA; seq_rewrite F_FE.
          cdes WF; cdes WF_SB; clear - WF SB_T.
          unfold inclusion, seq, eqv_rel, minus_rel; ins; unfold FP.
          desf.
          destruct (classic(exists a, is_f_sync (lab G) a /\ (sb G) |imm a z1)).
          { (* F_sync immediately before *)
            left.
            desf.
            do 2 (eexists; splits; eauto; try act_solver; try type_solver).
            assert (sb G a z1) by (unfold immediate in H2; desf).
            assert (sb G z a).
            { destruct (classic(I z)).
              - assert (sb G z a \/ sb G a z).
                { cycle_detector;
                  [thread_solver | red; ins; subst; type_solver]. }
                assert (~ sb G a z).
                { red; ins. unfold immediate in H2. destruct H2.
                  by apply (H11 z). }
                desf.
              - cdes WF; cdes WF_SB.
                apply SB_INIT.
                exists a.
                split.
                + red; split; try type_solver.
                  by unfold I in H8; apply NNPP in H8.
                + red; split; auto; act_solver.
            }
            desf.
            exists a; splits; auto.
            eexists; splits; eauto; try act_solver.
            eexists; splits; eauto.
            + eexists; splits; eauto; try act_solver.
            + exists y; splits; auto.
              by apply SB_T with z1.
              eexists; splits; eauto; try act_solver; try type_solver.
          }
          { (* Separate F_lwsync (not filtered out) *)
            right.
            repeat (eexists; splits; eauto); try act_solver; try type_solver;
            apply in_filterP_iff; splits; try act_solver;
            apply not_and_or in H0; apply or_not_and; auto.
          }
      + unionL.
        * by rewrite SYNC; unionR left.
        * unionR right.
          unfold lwsync; subst; unfold filter_fence_events; unfold_all; simpl.
          rewrite !seqA.
          by arewrite_id ⦗fun a => In a (filterP FP (acts G))⦘; simpl_rels.
    - (* sb|loc *)
      subst.
      clear - WF RW_FE FE_RW E_SB_E.
      unfold same_loc, filter_fence_events; unfold_all; simpl.
      rewrite dom_inter.
      arewrite (sb G ∩ same_loc G ≡ ⦗RW G⦘ ⨾ (sb G ∩ same_loc G) ⨾ ⦗RW G⦘) by
        red; split; [| basic_solver 42]; domain_solver.
      seq_rewrite FE_RW; seq_rewrite RW_FE; rewrite E_SB_E at 1.
      rewrite dom_inter2.
      by seq_rewrite seq_eqvC; rewrite !seqA.
   }
Qed.

(* Lemma F.2 *)
Definition A := (fun a => exists b, 
  (⦗R G⦘ ⨾ ((sb G)|imm ∩ (ctrl_isync G)) ⨾ ⦗F G⦘) a b).

Definition removed_ctrli :=
  {|  acts        := G.(acts);
      lab         := G.(lab);
      sb          := G.(sb);
      rf          := G.(rf);
      mo          := G.(mo);
      rmw         := G.(rmw);
      data        := G.(data);
      addr        := G.(addr);
      ctrl        := G.(ctrl);
      ctrl_isync  := G.(ctrl_isync) \ A✕(E G)
  |}.

Lemma R_sbimm_ctrli_F (WF: Wf G) (FG: G' = removed_ctrli): 
  PowerConsistent G' -> PowerConsistent G.
Proof.
  ins.
  Notation "r `" := (r G) (at level 1).
  Notation "r ``" := (r G') (at level 1).
  
  assert {LAB} (G [lab] G').
  assert {SB} (G ⟪sb⟫ G').
  assert {MO} (G ⟪mo⟫ G').
  assert {RF} (G ⟪rf⟫ G').
  assert {RB} (G ⟪rb⟫ G').
  assert {RMW} (G ⟪rmw⟫ G').
  assert {II0} (G ⟪ii0⟫ G').
  assert {CC0} (G ⟪cc0⟫ G').
  assert {SBLOC} (G ⟪sb|loc⟫ G').
  assert {SYNC} (G ⟪sync⟫ G').
  assert {FENCE} (G ⟪fence⟫ G').
  assert {DATA} (G ⟪data⟫ G').
  assert {ADDR} (G ⟪data⟫ G').
  assert {CTRL} (G ⟪ctrl⟫ G').
  assert {DETOUR} (G ⟪detour⟫ G').

  assert (SC2: acyclic ((sb|loc``) ∪ rf`` ∪ rb`` ∪ mo``)) by by cdes H.
  assert (SC: acyclic ((sb|loc`) ∪ rf` ∪ rb` ∪ mo`)) by
    by rewrite SBLOC, RF, RB, MO.
  revert H.
  
  assert (WF2: Wf``).
  { (* WF G' *)
    repeat autounfold with wf_unfold; unnw; splits;
    subst; unfold removed_ctrli; unfold_all; simpl;
    try (by rewrite inclusion_minus_rel; unfold_wf);
    try (by unfold_wf; desf).
    unfolder; ins; desf; splits; auto.
    by unfold_wf; hahn_rewrite CTRLI_RE in H; revert H; basic_solver.
    unfold_wf; rewrite SB_ACT; unfolder; ins; desf; splits.
    by unfold_wf; apply CTRLI_SB; basic_solver.
    tauto.
  }
  apply consistent_alt3; splits; auto.
  
  assert (CTRLI: ctrl_isync`` ⊆ ctrl_isync`)
    by (subst; unfold removed_ctrli; simpl; basic_solver 42).
  
  assert (forall x y,
    (ii`` x y -> ii` x y) /\
    (ic`` x y -> ic` x y) /\
    (ci`` x y -> ci` x y) /\
    (cc`` x y -> cc` x y)).
  { apply ppo_comp_ind; ins; try (by desf; vauto).
    red in H; unfolder in H; desf; vauto.
    apply CI0; red; left; unfolder; basic_solver 42. }

  assert (II: ii`` ⊆ ii`).
    by (unfolder; ins; specialize (H x y); desf; intuition).
  assert (IC: ic`` ⊆ ic`)
    by (unfolder; ins; specialize (H x y); desf; intuition).

  assert (forall x y,
    (ii` x y -> ii`` x y \/ (sb` ⨾ ⦗F`⦘ ⨾ sb`) x y) /\
    (ic` x y -> ic`` x y \/ (sb` ⨾ ⦗F`⦘ ⨾ sb`) x y) /\
    (ci` x y -> ci`` x y \/ (sb` ⨾ ⦗F`⦘ ⨾ sb`) x y) /\
    (cc` x y -> cc`` x y \/ (sb` ⨾ ⦗F`⦘ ⨾ sb`) x y)).
  { clear - WF WF2 FG SC SC2 SB DETOUR.
    assert (II_SB: ii`` ⊆ sb`) by by rewrite SB; apply ppo_components_in_sb.
    assert (IC_SB: ic`` ⊆ sb`) by by rewrite SB; apply ppo_components_in_sb.
    assert (CI_SB: ci`` ⊆ sb`) by by rewrite SB; apply ppo_components_in_sb.
    assert (CC_SB: cc`` ⊆ sb`) by by rewrite SB; apply ppo_components_in_sb.
    assert (SB_T: transitive sb`) by (by cdes WF; cdes WF_SB).
    assert (HELPER: forall a b c,
          (((sb ` ⨾ ⦗F `⦘ ⨾ sb `) a b /\ sb` b c) \/ 
           (sb` a b /\ (sb ` ⨾ ⦗F `⦘ ⨾ sb `) b c) \/
           ((sb ` ⨾ ⦗F `⦘ ⨾ sb `) a b /\ (sb ` ⨾ ⦗F `⦘ ⨾ sb `) b c)) -> 
           (sb ` ⨾ ⦗F `⦘ ⨾ sb `) a c)
    by (intros a b c HH; destruct HH as [HH | [HH | HH]]; clear - HH SB_T;
        unfolder in *; desf; eauto 20 using SB_T).
    apply ppo_comp_ind; ins; try (by desf; vauto);
    try (by destruct H0, H2; only 1: vauto; right;
      let assert_sb := (fun a b => assert (sb` a b) by basic_solver) in 
      try match goal with 
      | _:(ii`` ?a ?b) |- _ => assert_sb a b
      | _:(ic`` ?a ?b) |- _ => assert_sb a b
      | _:(ci`` ?a ?b) |- _ => assert_sb a b
      | _:(cc`` ?a ?b) |- _ => assert_sb a b
      end;
      match goal with 
      | _:(sb` ?a ?b),_:((sb` ⨾ ⦗F`⦘ ⨾ sb`) ?b ?c) |- _ => idtac
      | _:(sb` ?b ?c),_:((sb` ⨾ ⦗F`⦘ ⨾ sb`) ?a ?b) |- _ => idtac
      | _:((sb` ⨾ ⦗F`⦘ ⨾ sb`) ?a ?b),_:((sb` ⨾ ⦗F`⦘ ⨾ sb`) ?b ?c) |- _ => idtac
      end; by eapply HELPER; eauto
    ).
    red in H; unfolder in H; desf.
    - clear - WF H H0.
      destruct (classic(A x)).
      + right.
        red in H1; unfolder in H1.
        desf.
        assert (sb` z y) by (by unfold_wf; apply CTRLI_IN_SB).
        specialize (H6 y); desf; intuition.
        exists b; split; auto.
        exists b; split; [unfolder; auto|].
        assert (sb` y b \/ sb` b y).
        { cycle_detector; only 1: thread_solver.
          red; ins; subst; type_solver. }
        desf.
      + left; unfold removed_ctrli.
        apply CI0; red; unfolder; left; simpl; splits; auto.
        apply or_not_and; auto.
    - (assert (detour` x y) by by apply DETOUR); left; vauto.
  }
  assert (II2: ii` ⊆ ii`` ∪ (sb` ⨾ ⦗F`⦘ ⨾ sb`)) by
    (unfolder; ins; specialize (H0 x y); desf; intuition;
     unfolder in H0; basic_solver 42).
  assert (IC2: ic` ⊆ ic`` ∪ (sb` ⨾ ⦗F`⦘ ⨾ sb`)) by
    (unfolder; ins; specialize (H0 x y); desf; intuition
     unfolder in H2; basic_solver 42).

  assert (PPO: ppo` ⊆ ppo`` ∪ fence`).
  { unfold ppo.
    assert {RR} (G [R] G'); assert {WW} (G [W] G').
    rewrite <- RR, <- WW, ?II2, ?IC2, <- R_sb_F_sb_RW_in_fence.
    unfold RW; rewrite id_union; relsf; unionL; eauto with rel.
    - unionR right -> left; basic_solver 42.
    - unionR right -> right; basic_solver 42. }
  
  assert (PPO2: ppo`` ⊆ ppo`).
  { unfold ppo.
    rewrite II, IC.
    assert {RR} (G [R] G'); assert {WW} (G [W] G').
    by rewrite <- RR, <- WW. }

  assert (HB: G ⟪hb⟫ G') by 
    (unfold hb; split; rewrite <- RF, <- FENCE, ?PPO, ?PPO2; basic_solver 42).

  unfold consistency_iso3; splits; auto.
  - (*prop1*) by unfold prop1; apply prop1_if_rf_fence_hb.
  - (*prop2*) by unfold prop2; apply prop2_if_mo_rf_fence_hb_sync.
Qed.

End Power_Fences.

(******************************************************************************)
(** ** RC11-RMW one-to-one Correspondence *)
(******************************************************************************)
Require Import Classical List Relations Peano_dec.
Require Import Hahn.
Require Import Basic.
Require Import ClassicalDescription IndefiniteDescription.
Require Import RC11_Events RC11_Model RC11_Threads.

Lemma in_helper A (l: list A) (P: A -> Prop) :
   ⦗fun a => In a (filterP P l)⦘ ⊆ ⦗fun a => In a l⦘.
Proof. unfolder; ins; desf; apply in_filterP_iff in H0; desf. Qed.

Lemma case_doma A (r: relation A) (P: A -> Prop) :
  r ≡ ⦗P⦘ ⨾ r ∪ ⦗set_compl P⦘ ⨾ r.
Proof.
  split; [unfolder; ins; tauto | basic_solver].
Qed.

Lemma case_domb A (r: relation A) (P: A -> Prop) :
  r ≡ r ⨾ ⦗P⦘ ∪ r ⨾ ⦗set_compl P⦘.
Proof.
  split; [unfolder; ins; tauto | basic_solver].
Qed.

Lemma case_dom A (r: relation A) (P: A -> Prop) :
  r ≡ ⦗P⦘ ⨾ r ⨾ ⦗P⦘ 
    ∪ ⦗set_compl P⦘ ⨾ r ⨾ ⦗P⦘
    ∪ ⦗P⦘ ⨾ r ⨾ ⦗set_compl P⦘
    ∪ ⦗set_compl P⦘ ⨾ r ⨾ ⦗set_compl P⦘.
Proof.
  split; [unfolder; ins; tauto | basic_solver].
Qed.

Definition NO_RMW_EDGES G := G.(rmw) ⊆ ∅₂.

Section RC11_Correspondence.
Variable G : execution.
Variable G' : execution.

Notation "'acts''" := G'.(acts).
Notation "'lab''" := G'.(lab).
Notation "'loc''" := (loc lab').
Notation "'val''" := (val lab').
Notation "'mod''" := (mod lab').
Notation "'sb''" := G'.(sb).
Notation "'rf''" := G'.(rf).
Notation "'mo''" := G'.(mo).
Notation "'sw''" := G'.(sw).
Notation "'rmw''" := G'.(rmw).
Notation "'rb''" := G'.(rb).
Notation "'hb''" := G'.(hb).
Notation "'data''" := G'.(data).
Notation "'addr''" := G'.(addr).
Notation "'ctrl''" := G'.(ctrl).
Notation "'deps''" := G'.(deps).
Notation "'eco''" := G'.(eco).
Notation "'same_loc''" := G'.(same_loc).
Notation "rel |loc'" := (rel ∩ same_loc') (at level 1).
Notation "'psc''" := G'.(psc).
Notation "'psc_base''" := G'.(psc_base).
Notation "'psc_f''" := G'.(psc_f).
Notation "'scb''" := G'.(scb).
Notation "'sb_neq_loc''" := G'.(sb_neq_loc).

Notation "'E''" := G'.(E).
Notation "'R''" := (R lab').
Notation "'W''" := (W lab').
Notation "'F''" := (F lab').
Notation "'RMW''" := (RMW lab').
Notation "'RW''" := (RW lab').
Notation "'FR''" := (FR lab').
Notation "'FW''" := (FW lab').
Notation "'Na''" := (Only_Na lab').
Notation "'Rlx''" := (Rlx lab').
Notation "'Rel''" := (Rel lab').
Notation "'Acq''" := (Acq lab').
Notation "'Acqrel''" := (Acqrel lab').
Notation "'Sc''" := (Sc lab').

Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
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
Notation "'sb_neq_loc'" := G.(sb_neq_loc).

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
Notation "'R_rmw'" := (dom_rel rmw).
Notation "'W_rmw'" := (codom_rel rmw).

Definition get_rmw_mod (modR: mode_r) (modW: mode_w) : option mode_rw :=
  match modR, modW with
  | Rrlx, Wrlx => Some RWrlx
  | Racq, Wrlx => Some RWacq
  | Rrlx, Wrel => Some RWrel
  | Racq, Wrel => Some RWacqrel
  | Rsc, Wsc => Some RWsc
  | _, _ => None
  end.

Hypothesis NRMW_EVENTS: NO_RMW_EVENTS G.
Hypothesis NRMW_EDGES: NO_RMW_EDGES G'.

Notation "'consistent''" := (consistent G').
Notation "'consistent'" := (consistent G).

Section EDGES_TO_EVENTS.

Hypothesis ACTS: acts' = filterP (fun a => ~ R_rmw a) acts.
Hypothesis RMW_COR: forall r w (RMW_rw : rmw r w), RMW' w.
Hypothesis RMW_COR': forall w (RMW_y: RMW' w),
  exists r l vr vw o or ow,
    rmw r w /\
    lab' w = Armw l vr vw o /\
    lab r = Aload l vr or /\
    lab w = Astore l vw ow /\
    get_rmw_mod or ow = Some o /\
    sb|imm r w /\
    (forall r', rmw r' w -> r' = r).
Hypothesis LAB: forall a (N_Rrmw: ~ W_rmw a), lab' a = lab a.
Hypothesis MO: mo' ≡ mo.
Hypothesis RF: rf' ≡ rf ⨾ ⦗set_compl R_rmw⦘ ∪ rf ⨾ rmw.
Hypothesis SB: sb' ≡ ⦗set_compl R_rmw⦘ ⨾ sb ⨾ ⦗set_compl R_rmw⦘.
Hypothesis DEPS: WfDEPS G'.

Lemma ACTS0a: ⦗E'⦘ ≡ ⦗E'⦘ ⨾ ⦗set_compl R_rmw⦘.
Proof.
  split; [|basic_solver].
  unfold RC11_Model.E; rewrite ACTS; unfolder; ins; desf; in_simp.
Qed.

Lemma ACTS0b: ⦗E'⦘ ≡ ⦗set_compl R_rmw⦘ ⨾ ⦗E'⦘.
Proof.
  split; [|basic_solver].
  unfold RC11_Model.E; rewrite ACTS; unfolder; ins; desf; in_simp.
Qed.

Lemma ACTS1: E' ⊆₁ E.
Proof. unfold RC11_Model.E; rewrite ACTS; unfolder; ins; desf; in_simp. Qed.

Lemma ACTS2a: ⦗E'⦘ ≡ ⦗E⦘ ⨾ ⦗set_compl R_rmw⦘.
Proof.
  split.
  - by rewrite ACTS0a, ACTS1.
  - unfold RC11_Model.E; rewrite ACTS; unfolder; ins; desf; in_simp.
Qed.

Lemma ACTS2b: ⦗E'⦘ ≡ ⦗set_compl R_rmw⦘ ⨾ ⦗E⦘.
Proof.
  split.
  - by rewrite ACTS0b, ACTS1.
  - unfold RC11_Model.E; rewrite ACTS; unfolder; ins; desf; in_simp.
Qed.

Lemma ACTS3: ⦗E⦘ ≡ ⦗E'⦘ ∪ ⦗E⦘ ⨾ ⦗R_rmw⦘.
Proof. rewrite case_domb with (P := R_rmw); rewrite ACTS2a; basic_solver 42. Qed.

Lemma RF': rf ⊆ rf' ∪ rf ⨾ ⦗R_rmw⦘.
Proof.
  rewrite RF; rewrite case_domb with (P := R_rmw) at 1; unionL; basic_solver.
Qed.

Lemma WW: W' ≡₁ W.
Proof.
  split; ins; destruct (classic (W_rmw x)).
  2, 4: by unfold RC11_Events.W in *; specialize (LAB x H0); crewrite LAB.
  all: red in H0; desf; specialize (RMW_COR' x (RMW_COR x0 x H0));
       destruct RMW_COR' as (r & COR); desf; specialize (COR5 r COR); desf;
       solve_type_mismatch.
Qed.

Lemma FF: F' ≡₁ F.
Proof.
  split; ins; destruct (classic (W_rmw x)).
  2, 4: by unfold RC11_Events.F in *; specialize (LAB x H0); crewrite LAB.
  all: red in H0; desf; specialize (RMW_COR' x (RMW_COR x0 x H0));
       destruct RMW_COR' as (r & COR); desf; specialize (COR5 r COR); desf;
       solve_type_mismatch.
Qed.

Lemma WR_MISMATCH a (Wa: W a) (Ra: R a): False.
Proof.
  red in Wa; red in Ra; desf.
  apply (NRMW_EVENTS a); red; desf.
Qed.

Lemma RR: R ⊆₁ R' ∪₁ R_rmw.
Proof.
  unfolder; ins.
  destruct (classic (R_rmw x)); [by right|].
  left.
  destruct (classic (W_rmw x)).
  - red in H1; desf.
    specialize (RMW_COR' x (RMW_COR x0 x H1)).
    destruct RMW_COR' as (r & COR); desf.
    specialize (COR5 x0 H1); desf.
    solve_type_mismatch.
  - specialize (LAB x H1).
    red; red in H; rewrite LAB; desf.
Qed.

Lemma RR2 (WF: Wf G): R' ⊆₁ R ∪₁ W.
Proof.
  unfolder; ins.
  destruct (classic (W_rmw x)).
  - right.
    red in H0; desf.
    cdes WF; cdes WF_RMW; apply RMW_DOM in H0; unfolder in H0; desf.
  - left.
    assert (~ RMW' x).
    { intro; contradict H0.
      specialize (RMW_COR' x H1).
      destruct RMW_COR' as (r & COR); desf.
      red; eexists; eauto. }
    red in H; desf.
    + rewrite (LAB x H0) in *; red; desf.
    + contradict H1; red; desf.
Qed.

Lemma RR3 (WF: Wf G): R' ⊆₁ R ∪₁ RMW'.
Proof.
  unfolder; ins.
  destruct (classic (W_rmw x)).
  - right.
    red in H0; desf.
    by apply RMW_COR with x0.
  - left.
    assert (~ RMW' x).
    { intro; contradict H0.
      specialize (RMW_COR' x H1).
      destruct RMW_COR' as (r & COR); desf.
      red; eexists; eauto. }
    red in H; desf.
    + rewrite (LAB x H0) in *; red; desf.
    + contradict H1; red; desf.
Qed.

Lemma LOC: loc' = loc.
Proof.
  exten; ins.
  unfold RC11_Events.loc.
  destruct (classic (W_rmw x)).
  - red in H; destruct H.
    specialize (RMW_COR' x (RMW_COR x0 x H)).
    destruct RMW_COR' as (r & COR); desf.
  - specialize (LAB x H).
    by rewrite LAB.
Qed.

Lemma SAME_LOC: same_loc' ≡ same_loc.
Proof. by unfold RC11_Model.same_loc; rewrite LOC. Qed.

Lemma REL: Rel' ⊆₁ Rel.
Proof.
  unfolder; ins.
  destruct (classic (W_rmw x)).
  + red in H0; desf.
    specialize (RMW_COR' x (RMW_COR x0 x H0)).
    destruct RMW_COR' as (r & COR); desf.
    specialize (COR5 x0 H0); desf.
    red; red in H.
    unfold get_rmw_mod in *.
    unfold RC11_Events.mod in *.
    desf.
  + red; red in H.
    unfold RC11_Events.mod in *.
    rewrite (LAB x H0) in *.
    desf.
Qed.

Lemma RLX: Rlx' ⊆₁ Rlx.
Proof.
  unfolder; ins.
  destruct (classic (W_rmw x)).
  + red in H0; desf.
    specialize (RMW_COR' x (RMW_COR x0 x H0)).
    destruct RMW_COR' as (r & COR); desf.
    specialize (COR5 x0 H0); desf.
    red; red in H.
    unfold get_rmw_mod in *.
    unfold RC11_Events.mod in *.
    desf.
  + red; red in H.
    unfold RC11_Events.mod in *.
    rewrite (LAB x H0) in *.
    desf.
Qed.

Lemma M_SC: Sc' ⊆₁ Sc.
Proof.
  unfolder; ins.
  destruct (classic (W_rmw x)).
  + red in H0; desf.
    specialize (RMW_COR' x (RMW_COR x0 x H0)).
    destruct RMW_COR' as (r & COR); desf.
    specialize (COR5 x0 H0); desf.
    red; red in H.
    unfold get_rmw_mod in *.
    unfold RC11_Events.mod in *.
    desf.
  + red; red in H.
    unfold RC11_Events.mod in *.
    rewrite (LAB x H0) in *.
    desf.
Qed.

Lemma F_ACQ (WF: Wf G): F ∩₁ Acq' ⊆₁ F ∩₁ Acq.
Proof.
  unfolder; ins; desf; split; auto.
  assert (~ W_rmw x).
  { intro.
    assert (W x).
    { cdes WF; cdes WF_RMW; red in H1.
      desf; apply RMW_DOM in H1; unfolder in H1; desf. }
    solve_type_mismatch. 
  }
  red; red in H0.
  unfold RC11_Events.mod in *; rewrite (LAB x H1) in *; desf.
Qed.

Lemma R_ACQ (WF: Wf G): (R ∩₁ Acq' ⊆₁ R ∩₁ Acq).
Proof.
  unfolder; ins; desf; split; auto.
  assert (~ W_rmw x).
  { intro.
    assert (W x).
    { cdes WF; cdes WF_RMW; red in H1.
      desf; apply RMW_DOM in H1; unfolder in H1; desf. }
    by apply WR_MISMATCH with x.
  }
  red; red in H0.
  unfold RC11_Events.mod in *; rewrite (LAB x H1) in *; desf.
Qed.

Lemma N_Wrmw_Init l (SB_TID: sb ⊆ sb∙ ∪ init_pair): (~ W_rmw (Init l)).
Proof.
  remember (Init l) as I.
  intro RMW_xI; red in RMW_xI; desc.
  specialize (RMW_COR' I (RMW_COR x I RMW_xI)).
  destruct RMW_COR' as (r & COR); desf.
  specialize (COR5 x); intuition; desf.
  unfolder in COR4; desc.
  apply SB_TID in COR4.
  unfolder in COR4; desf.
  - red in COR6; desf.
  - red in COR4; desf; apply COR6; red; desf.
Qed.

Lemma RF_Rrmw (WF: Wf G): rf ⊆ ⦗set_compl R_rmw⦘ ⨾ rf.
Proof.
  cdes WF; cdes WF_RF.
  arewrite (rf ⊆ ⦗W⦘ ⨾ rf) by rewrite RF_DOM at 1; basic_solver.
  arewrite (W ⊆₁ set_compl R_rmw).
  { unfolder; ins; intro Rrmw_x.
    red in Rrmw_x; desf.
    specialize (RMW_COR' y (RMW_COR x y Rrmw_x)).
    destruct RMW_COR' as (r & COR).
    desf. specialize (COR5 x Rrmw_x). desf.
    solve_type_mismatch. }
  done.
Qed.

Proposition edges_to_events : consistent -> consistent'.
Proof.
  ins; cdes H; red; unnw; split.
  (* Wf *) 
  { cdes WF; red; splits; unnw.
    - (* WfACTS *) cdes WF_ACTS; red; splits; unnw.
      + (* ACTS_INIT *)
        rewrite ACTS.
        ins; specialize (ACTS_INIT l).
        apply in_filterP_iff; splits; auto.
        unfold dom_rel.
        intro; desf.
        apply WR_MISMATCH with (Init l).
        * red; rewrite (LAB_INIT l); desf.
        * cdes WF_RMW; apply RMW_DOM in H0; unfolder in H0; desf.
      + cdes WF; cdes WF_ACTS; cdes WF_SB.
        ins; specialize (LAB_INIT l).
        by rewrite (LAB (Init l) (N_Wrmw_Init l SB_TID)).
    - (* WfSB *) cdes WF_SB; red; splits; unnw.
      + (* SB_ACT *)
        rewrite SB; rewrite SB_ACT at 1; rewrite !seqA.
        seq_rewrite <- ACTS2b; seq_rewrite <- ACTS2a.
        by seq_rewrite <- ACTS0a; seq_rewrite <- ACTS0b.
      + (* SB_INIT *)
        rewrite SB, ACTS2a.
        arewrite (init_pair ⊆ ⦗set_compl R_rmw⦘ ⨾ init_pair).
        { unfold init_pair, is_init; unfolder; ins; desf; splits; auto.
          intro.
          apply WR_MISMATCH with (Init l).
          - cdes WF_ACTS; red; rewrite (LAB_INIT l); desf.
          - red in H2; cdes WF_RMW; apply RMW_DOM in H2; unfolder in H2; desf.
        }
        by hahn_frame; rewrite SB_INIT.
      + (* SB_IRR *)
        rewrite SB.
        by clear_equivs ⦗set_compl R_rmw⦘.
      + (* SB_T *)
        rewrite SB.
        apply transitiveI.
        arewrite_id ⦗set_compl R_rmw⦘ at 2; arewrite_id ⦗set_compl R_rmw⦘ at 2.
        relsf.
      + (* SB_TID *)
        rewrite SB.
        rewrite SB_TID at 1.
        case_union_2 _ _; [unionR left | unionR right]; basic_solver.
      + (* SB_TOT *)
        ins; specialize (SB_TOT i).
        rewrite SB.
        arewrite (E' ⊆₁ E' ∩₁ (set_compl R_rmw))
          by (unfold RC11_Model.E; rewrite ACTS; unfolder; ins; desf; in_simp).
        red; ins.
        assert (sb a b \/ sb b a).
        { apply SB_TOT; unfolder in IWa; unfolder in IWb; desf;
          by split; auto; apply ACTS1. }
        desf; [left | right]; unfolder in *; desf.
    - (* WfRMW *) cdes WF_RMW; red; splits; unnw.
      + (* RMW_DOM *) by red in NRMW_EDGES; rewrite NRMW_EDGES at 1.
      + (* RMW_LOC *) by red in NRMW_EDGES; rewrite NRMW_EDGES at 1.
      + (* RMW_MOD *) by red in NRMW_EDGES; ins; apply NRMW_EDGES in RMW_AB.
      + (* RMW_IMM *) by red in NRMW_EDGES; rewrite NRMW_EDGES at 1.
    - (* WfRF *) cdes WF_RF; red; splits; unnw.
      + (* RF_ACT *)
        rewrite RF; unionL.
        * rewrite RF_ACT at 1.
          relsf; unionR left.
          rewrite !seqA; rewrite ACTS2a at 1; rewrite ACTS2b at 1.
          seq_rewrite seq_eqvK; rewrite seq_eqvC at 1.
          rewrite (RF_Rrmw WF) at 1.
          by rewrite !seqA.
        * relsf; unionR right.
          rewrite RF_ACT at 1; arewrite_id ⦗E⦘ at 2; simpl_rels.
          arewrite (rmw ⊆ rmw ⨾ ⦗E⦘) at 1.
          { unfolder; ins; split; auto.
            cdes WF_RMW; apply RMW_IMM in H0; unfolder in H0; desf.
            cdes WF_SB; apply SB_ACT in H0; unfolder in H0; desf. }
          rewrite ACTS2a at 1; rewrite ACTS2b at 1; rewrite (RF_Rrmw WF) at 1.
          arewrite (rmw ⊆ rmw ⨾ ⦗set_compl R_rmw⦘) at 2.
          { arewrite (rmw ⊆ rmw ⨾ ⦗W⦘)
              by cdes WF_RMW; rewrite RMW_DOM at 1; basic_solver.
            arewrite (W ⊆₁ set_compl R_rmw).
            { unfolder; ins; intro Rrmw_x.
              red in Rrmw_x; desf.
              specialize (RMW_COR' y (RMW_COR x y Rrmw_x)).
              destruct RMW_COR' as (r & COR).
              desf. specialize (COR5 x Rrmw_x). desf.
              solve_type_mismatch. }
            done.
          }
          done.
      + (* RF_IRR *)
        rewrite RF; unionL; [by clear_equivs ⦗set_compl R_rmw⦘ |].
        arewrite (rmw ⊆ sb) by cdes WF_RMW; rewrite RMW_IMM; eauto with rel.
        clear - NTA.
        rotate; red; repeat red in NTA.
        ins; apply (NTA x).
        unfolder in H; desf; apply t_trans with z; vauto.
      + (* RF_DOM *)
        rewrite RF, WW.
        relsf. unionL; [unionR left | unionR right].
        * rewrite RF_DOM at 1.
          rewrite RR, id_union.
          basic_solver.
        * arewrite (rf ⊆ ⦗W⦘ ⨾ rf) by rewrite RF_DOM at 1; basic_solver.
          hahn_frame.
          unfolder; ins; split; auto; red.
          specialize (RMW_COR x y H0).
          red in RMW_COR; desf.
      + (* RF_LOC *)
        rewrite RF, LOC.
        apply funeq_union.
        * by clear_equivs ⦗set_compl R_rmw⦘.
        * apply funeq_seq; auto.
          by cdes WF_RMW.
      + (* RF_VAL *)
        assert (RF_HELPER: forall a b, rf a b -> valw lab' a = valr lab' b).
        { intros a b RF_ab; specialize (RF_VAL a b RF_ab).
          assert (~ W_rmw b).
          { intro Wrmw_b.
            apply WR_MISMATCH with b.
            - red in Wrmw_b; desf; cdes WF_RMW.
              apply RMW_DOM in Wrmw_b; unfolder in Wrmw_b; desf.
            - apply RF_DOM in RF_ab; unfolder in RF_ab; desf. }
          destruct (classic (W_rmw a)).
          - red in H1; desf.
            assert (Lb: valr lab' b = valr lab b).
            { assert (LABb: lab' b = lab b) by by apply LAB.
              by unfold RC11_Events.valr in *; rewrite LAB. }
            assert (La: valw lab' a = valw lab a).
            { specialize (RMW_COR' a (RMW_COR x a H1)).
              destruct RMW_COR' as (r & COR); desf.
              specialize (COR5 x H1); desf.
              unfold RC11_Events.valw in *; desf. }
            by rewrite Lb, La.
          - assert (LABa: lab' a = lab a) by by apply LAB.
            assert (LABb: lab' b = lab b) by by apply LAB.
            unfold RC11_Events.valr, RC11_Events.valw.
            by rewrite LABa, LABb. }
        intros a b RF_ab.
        apply RF in RF_ab; unfolder in RF_ab; desf; auto.
        assert (T: valw lab' a = valr lab' z) by by apply RF_HELPER.
        rewrite T.
        assert (Lz: lab' z = lab z).
        { apply LAB.
          intro Wrmw_z.
          apply WR_MISMATCH with z.
          - red in Wrmw_z; desf; cdes WF_RMW.
            apply RMW_DOM in Wrmw_z; unfolder in Wrmw_z; desf.
          - apply RF_DOM in RF_ab; unfolder in RF_ab; desf. }
        specialize (RMW_COR' b (RMW_COR z b RF_ab0)).
        destruct RMW_COR' as (r & COR); desf.
        specialize (COR5 z RF_ab0); desf.
        unfold RC11_Events.valr, RC11_Events.valw in *.
        rewrite Lz; desf.
      + (* RF_FUN *)
        rewrite RF.
        red in RF_FUN.
        apply functional_union.
        * red.
          intros x y z RF_yx RF_zx.
          unfolder in RF_yx; unfolder in RF_zx; desf.
          by apply RF_FUN with x.
        * red; unfolder; ins; desf.
          assert (sb z1 x) by by cdes WF_RMW; apply RMW_IMM.
          assert (sb z0 x) by by cdes WF_RMW; apply RMW_IMM.
          destruct (classic (z1 = z0)).
          { (* z1 = z0 *) by subst; apply RF_FUN with z0. }
          assert (sb z1 z0 \/ sb z0 z1).
          { apply st_implies_sb; auto.
            apply st_trans with x.
            - apply sb_not_init_implies_st with G; auto.
              intro T.
              apply WR_MISMATCH with z1.
              + red in T. desf.
                cdes WF_ACTS; red.
                rewrite (LAB_INIT l); desf.
              + cdes WF_RMW; apply RMW_DOM in H3; unfolder in H3; desf.
            - apply st_inv, sb_not_init_implies_st with G; auto.
              intro T.
              apply WR_MISMATCH with z0.
              + red in T. desf.
                cdes WF_ACTS; red.
                rewrite (LAB_INIT l); desf.
              + cdes WF_RMW; apply RMW_DOM in H2; unfolder in H2; desf.
            - cdes WF_SB; apply SB_ACT in H4; unfolder in H4; desf.
            - cdes WF_SB; apply SB_ACT in H5; unfolder in H5; desf.
          }
          cdes WF_RMW; exfalso.
          unfolder in RMW_IMM; desf.
          -- (* sb z1 z0 *)
             specialize (RMW_IMM z1 x H3); desf.
             apply RMW_IMM0 with z0; auto.
          -- (* sb z0 z1 *)
             specialize (RMW_IMM z0 x H2); desf.
             apply RMW_IMM0 with z1; auto.
        * unfold dom_rel; ins; desf.
          apply WR_MISMATCH with x.
          -- unfolder in H1; desf; cdes WF_RMW.
             apply RMW_DOM in H2; unfolder in H2; desf.
          -- unfolder in H0; desf.
             apply RF_DOM in H0; unfolder in H0; desf.
      + (* RF_TOT *)
        ins.
        destruct (classic (W_rmw b)).
        * red in H0; desf.
          specialize (RMW_COR' b (RMW_COR x b H0)).
          destruct RMW_COR' as (r & COR); desf.
          specialize (COR5 x H0); desf.
          assert (Er: E r).
          { cdes WF_SB; cdes WF_RMW.
            apply RMW_IMM in H0; red in H0; desf.
            apply SB_ACT in H0; unfolder in H0; desf. }
          assert (Rr: R r) by (red; desf).
          specialize (RF_TOT r Er Rr); desf.
          exists a; hahn_rewrite RF.
          right; exists r; split; auto.
        * destruct (classic (R_rmw b)).
          { red in IN. rewrite ACTS in IN.
            apply in_filterP_iff in IN; desf. }
          assert (Rb: R b) by by red; red in READ; rewrite <- (LAB b H0).
          apply ACTS1 in IN; specialize (RF_TOT b IN Rb); desf.
          exists a; hahn_rewrite RF.
          left; basic_solver.
    - (* WfMO *) cdes WF_MO; red; splits; unnw; try by rewrite MO, ?WW, ?LOC.
      + (* MO_ACT *)
        assert (MIS: ⦗R_rmw⦘ ⨾ ⦗W⦘ ⊆ ∅₂).
        { unfolder; ins; desf.
          red in H1; desf.
          specialize (RMW_COR' y0 (RMW_COR y y0 H1)).
          destruct RMW_COR' as (r & COR); desf.
          red in H2.
          specialize (COR5 y H1); desf. }
        rewrite MO.
        rewrite MO_ACT at 1.
        rewrite ACTS3.
        clear_equivs ⦗E⦘.
        relsf; unionL; try done; arewrite (mo ⊆ ⦗W⦘ ⨾ mo ⨾ ⦗W⦘) at 1.
        2: rewrite seq_eqvC with (doma := W).
        all: sin_rewrite MIS; basic_solver.
      + (* MO_TOT *)
        ins; specialize (MO_TOT l).
        crewrite MO.
        arewrite (E' ∩₁ W' ∩₁ (fun a : event => loc' a = Some l) ⊆₁ 
                  E ∩₁ W ∩₁ (fun a : event => loc a = Some l)).
          by rewrite WW, ACTS1, LOC.
        done.
    - (* WfDEPS *) done.
  }
  (* Consistent *)
  assert (SW: sw' ⊆ sw ∪ sw ⨾ rmw).
  { unfold RC11_Model.sw, RC11_Model.release, RC11_Model.rs, RC11_Model.useq.
    rewrite WW, FF, SAME_LOC, REL, RLX, (F_ACQ WF).
    rewrite ACTS1 at 1.
    arewrite (sb' ⊆ sb) by crewrite SB; basic_solver.
    arewrite (⦗RMW⦘ ≡ ∅₂) by arewrite (RMW ≡₁ ∅₁); basic_solver.
    arewrite (rmw' ⊆ ∅₂).
    rels.
    arewrite (rf' ⨾ ⦗RMW'⦘ ⊆ rf ⨾ rmw).
    { arewrite (rf' ⊆ rf ∪ rf ⨾ rmw) by crewrite RF; basic_solver.
      case_union_2 _ _; [| basic_solver].
      arewrite (rf ⊆ rf ⨾ ⦗R⦘)
        by cdes WF; cdes WF_RF; rewrite RF_DOM at 1; basic_solver.
      arewrite (RMW' ⊆₁ W).
      { unfolder; intros x RMW_x.
        specialize (RMW_COR' x RMW_x).
        destruct RMW_COR' as (r & COR); desf.
        red; desf. }
      unfolder; ins; desf.
      by exfalso; apply WR_MISMATCH with y.
    }
    rewrite !seq_union_r; unionL.
    - arewrite (rf' ⨾ ⦗R' ∩₁ Acq'⦘ ⊆ rf ⨾ ⦗R ∩₁ Acq⦘ ∪ rf ⨾ ⦗R ∩₁ Acq⦘ ⨾ rmw).
      { arewrite (rf' ⊆ rf ∪ rf ⨾ rmw) by crewrite RF; basic_solver.
        case_union_2 _ _; [unionR left | unionR right].
        - rewrite (RR2 WF).
          arewrite (rf ⊆ rf ⨾ ⦗R⦘)
            by cdes WF; cdes WF_RF; rewrite RF_DOM at 1; basic_solver.
          rewrite !set_inter_union_l, !id_union.
          relsf; unionL.
          + rewrite (R_ACQ WF); basic_solver.
          + by unfolder; ins; desf; exfalso; apply WR_MISMATCH with y.
        - rewrite !seqA.
          arewrite (rmw ⨾ ⦗R' ∩₁ Acq'⦘ ⊆ rmw ⨾ ⦗RMW' ∩₁ Acq'⦘).
          { rewrite (RR3 WF).
            arewrite (rmw ⊆ rmw ⨾ ⦗W⦘)
              by cdes WF; cdes WF_RMW; rewrite RMW_DOM at 1; basic_solver.
            rewrite !set_inter_union_l, !id_union.
            relsf; unionL.
            - by unfolder; ins; desf; exfalso; apply WR_MISMATCH with y.
            - basic_solver.
          }
          unfolder; ins; desf.
          specialize (RMW_COR' y H2).
          destruct RMW_COR' as (r & COR); desf.
          eexists; splits; eauto.
          + cdes WF; cdes WF_RMW; apply RMW_DOM in H1; unfolder in H1; desf.
          + specialize (COR5 z H1); subst; red in H3.
            unfold get_rmw_mod in COR3; unfold RC11_Events.mod in H3.
            desf; red; unfold RC11_Events.mod; desf.
      }
      remember (⦗W ∩₁ Rel⦘ ∪ ⦗F ∩₁ Rel⦘ ⨾ sb) as r.
      case_union_2 _ _; [unionR left | unionR right]; unionR left; by hahn_frame.
    - arewrite (rf' ⊆ rf ∪ rf ⨾ rmw) by crewrite RF; basic_solver.
      case_union_2 _ (rf ⨾ rmw).
      + arewrite (rf ⨾ ⦗R' ∩₁ Rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⊆
                  rf ⨾ ⦗R ∩₁ Rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ Acq⦘).
        { rewrite (RR2 WF).
          arewrite (rf ⊆ rf ⨾ ⦗R⦘)
            by cdes WF; cdes WF_RF; rewrite RF_DOM at 1; basic_solver.
          rewrite !set_inter_union_l, !id_union.
          relsf; unionL.
          - basic_solver 42.
          - arewrite (⦗R⦘ ⨾ ⦗W ∩₁ Rlx⦘ ⊆ ∅₂)
              by unfolder; ins; desf; apply WR_MISMATCH with y.
            basic_solver 42.
        }
        by unionR left -> right.
      + rewrite !seqA.
        arewrite (rmw ⨾ ⦗R' ∩₁ Rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ Acq⦘ ⊆
                  rmw ⨾ ⦗W ∩₁ Rlx⦘ ⨾ sb ⨾ ⦗F ∩₁ Acq⦘).
        { rewrite (RR2 WF).
          arewrite (rmw ⊆ rmw ⨾ ⦗W⦘)
            by cdes WF; cdes WF_RMW; rewrite RMW_DOM at 1; basic_solver.
          rewrite !set_inter_union_l, !id_union.
          relsf; unionL.
          - arewrite (⦗W⦘ ⨾ ⦗R ∩₁ Rlx⦘ ⊆ ∅₂)
              by unfolder; ins; desf; apply WR_MISMATCH with y.
            basic_solver 42.
          - basic_solver 42.
        }
        arewrite (rmw ⨾ ⦗W ∩₁ Rlx⦘ ⊆ ⦗R ∩₁ Rlx⦘ ⨾ rmw).
        { cdes WF; cdes WF_RMW.
          unfolder; ins; desf.
          specialize (RMW_MOD x y H0).
          splits; auto.
          - apply RMW_DOM in H0; unfolder in H0; desf.
          - solve_mode_mismatch. }
        arewrite (rmw ⨾ sb ⊆ sb).
        { cdes WF; cdes WF_RMW; cdes WF_SB.
          rewrite RMW_IMM.
          basic_solver 42. }
        eauto with rel.
  }
  assert (RB: rb' ⊆ rb ∪ mo).
  { arewrite (rb ≡ rf⁻¹ ⨾ mo) by rewrite NRMW_implies_original_rb.
    unfold RC11_Model.rb.
    rewrite MO.
    arewrite (rf' ⊆ rf ∪ rf ⨾ rmw) by crewrite RF; basic_solver.
    rewrite transp_union.
    unfolder; ins; desf; [basic_solver|].
    assert (Ex: E' x).
    { red; rewrite ACTS; apply in_filterP_iff; split.
      - cdes WF; cdes WF_RMW; apply RMW_IMM in H3; unfolder in H3; desf.
        cdes WF_SB; apply SB_ACT in H3; unfolder in H3; desf.
      - intro.
        red in H4; desf.
        apply WR_MISMATCH with x; cdes WF; cdes WF_RMW.
        + apply RMW_DOM in H3; unfolder in H3; desf.
        + apply RMW_DOM in H4; unfolder in H4; desf.
    }
    assert (NEQ: x <> y) by (apply not_and_or in H1; desf); clear H1 Ex.
    assert (MO_zx: mo z x) by (apply rf_rmw_mo; auto; basic_solver).
    assert (N_MO_yx: ~ mo y x).
    { intro MO_yx.
      apply AT with z0.
      exists y; split.
      - by apply NRMW_implies_original_rb; auto; exists z.
      - exists x; split; auto.
    }
    assert (MOS: mo x y \/ mo y x).
    { cdes WF; cdes WF_MO.
      assert (W z) by (apply MO_DOM in H2; unfolder in H2; desf).
      assert (exists lz, loc z = Some lz).
      { case_eq (loc z); ins; eauto.
        red in H3; unfold RC11_Events.loc in H4; solve_type_mismatch. }
      destruct H4 as [lz L_z].
      apply MO_TOT with lz; auto; unfolder; splits.
      3, 6: by rewrite <- L_z; symmetry; apply MO_LOC.
      - apply MO_ACT in MO_zx; unfolder in MO_zx; desf.
      - apply MO_DOM in MO_zx; unfolder in MO_zx; desf.
      - apply MO_ACT in H2; unfolder in H2; desf.
      - apply MO_DOM in H2; unfolder in H2; desf.
    }
    desf; auto.
  }
  assert (ECO: eco' ⊆ eco).
  { unfold RC11_Model.eco.
    rewrite RB.
    arewrite (rf' ⊆ rf ∪ rf ⨾ rmw) by crewrite RF; basic_solver.
    rewrite MO, !crE; relsf; rewrite <- !unionA; unionL.
    all: rels; eauto with rel; rewrite rf_rmw_mo; auto; eauto with rel.
    1, 3: cdes WF; cdes WF_MO; relsf; eauto with rel.
    rewrite (rb_seq_mo WF NRMW_EVENTS); eauto with rel.
  }
  assert (HB: hb' ⊆ hb).
  { unfold RC11_Model.hb at 1.
    arewrite (sb' ⊆ sb) by crewrite SB; basic_solver.
    rewrite SW.
    arewrite (sw ⨾ rmw ⊆ hb) by rewrite sw_in_hb, rmw_in_sb, sb_in_hb, hb_hb.
    rewrite sw_in_hb, sb_in_hb; relsf.
  }
  splits.
  - (* Coherence *)
    red; red in COH.
    by rewrite HB, ECO.
  - (* Atomicity *) red; arewrite (rmw' ⊆ ∅₂); rels.
  - (* Atomicity2 *)
    red; red in AT2.
    rewrite MO.
    arewrite (rf' ⊆ rf ∪ rf ⨾ rmw) by crewrite RF; basic_solver.
    rewrite transp_union.
    relsf; unionL; auto.
    unfolder; ins; desf.
    apply AT with z1.
    exists z; split.
    + by apply NRMW_implies_original_rb; auto; exists x.
    + exists z0; split; auto.
  - (* SC *)
    red; red in SC.
    unfold RC11_Model.psc, RC11_Model.psc_base, RC11_Model.psc_f,
      RC11_Model.scb in *.
    arewrite (sb' ⊆ sb) by crewrite SB; basic_solver.
    rewrite MO, SAME_LOC, FF, M_SC, HB, ECO, RB.
    arewrite (sb_neq_loc' ⊆ sb_neq_loc).
    { unfold RC11_Model.sb_neq_loc.
      rewrite SAME_LOC, SB.
      unfolder; ins; desf; split; auto.
      apply or_not_and; right.
      repeat (apply not_and_or in H1; desf).
    }
    by arewrite (sb ∪ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ∪ hb |loc ∪ mo ∪ (rb ∪ mo) ⊆
                (sb ∪ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ∪ hb |loc ∪ mo ∪ rb)).
  - (* No-thin-air *)
    red; red in NTA.
    arewrite (sb' ⊆ sb) by crewrite SB; basic_solver.
    arewrite (rf' ⊆ rf ∪ rf ⨾ rmw) by crewrite RF; basic_solver.
    clear - WF NTA; rewrite (rmw_in_sb WF); red.
    arewrite ((sb ∪ (rf ∪ rf ⨾ sb))⁺ ⊆ (sb ∪ rf)⁺)
      by eauto 42 with rel rel_full.
Qed.

End EDGES_TO_EVENTS.

Section EVENTS_TO_EDGES.

Variable f: event -> event.
Hypothesis F_new: forall a, ~ In (f a) acts'.
Hypothesis F_fun: forall a b, f a = f b -> a = b.
Hypothesis F_tid: forall a, tid a = tid (f a).
Hypothesis F_read: forall a, R (f a).

Definition RMW_list := filterP RMW' acts'.
Definition newR := map f RMW_list.
Definition New_R := fun a => In a newR.
Hypothesis ACTS: acts = acts' ++ newR.

Hypothesis RMW_COR_R: forall r (NewR_r : New_R r), exists w, rmw r w.
Hypothesis RMW_COR_W: forall w (RMW_w : RMW' w), exists r, rmw r w.
Hypothesis RMW_COR: forall r w (RMW_rw: rmw r w),
  exists l vr vw o or ow,
    f w = r /\
    New_R r /\
    RMW' w /\
    lab' w = Armw l vr vw o /\
    lab r = Aload l vr or /\
    lab w = Astore l vw ow /\
    get_rmw_mod or ow = Some o /\
    sb|imm r w /\
    (forall r', rmw r' w -> r' = r) /\
    (forall w', rmw r w' -> w' = w).
Hypothesis LAB: forall a (N_RMW: ~ RMW' a), lab a = lab' a.

Hypothesis MO: mo ≡ mo'.
Hypothesis RF: rf ≡ rf' ⨾ ⦗set_compl RMW'⦘ ∪ rf' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹.
Hypothesis Rmw: rmw = (fun r w => RMW w /\ r = f w).
Hypothesis SB: sb ≡ sb' ∪ sb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹.

Hypothesis DEPS: WfDEPS G.

Lemma RMW_implies_not_init
  (LAB_INIT: forall l : location, lab' (Init l) = init_label l):
  forall a, RMW' a -> ~ is_init a.
Proof.
  intros a RMW_a INIT_a.
  unfold is_init in INIT_a; desf.
  red in RMW_a; rewrite (LAB_INIT l) in RMW_a; desf.
Qed.

Lemma sb_implies_not_init (SB_TID: sb' ⊆ sb'∙ ∪ init_pair) a b (SB_ab: sb' a b): 
  ~ is_init b.
Proof.
  clear - SB_TID SB_ab.
  apply SB_TID in SB_ab.
  unfolder in SB_ab; desf; unfold same_thread, tid, init_pair in *; desf.
Qed.

Lemma EE: E ≡₁ E' ∪₁ New_R.
Proof.
  unfold RC11_Model.E; rewrite ACTS.
  by unfolder; ins; rewrite in_app_iff.
Qed.

Lemma set_union_inter X (A B: X -> Prop): (A ∪₁ B) \₁ B ⊆₁ A.
Proof. unfolder; ins; desf. Qed.

Lemma E_No_NewR: E' ≡₁ E' \₁ New_R.
Proof.
  unfolder; split; ins; splits; desf.
  intro NR; red in NR; unfold RMW_list, newR in NR.
  apply in_map_iff in NR; desf.
  apply in_filterP_iff in NR0; desf.
  red in H; specialize (F_new x0); desf.
Qed.

Lemma EE': E' ≡₁ E \₁ New_R.
Proof.
  rewrite EE, E_No_NewR.
  unfolder; ins; split; ins; splits; desf; auto.
Qed.

Lemma New_R_seq_E: ⦗New_R⦘ ⨾ ⦗E'⦘ ⊆ ∅₂.
Proof. rewrite EE'; basic_solver. Qed.

Lemma rmw_transp_seq_sb (SB_ACT: sb' ⊆ ⦗E'⦘ ⨾ sb' ⨾ ⦗E'⦘):
  rmw⁻¹ ⨾ sb' ⊆ ∅₂.
Proof.
  arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗New_R⦘) at 1.
  { unfolder; intros w r RMW_rw; desf; split; auto.
    specialize (RMW_COR r w RMW_rw).
    destruct RMW_COR as (l & COR); desf.
  }
  arewrite_false (⦗New_R⦘ ⨾ sb').
  { rewrite SB_ACT.
    arewrite_false (⦗New_R⦘ ⨾ ⦗E'⦘); try apply New_R_seq_E.
    basic_solver.
  }
  basic_solver.
Qed.

Lemma sb_not_init_implies_st (SB_TID: sb' ⊆ sb'∙ ∪ init_pair)
  a b (SB_ab: sb' a b) (N_INIT: ~ is_init a):
  same_thread a b.
Proof.
  eapply SB_TID in SB_ab.
  unfold init_pair in *.
  generalize SB_ab, SB_TID; basic_solver.
Qed.

Lemma SB_incl: sb' ⊆ sb.
Proof. rewrite SB; eauto with rel. Qed.

Lemma NewR_in_E: New_R ⊆₁ E.
Proof.
  unfolder; intros r NewR_r.
  red in NewR_r; unfold newR, RMW_list in *.
  rewrite ACTS; apply in_app_iff; auto.
Qed.

Lemma NewR_in_R: New_R ⊆₁ R.
Proof.
  unfolder; intros r NewR_r.
  specialize (RMW_COR_R r NewR_r); destruct RMW_COR_R as [w RMW_rw].
  specialize (RMW_COR r w RMW_rw).
  destruct RMW_COR as (l & COR); desf.
Qed.

Lemma RMW_in_W: RMW' ⊆₁ W.
Proof.
  unfolder; intros w RMW_w.
  specialize (RMW_COR_W w RMW_w); destruct RMW_COR_W as [r RMW_rw].
  specialize (RMW_COR r w RMW_rw).
  destruct RMW_COR as (l & COR); desf.
  red; desf.
Qed.

Lemma RMW_in_E (SB_ACT: sb ⊆ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘): RMW' ⊆₁ E'.
Proof.
  unfolder; intros w RMW_w.
  assert (NewR_in_R := NewR_in_R).
  assert (RMW_in_W := RMW_in_W).
  specialize (RMW_COR_W w RMW_w); destruct (RMW_COR_W) as [r RMW_rw].
  specialize (RMW_COR r w RMW_rw).
  destruct RMW_COR as (l & COR); desf.
  apply EE'; unfolder; split.
  - unfolder in COR6; desf; apply SB_ACT in COR6; unfolder in COR6; desf.
  - intro NewR_w.
    apply NewR_in_R in NewR_w.
    apply RMW_in_W in COR1.
    solve_type_mismatch.
Qed.

Lemma NewR_implies_sb_to_RMW (SB_ACT: sb ⊆ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘) r (NewR_r: New_R r):
  exists w, RMW' w /\ rmw r w /\ sb|imm r w /\ E' w.
Proof.
  assert (NewR_in_R := NewR_in_R).
  assert (RMW_in_W := RMW_in_W).
  specialize (RMW_COR_R r NewR_r); destruct (RMW_COR_R) as [w RMW_rw].
  specialize (RMW_COR r w RMW_rw).
  destruct RMW_COR as (l & COR); desf.
  exists w; splits; auto.
  unfolder in COR6; desf.
  apply EE'; unfolder; split.
  - apply SB_ACT in COR6; unfolder in COR6; desf.
  - intro NewR_w.
    apply NewR_in_R in NewR_w.
    apply RMW_in_W in COR1.
    solve_type_mismatch.
Qed.

Lemma WW': W ≡₁ W'.
Proof.
  red; intros w.
  destruct (classic (RMW' w)) as [RMW_w | N_RMW_w].
    by split; intro W_w; [red; red in RMW_w; desf | by apply RMW_in_W].
  unfold RC11_Events.W.
  by rewrite (LAB w N_RMW_w).
Qed.

Lemma LOC': loc = loc'.
Proof.
  exten; ins.
  unfold RC11_Events.loc.
  destruct (classic (RMW' x)) as [RMW_x | N_RMW_x].
  - specialize (RMW_COR_W x RMW_x).
    destruct RMW_COR_W as [r RMW_rx].
    specialize (RMW_COR r x RMW_rx).
    destruct RMW_COR as (l & COR); desf.
  - by rewrite (LAB x N_RMW_x).
Qed.

Lemma SAME_LOC': same_loc ≡ same_loc'.
Proof. by unfold RC11_Model.same_loc; rewrite LOC'. Qed.

Lemma RR': R' ≡₁ R ∪₁ RMW'.
Proof.
  split; rename x into r.
  - intro R_r; unfolder.
    destruct (classic (RMW' r)) as [RMW_r | N_RMW_r]; [right | left].
    + specialize (RMW_COR_W r RMW_r).
      destruct RMW_COR_W as [r2 RMW_r2r].
      specialize (RMW_COR r2 r RMW_r2r).
      destruct RMW_COR as (l & COR); desf.
    + red; red in R_r; by rewrite (LAB r N_RMW_r).
  - unfolder; ins; desf.
    + assert (N_RMW_r: ~ RMW' r).
      { intro RMW_r.
        apply RMW_in_W in RMW_r.
        by apply WR_MISMATCH with r.
      }
      red; red in H.
      by rewrite <- (LAB r N_RMW_r).
    + red; red in H; desf.
Qed.

Lemma FF': F' ≡₁ F.
Proof.
  split; intros F_x; unfold RC11_Events.F in *.
  - rewrite LAB; auto.
    intro RMW_x; red in RMW_x; desf.
  - rewrite <- LAB; auto.
    intro RMW_x.
    specialize (RMW_COR_W x RMW_x); destruct RMW_COR_W as [r RMW_rx].
    specialize (RMW_COR r x RMW_rx); destruct RMW_COR as (l & COR); desf.
Qed.

Lemma E_W: ⦗E⦘ ⨾ ⦗W⦘ ⊆ ⦗E'⦘ ⨾ ⦗W'⦘.
Proof.
  rewrite EE, id_union.
  relsf; unionL.
  - by rewrite WW'.
  - rewrite NewR_in_R.
    unfolder; ins; desf.
    by exfalso; apply WR_MISMATCH with y.
Qed.

Lemma F_REL': ⦗F ∩₁ Rel⦘ ⊆ ⦗F' ∩₁ Rel'⦘.
Proof.
  unfolder; intros t a (EQ & F_a & Rel_a); desf; splits; auto; [by apply FF'|].
  assert (lab a = lab' a) by (apply LAB; apply FF' in F_a; solve_type_mismatch).
  solve_mode_mismatch.
Qed.

Lemma F_ACQ': ⦗F ∩₁ Acq⦘ ⊆ ⦗F' ∩₁ Acq'⦘.
Proof.
  unfolder; intros t a (EQ & F_a & Acq_a); desf; splits; auto; [by apply FF'|].
  assert (lab a = lab' a) by (apply LAB; apply FF' in F_a; solve_type_mismatch).
  solve_mode_mismatch.
Qed.

Lemma W_REL': ⦗W ∩₁ Rel⦘ ⊆ ⦗W' ∩₁ Rel'⦘.
Proof.
  rewrite WW'.
  unfolder; intros t w (EQ & W_w & Rel_w); desf; splits; auto.
  destruct (classic (RMW' w)) as [RMW_w | N_RMW_w].
  - specialize (RMW_COR_W w RMW_w); destruct RMW_COR_W as [r RMW_rw].
    specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
    red; red in Rel_w; unfold get_rmw_mod in COR5; mode_unfolder; desf.
  - assert (lab w = lab' w) by by apply LAB.
    solve_mode_mismatch.
Qed.

Lemma W_RLX': ⦗W ∩₁ Rlx⦘ ⊆ ⦗W' ∩₁ Rlx'⦘.
Proof.
  rewrite WW'.
  unfolder; intros t w (EQ & W_w & Rlx_w); desf; splits; auto.
  destruct (classic (RMW' w)) as [RMW_w | N_RMW_w].
  - specialize (RMW_COR_W w RMW_w); destruct RMW_COR_W as [r RMW_rw].
    specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
    red; red in Rlx_w; unfold get_rmw_mod in COR5; mode_unfolder; desf.
  - assert (lab w = lab' w) by by apply LAB.
    solve_mode_mismatch.
Qed.

Lemma W_sbloc_W (WF: Wf G): ⦗W⦘ ⨾ sb|loc^? ⨾ ⦗W ∩₁ Rlx⦘ ⊆ ⦗W'⦘ ⨾ sb'|loc'^? ⨾ ⦗W' ∩₁ Rlx'⦘.
Proof.
  rewrite SB.
  arewrite (
    ((sb' ∪ sb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) |loc)^? ⨾ ⦗W ∩₁ Rlx⦘ ⊆ sb'|loc^? ⨾ ⦗W ∩₁ Rlx⦘).
  { arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗R⦘) by cdes WF; cdes WF_RMW;
      apply domb_helper, transp_domb; rewrite RMW_DOM; basic_solver.
    case_refl _; try basic_solver.
    rewrite inter_union_l; relsf; unionL; [basic_solver|].
    by unfolder; ins; desf; exfalso; apply WR_MISMATCH with y.
  }
  by rewrite W_RLX', WW', SAME_LOC'.
Qed.

Lemma R_ACQ': ⦗R ∩₁ Acq⦘ ⊆ ⦗R' ∩₁ Acq'⦘.
Proof.
  rewrite RR'.
  unfolder; ins; desf; splits; auto.
  assert (lab y = lab' y).
  { apply LAB; intro RMW_y; apply RMW_in_W in RMW_y.
    by apply WR_MISMATCH with y. }
  solve_mode_mismatch.
Qed.

Lemma R_RLX': ⦗R ∩₁ Rlx⦘ ⊆ ⦗R' ∩₁ Rlx'⦘.
Proof.
  rewrite RR'.
  unfolder; ins; desf; splits; auto.
  assert (lab y = lab' y).
  { apply LAB; intro RMW_y; apply RMW_in_W in RMW_y.
    by apply WR_MISMATCH with y. }
  solve_mode_mismatch.
Qed.

Lemma path_helper X (r r' : relation X)
      (A : r' ⨾ r ≡ ∅₂)
      (B : r' ⨾ r' ≡ ∅₂) :
  (r ∪ r')＊ ≡ r＊ ∪ r＊ ⨾ r'.
Proof.
  clear - A B.
  split.
  - eapply inclusion_rt_ind_left; eauto with rel.
    relsf; unionL; eauto with rel rel_full.
    + rewrite seq_rtE_r, A; rels; eauto with rel rel_full.
    + arewrite (r ⨾ r＊ ⊆ r＊); rewrite seq_rtE_l; basic_solver 42.
    + arewrite (r' ⨾ r＊ ⊆ r' ∪ (r' ⨾ r) ⨾ r＊) by rewrite seq_rtE_r.
      seq_rewrite A; rels; rewrite B; rels.
  - arewrite (r ⊆ r ∪ r').
    arewrite (r ⊆ r ∪ r') at 2.
    arewrite (r' ⊆ r ∪ r') at 3.
    rewrite <- ct_end.
    eauto with rel.
Qed.

Lemma pathp_helper X (r r' : relation X)
      (A : r' ⨾ r ≡ ∅₂)
      (B : r' ⨾ r' ≡ ∅₂) :
  (r ∪ r')⁺ ≡ r⁺ ∪ r＊ ⨾ r'.
Proof.
  clear - A B.
  rewrite ct_begin, path_helper; auto.
  split.
  - relsf; unionL; eauto with rel rel_full.
    + rewrite seq_rtE_r. rewrite A. rels. eauto with rel rel_full.
    + arewrite (r ⨾ r＊ ⊆ r＊); eauto with rel rel_full.
    + rewrite seq_rtE_l.
      relsf; sin_rewrite B; rels.
      rewrite ct_begin, !seqA.
      seq_rewrite A; rels.
  - unionL.
    + rewrite ct_begin; basic_solver 42.
    + rewrite rtE at 1; relsf; unionL.
      * eauto with rel rel_full.
      * unionR right -> left.
        by rewrite ct_begin, !seqA.
Qed.

Proposition events_to_edges : consistent' -> consistent.
Proof.
  ins; cdes H; red; unnw.
  
  assert (WF': Wf G).
  { (* LAB_INIT *)
    assert (LAB_INIT': forall l : location, lab (Init l) = init_label l).
    { cdes WF; cdes WF_ACTS; ins; rewrite LAB; auto.
      intro RMW_I; red in RMW_I; rewrite (LAB_INIT l) in RMW_I; desf. }
    (* SB_ACT *)
    assert (SB_ACT': sb ⊆ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘).
    { cdes WF; cdes WF_SB; rewrite SB, EE; unionL; rewrite SB_ACT at 1.
      * clear; basic_solver.
      * arewrite_id ⦗E'⦘ at 2; simpl_rels.
        arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗New_R⦘) at 1.
        { unfolder; intros w r RMW_rw; desf; split; auto.
          specialize (RMW_COR r w RMW_rw).
          destruct RMW_COR as (l & COR); desf.
        }
      arewrite (New_R ⊆₁ E' ∪₁ New_R) at 1 by basic_solver.
      arewrite (E' ⊆₁ E' ∪₁ New_R) at 1 by basic_solver.
      clear; basic_solver 42.
    }
    (* SB_T *)
    assert (SB_T': transitive sb).
    { cdes WF; cdes WF_SB; apply transitiveI; rewrite SB.
      relsf; unionL; eauto with rel rel_full; rewrite !seqA;
      sin_rewrite (rmw_transp_seq_sb SB_ACT); basic_solver.
    }
    (* SB_TID *)
    assert (SB_TID': sb ⊆ sb∙ ∪ init_pair).
    { cdes WF; cdes WF_SB; rewrite SB.
      unionL.
      * rewrite SB_TID at 1; unionL; basic_solver.
      * rewrite SB_TID at 1; relsf; unionL.
        -- arewrite (sb'∙ ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹ ⊆ (sb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹)∙).
           { assert (NewR_in_R := NewR_in_R).
             clear - SB_TID RMW_COR F_read F_tid NRMW_EVENTS NewR_in_R LAB_INIT'.
             unfolder; ins; desf; split; [eexists; splits; eauto |].
             apply st_trans with z; auto.
             apply st_inv.
             specialize (RMW_COR y z H1).
             destruct RMW_COR as (l & COR); desf.
             
             red; split.
             - unfold tid; desf.
               apply NewR_in_R in COR0.
               assert (W (Init l0)) by (red; rewrite (LAB_INIT' l0); desf).
               solve_type_mismatch.
             - symmetry;apply F_tid.
           }
           basic_solver 42.
        -- arewrite (init_pair ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹ ⊆ init_pair).
           { clear - F_read RMW_COR NRMW_EVENTS LAB_INIT'.
             unfold init_pair; unfolder; ins; desf; split; auto.
             assert (R y).
             { specialize (RMW_COR y z H1).
               destruct RMW_COR as (l & COR); desf.
             }
             intro INIT_y.
             assert (W y) by
              (red in INIT_y; desf; red; rewrite (LAB_INIT' l); desf).
             by apply WR_MISMATCH with y.
           }
           eauto with rel.
    }
    
    (* RMW_DOM *)
    assert (RMW_DOM': rmw ⊆ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘).
    { unfolder; intros r w RMW_rw.
      assert (RMW_in_W := RMW_in_W).
      specialize (RMW_COR r w RMW_rw).
      destruct RMW_COR as (l & COR); desf.
      splits; auto.
    }
    (* RMW_LOC *)
    assert (RMW_LOC': funeq loc rmw).
    { red; intros r w RMW_rw.
      specialize (RMW_COR r w RMW_rw).
      destruct RMW_COR as (l & COR); desf.
      unfold RC11_Events.loc; desf.
    }
    (* RMW_IMM *)
    assert (RMW_IMM': rmw ⊆ sb|imm).
    { unfolder; intros r w RMW_rw.
      specialize (RMW_COR r w RMW_rw).
      destruct RMW_COR as (l & COR); desf.
    }
    
    cdes WF; red; unnw; splits.
    - (* WfACTS *)
      cdes WF_ACTS; red; splits; unnw; auto.
      + (* ACTS_INIT *)
        rewrite ACTS.
        ins; specialize (ACTS_INIT l).
        apply in_app_iff; auto.
    - (* WfSB *)
      cdes WF_SB; red; splits; unnw; auto.
      + (* SB_INIT *)
        rewrite EE, SB, id_union.
        relsf; unionL.
        * rewrite SB_INIT; eauto with rel.
        * unionR right.
          unfolder; intros i r (IP_ir & NewR_r).
          assert (RMW_in_E := RMW_in_E).
          specialize (RMW_COR_R r NewR_r); destruct RMW_COR_R as [w RMW_rw].
          specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
          exists w; splits; auto.
          apply SB_INIT.
          unfolder in COR6; desf.
          exists w; split.
          -- unfold init_pair in *; split; desf.
             by cdes WF; cdes WF_ACTS; apply RMW_implies_not_init.
          -- unfolder; split; auto.
             by apply RMW_in_E.
      + (* SB_IRR *)
        rewrite SB; unionL; auto.
        rotate.
        sin_rewrite (rmw_transp_seq_sb SB_ACT); basic_solver.
      + (* SB_TOT *)
        ins; specialize (SB_TOT i).
        assert (NewR_implies_sb_to_RMW := NewR_implies_sb_to_RMW).
        clear - WF SB ACTS SB_ACT' SB_TID' SB_TOT SB_T' RMW_COR NewR_implies_sb_to_RMW.
        arewrite (E ⊆₁ E' ∪₁ New_R) by rewrite EE.
        unfold is_total in *; ins; unfolder in IWa; unfolder in IWb; desf.
        * assert (IWa': (E' ∩₁ (fun a : event => tid a = Some i)) a)
            by basic_solver.
          assert (IWb': (E' ∩₁ (fun a : event => tid a = Some i)) b)
            by basic_solver.
          specialize (SB_TOT a IWa' b IWb' NEQ); desf;
          [left | right]; by apply SB_incl.
        * apply (NewR_implies_sb_to_RMW SB_ACT') in IWa.
          destruct IWa as (w & RMW_w & RMW_aw & SB_aw & E_w).
          destruct (classic (w = b)) as [EQ | NEQ'].
          { (* w = b *) unfolder in SB_aw; desf; subst; auto. }
          assert (IWw': (E' ∩₁ (fun a : event => tid a = Some i)) w).
          { unfolder; split; auto.
            unfolder in SB_aw; desf.
            apply SB_TID' in SB_aw; unfolder in SB_aw; desf.
            - unfold same_thread in *; desf; congruence.
            - repeat (red in SB_aw; desf).
          }
          assert (IWb': (E' ∩₁ (fun a : event => tid a = Some i)) b)
            by basic_solver.
          specialize (SB_TOT w IWw' b IWb' NEQ'); desf.
          -- unfolder in SB_aw; desf; apply SB_incl in SB_TOT; eauto with rel.
          -- right; apply SB; right; basic_solver.
        * apply (NewR_implies_sb_to_RMW SB_ACT') in IWb.
          destruct IWb as (w & RMW_w & RMW_aw & SB_aw & E_w).
          destruct (classic (a = w)) as [EQ | NEQ'].
          { (* a = w *) unfolder in SB_aw; desf; subst; auto. }
          assert (IWa': (E' ∩₁ (fun a : event => tid a = Some i)) a)
            by basic_solver.
          assert (IWw': (E' ∩₁ (fun a : event => tid a = Some i)) w).
          { unfolder; split; auto.
            unfolder in SB_aw; desf.
            apply SB_TID' in SB_aw; unfolder in SB_aw; desf.
            - unfold same_thread in *; desf; congruence.
            - repeat (red in SB_aw; desf).
          }
          specialize (SB_TOT a IWa' w IWw' NEQ'); desf.
          -- left; apply SB; right; basic_solver.
          -- unfolder in SB_aw; desf; apply SB_incl in SB_TOT; eauto with rel.
        * apply (NewR_implies_sb_to_RMW SB_ACT') in IWa.
          destruct IWa as (w1 & RMW_w1 & RMW_aw1 & SB_aw1 & E_w1).
          apply (NewR_implies_sb_to_RMW SB_ACT') in IWb.
          destruct IWb as (w2 & RMW_w2 & RMW_bw2 & SB_bw2 & E_w2).
          destruct (classic (w1 = w2)) as [EQ | NEQ'].
          { (* w1 = w2 *)
            subst; exfalso; apply NEQ.
            specialize (RMW_COR a w2 RMW_aw1).
            destruct RMW_COR as (l & COR); desf.
            by symmetry; apply COR7.
          }
          assert (IWw1: (E' ∩₁ (fun a : event => tid a = Some i)) w1).
          { unfolder; split; auto.
            unfolder in SB_aw1; desf.
            apply SB_TID' in SB_aw1; unfolder in SB_aw1; desf.
            - unfold same_thread in *; desf; congruence.
            - repeat (red in SB_aw1; desf).
          }
          assert (IWw2: (E' ∩₁ (fun a : event => tid a = Some i)) w2).
          { unfolder; split; auto.
            unfolder in SB_bw2; desf.
            apply SB_TID' in SB_bw2; unfolder in SB_bw2; desf.
            - unfold same_thread in *; desf; congruence.
            - repeat (red in SB_bw2; desf).
          }
          specialize (SB_TOT w1 IWw1 w2 IWw2 NEQ'); desf.
          -- assert (SB_w1b: sb w1 b) by (apply SB; right; basic_solver).
             unfolder in SB_aw1; desf.
             eauto with rel.
          -- assert (SB_w2a: sb w2 a) by (apply SB; right; basic_solver).
             unfolder in SB_bw2; desf.
             eauto with rel.
    - (* WfRMW *)
      cdes WF_RMW; red; splits; unnw; auto.
      + (* RMW_MOD *)
        intros r w RMW_rw.
        specialize (RMW_COR r w RMW_rw).
        destruct RMW_COR as (l & COR); desf.
        clear - COR3 COR4 COR5.
        unfold get_rmw_mod in *; destruct or, ow; desf; solve_mode_mismatch.
    - (* WfRF *)
      cdes WF_RF; red; splits; unnw.
      + (* RF_ACT *)
        rewrite RF; unionL.
        * rewrite RF_ACT at 1; rewrite !seqA; rewrite seq_eqvC at 1.
          arewrite (E' ⊆₁ E) by rewrite EE; basic_solver.
          basic_solver 42.
        * rewrite RF_ACT at 1; arewrite_id ⦗E'⦘ at 2; simpl_rels.
          arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗E⦘) at 1.
          { apply domb_helper, transp_domb; red; intros a b RMW_ab.
            apply RMW_IMM' in RMW_ab; unfolder in RMW_ab; desf.
            apply SB_ACT' in RMW_ab; unfolder in RMW_ab; desf.
          }
          arewrite (E' ⊆₁ E) by rewrite EE; basic_solver.
          basic_solver 42.
      + (* RF_IRR *)
        rewrite RF; unionL.
        * by clear_equivs ⦗set_compl RMW'⦘.
        * arewrite (rf' ⊆ ⦗W⦘ ⨾ rf')
            by rewrite WW'; rewrite RF_DOM at 1; basic_solver.
          arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗R⦘)
            by apply domb_helper, transp_domb; rewrite RMW_DOM'; basic_solver.
          rotate; unfolder; ins; desf.
          by apply WR_MISMATCH with z.
      + (* RF_DOM *)
        rewrite RF; unionL.
        * rewrite RF_DOM at 1; rewrite RR', <- WW'; rewrite !seqA.
          arewrite (⦗R ∪₁ RMW'⦘ ⨾ ⦗set_compl RMW'⦘ ⊆ ⦗set_compl RMW'⦘ ⨾ ⦗R⦘)
            by unfolder; ins; desf.
          basic_solver 42.
        * arewrite (rf' ⊆ ⦗W⦘ ⨾ rf')
            by rewrite WW'; rewrite RF_DOM at 1; basic_solver.
          arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗R⦘) at 1.
            by apply domb_helper, transp_domb; rewrite RMW_DOM'; basic_solver.
          basic_solver 42.
      + (* RF_LOC *)
        rewrite RF; apply funeq_union.
        * by rewrite LOC'; clear_equivs ⦗set_compl RMW'⦘.
        * repeat apply funeq_seq.
          -- by rewrite LOC'.
          -- by apply funeq_eqv_rel.
          -- by apply funeq_transp.
      + (* RF_VAL *)
        intros a b RF_ab; apply RF in RF_ab; unfolder in RF_ab; desf.
        * assert (N_RMW_b: ~ RMW' b) by tauto.
          destruct (classic (RMW' a)) as [RMW_a | N_RMW_a].
          -- specialize (RMW_COR_W a RMW_a); destruct RMW_COR_W as [r RMW_ra].
             specialize (RMW_COR r a RMW_ra); destruct RMW_COR as (l & COR); desf.
             unfold valr, valw in *.
             rewrite (LAB b N_RMW_b), <- (RF_VAL a b RF_ab).
             desf.
          -- unfold valr, valw in *.
             by rewrite (LAB b N_RMW_b), (LAB a N_RMW_a), <- (RF_VAL a b RF_ab).
        * assert (VA: valw lab a = valw lab' a).
          { destruct (classic (RMW' a)) as [RMW_a | N_RMW_a].
            - specialize (RMW_COR_W a RMW_a); destruct RMW_COR_W as [r RMW_ra].
              specialize (RMW_COR r a RMW_ra); destruct RMW_COR as (l & COR); desf.
              unfold valr, valw in *; desf.
            - unfold valr, valw in *.
              by rewrite (LAB a N_RMW_a).
          }
          rename RF_ab0 into RMW_z, RF_ab1 into RMW_bz.
          specialize (RMW_COR_W z RMW_z); destruct RMW_COR_W as [r RMW_rz].
          specialize (RMW_COR r z RMW_rz); destruct RMW_COR as (l & COR); desf.
          specialize (COR7 b RMW_bz); desf.
          rewrite VA, (RF_VAL a z RF_ab).
          unfold valr, valw in *; desf.
      + (* RF_FUN *)
        rewrite RF.
        apply functional_union.
        * red; unfolder; ins; desf.
          red in RF_FUN; apply (RF_FUN x y z); basic_solver.
        * red; unfolder; ins; desf.
          assert (z2 = z3).
          { specialize (RMW_COR x z3 H6); destruct RMW_COR as (l & COR); desf.
            apply (COR8 z2 H3). }
          subst; apply (RF_FUN z3 y z); basic_solver.
        * clear - RF_ACT F_new RMW_COR.
          unfold dom_rel; ins; unfolder in *; desf.
          apply (F_new z1).
          specialize (RMW_COR x z1 H2); destruct RMW_COR as (l & COR); desf.
          apply RF_ACT in H; desf.
      + (* RF_TOT *)
        ins.
        destruct (classic (New_R b)) as [NewR_r | N_NewR].
        * rename b into r.
          assert (RR' := RR').
          assert (NewR_in_R := NewR_in_R).
          assert (RMW_in_W := RMW_in_W).
          specialize (RMW_COR_R r NewR_r); destruct RMW_COR_R as [w RMW_rw].
          specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
          assert (E' w).
          { apply EE'; unfolder; split.
            - unfolder in COR6; desf; apply SB_ACT' in COR6; unfolder in COR6; desf.
            - intro NewR_w; apply NewR_in_R in NewR_w; apply RMW_in_W in COR1.
              by apply WR_MISMATCH with w.
          }
          assert (R' w) by (apply RR'; unfolder; auto).
          specialize (RF_TOT w H0 H1); desf.
          exists a; apply RF; right.
          exists w; split; auto.
          unfolder; splits; auto.
        * assert (E' b) by (apply EE'; unfolder; auto).
          assert (R' b) by (apply RR'; unfolder; auto).
          specialize (RF_TOT b H0 H1); desf.
          exists a; apply RF.
          destruct (classic (RMW' b)) as [RMW_b | N_RMW_b]; [right | left].
          -- apply RMW_in_W in RMW_b.
             by exfalso; apply WR_MISMATCH with b.
          -- unfolder; split; auto.
    - (* WfMO *)
      cdes WF_MO; red; splits; unnw; rewrite ?MO, ?LOC'; try done.
      + (* MO_ACT *)
        rewrite MO_ACT at 1.
        arewrite (E' ⊆₁ E) by rewrite EE; basic_solver.
      + (* MO_DOM *)
        rewrite MO_DOM at 1.
        arewrite (W' ⊆₁ W) by rewrite WW'.
      + (* MO_TOT *)
        ins; specialize (MO_TOT l); rewrite MO.
        arewrite (E ∩₁ W ∩₁ (fun a : event => loc' a = Some l) ⊆₁
                  E' ∩₁ W' ∩₁ (fun a : event => loc' a = Some l)).
        { rewrite WW', EE.
          unfolder; ins; desf; splits; auto.
          apply WW' in H2; apply NewR_in_R in H0.
          by exfalso; apply WR_MISMATCH with x.
        }
        done.
    - (* WfDEPS *) done.
  }
  
  assert (RB: rb ⊆ rb' ∪ rmw ⨾ ⦗RMW'⦘ ⨾ rb'^?).
  { arewrite (rb ≡ rf⁻¹ ⨾ mo) by rewrite NRMW_implies_original_rb.
    unfold RC11_Model.rb.
    rewrite MO, RF, !transp_union, !transp_seq, !transp_eqv_rel, !transp_inv,
      seq_union_l, !seqA; unionL.
    - unionR left.
      arewrite (rf'⁻¹ ⊆ ⦗R'⦘ ⨾ rf'⁻¹) at 1
        by cdes WF; cdes WF_RF; rewrite RF_DOM at 1; basic_solver.
      arewrite (mo' ⊆ mo' ⨾ ⦗W'⦘) at 1
        by cdes WF; cdes WF_MO; rewrite MO_DOM at 1; basic_solver.
      unfolder; ins; desf; split; eauto.
      apply or_not_and; left.
      intro; subst; contradict H0; solve_type_mismatch.
    - unionR right.
      unfolder; ins; desf.
      destruct (classic (z = y)) as [EQ | NEQ]; eauto.
      repeat eexists; splits; eauto.
      right.
      repeat eexists; splits; eauto.
      by apply or_not_and; left.
  }
  
  assert (ECO: eco ⊆ 
    eco' ∪
    rmw ⨾ ⦗RMW'⦘ ⨾ eco'^? ∪
    eco' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹ ∪
    rmw ⨾ ⦗RMW'⦘ ⨾ eco' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹).
  { unfold RC11_Model.eco.
    rewrite MO; rewrite RF; rewrite RB.
    relsf; unionL; try basic_solver 42.
  }
  
  assert (SW: sw ⊆ sw' ∪ sw' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹).
  { unfold RC11_Model.sw, RC11_Model.release, RC11_Model.rs.
    rewrite (NRMW_implies_original_useq WF' NRMW_EVENTS).
    unfold RC11_Model.useq.
    sin_rewrite (W_sbloc_W WF').
    rewrite <- WW' at 1.
    rewrite !seqA; sin_rewrite E_W; rewrite !seqA.
    rewrite W_REL', F_REL', R_RLX', F_ACQ'.
    
    arewrite (sb ⨾ ⦗F' ∩₁ Acq'⦘ ⊆ sb' ⨾ ⦗F' ∩₁ Acq'⦘).
    { rewrite SB; relsf; unionL; [basic_solver|].
      arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗R⦘) by cdes WF'; cdes WF_RMW;
        apply domb_helper, transp_domb; rewrite RMW_DOM; basic_solver.
      rewrite FF'.
      unfolder; ins; desf; solve_type_mismatch.
    }
    
    arewrite (rmw' ≡ ∅₂) by basic_solver.
    rels.
    arewrite ((⦗W' ∩₁ Rel'⦘ ∪ ⦗F' ∩₁ Rel'⦘ ⨾ sb) ⨾ ⦗E'⦘ ⨾ ⦗W'⦘ ⊆
              (⦗W' ∩₁ Rel'⦘ ∪ ⦗F' ∩₁ Rel'⦘ ⨾ sb') ⨾ ⦗E'⦘ ⨾ ⦗W'⦘).
    { rewrite SB.
      relsf; unionL; [by unionR left | by unionR right |].
      arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗R⦘) by cdes WF'; cdes WF_RMW;
        apply domb_helper, transp_domb; rewrite RMW_DOM; basic_solver.
      arewrite_id ⦗E'⦘ at 1; simpl_rels.
      rewrite <- WW'.
      by unfolder; ins; desf; exfalso; apply WR_MISMATCH with y.
    }
    rewrite RF.
    arewrite (((rf' ⨾ ⦗set_compl RMW'⦘ ∪ rf' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) ⨾ rmw)＊ ⊆ (rf' ⨾ ⦗RMW'⦘)＊).
    { rewrite seq_union_l.
      arewrite ((rf' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) ⨾ rmw ⊆ rf' ⨾ ⦗RMW'⦘).
      { unfolder; ins; desf.
        specialize (RMW_COR z0 z H2); destruct RMW_COR as (l & COR); desf.
        specialize (COR8 y H3); desf.
      }
      arewrite_false (rf' ⨾ ⦗set_compl RMW'⦘ ⨾ rmw).
      { cdes WF; cdes WF_RF; rewrite RF_ACT.
        unfolder; ins; desf.
        specialize (RMW_COR z1 y H4); destruct RMW_COR as (l & COR); desf.
        apply (F_new y).
        by red in H6.
      }
      rels.
    }
    case_union_2 _ (rf' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹); [unionR left | unionR right]; hahn_frame.
    - rewrite R_ACQ'; rels; basic_solver 42.
    - case_union_2 _ _.
      + unionR left.
        unfolder; ins; desf.
        repeat eexists; splits; eauto; [solve_type_mismatch|].
        specialize (RMW_COR y z0 H3); destruct RMW_COR as (l & COR); desf.
        unfold get_rmw_mod in *; red; red in H5; solve_mode_mismatch.
      + arewrite_id ⦗R' ∩₁ Rlx'⦘ at 1; simpl_rels.
        arewrite_false (rmw⁻¹ ⨾ sb').
        { arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗New_R⦘) at 1.
          { unfolder; intros w r RMW_rw; desf; split; auto.
            specialize (RMW_COR r w RMW_rw).
            destruct RMW_COR as (l & COR); desf.
          }
          arewrite (sb' ⊆ ⦗E'⦘ ⨾ sb') by cdes WF; cdes WF_SB;
            rewrite SB_ACT at 1; basic_solver.
          unfolder; ins; desf.
          apply (F_new x).
          specialize (RMW_COR z0 x H0); destruct RMW_COR as (l & COR); desf.
        }
        rels.
  }
  
  assert (RMW_seq_SB_SW: rmw⁻¹ ⨾ (sb' ∪ sw') ⊆ ∅₂).
  { arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗New_R⦘) at 1.
    { unfolder; intros w r RMW_rw; desf; split; auto.
      specialize (RMW_COR r w RMW_rw).
      destruct RMW_COR as (l & COR); desf.
    }
    arewrite (sb' ∪ sw' ⊆ ⦗E'⦘ ⨾ (sb' ∪ sw')).
    { unionL.
      - arewrite (sb' ⊆ ⦗E'⦘ ⨾ sb') by cdes WF; cdes WF_SB;
          rewrite SB_ACT at 1; basic_solver.
        basic_solver.
      - rewrite seq_union_r; unionR right.
        unfold RC11_Model.sw, RC11_Model.release, RC11_Model.rs.
        arewrite (sb' ⊆ ⦗E'⦘ ⨾ sb') at 1 by cdes WF; cdes WF_SB;
          rewrite SB_ACT at 1; basic_solver.
        case_union_2 ⦗W' ∩₁ Rel'⦘ _.
        + arewrite (⦗W' ∩₁ Rel'⦘ ⨾ ⦗E'⦘ ⊆ ⦗E'⦘ ⨾ ⦗W' ∩₁ Rel'⦘ ⨾ ⦗E'⦘) by basic_solver.
          eauto with rel rel_full.
        + arewrite (⦗F' ∩₁ Rel'⦘ ⨾ ⦗E'⦘ ⊆ ⦗E'⦘ ⨾ ⦗F' ∩₁ Rel'⦘) by basic_solver.
          eauto with rel rel_full.
    }
    sin_rewrite New_R_seq_E.
    rels.
  }
  
  assert (HB: hb ⊆ hb' ∪ hb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹).
  { unfold RC11_Model.hb.
    arewrite (sb ∪ sw ⊆ (sb' ∪ sw') ∪ (sb' ∪ sw') ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹).
      by rewrite SB, SW; basic_solver 42.
    rewrite pathp_helper;
    try by (split; [rewrite !seqA; sin_rewrite RMW_seq_SB_SW|]; basic_solver).
    seq_rewrite <- ct_end; eauto with rel rel_full.
  }
  assert (HB_SEQ_RMW: hb' ⨾ rmw ⊆ ∅₂).
  { unfolder; ins; desf.
    rename z into r, y into w, H1 into RMW_rw.
    specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
    eby eapply F_new, hb_actb.
  }
  assert (RMW_SEQ_SB: rmw⁻¹ ⨾ sb' ⊆ ∅₂).
  { cdes WF; cdes WF_SB.
    unfolder; ins; desf.
    rename z into r, x into w, H0 into RMW_rw.
    specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
    eby eapply F_new, sb_acta.
  }
  assert (RMW_SEQ_RF: rmw⁻¹ ⨾ rf' ⊆ ∅₂).
  { cdes WF; cdes WF_RF.
    unfolder; ins; desf.
    rename z into r, x into w, H0 into RMW_rw.
    specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
    eby eapply F_new, rf_acta.
  }
  assert (RMW_SEQ_ECO: rmw⁻¹ ⨾ eco' ⊆ ∅₂).
  { unfolder; ins; desf.
    rename z into r, x into w, H0 into RMW_rw.
    specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
    eby eapply F_new, eco_acta.
  }
  assert (RMW_SEQ_F: rmw⁻¹ ⨾ ⦗F ∩₁ Sc⦘ ⊆ ∅₂).
  { unfolder; ins; desf.
    rename y into r, x into w, H0 into RMW_rw.
    specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
    solve_type_mismatch.
  }
  assert (RMW_SEQ_HB: rmw⁻¹ ⨾ hb' ⊆ ∅₂).
  { unfolder; ins; desf.
    rename z into r, x into w, H0 into RMW_rw.
    specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
    eby eapply F_new, hb_acta.
  }
  assert (RMW_SEQ_MO: rmw⁻¹ ⨾ mo' ⊆ ∅₂).
  { cdes WF; cdes WF_MO.
    unfolder; ins; desf.
    rename z into r, x into w, H0 into RMW_rw.
    specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
    eby eapply F_new, mo_acta.
  }
  assert (RMW_SEQ_RB: rmw⁻¹ ⨾ rb' ⊆ ∅₂).
  { cdes WF; cdes WF_RF.
    unfolder; ins; desf.
    rename z into r, x into w, H0 into RMW_rw.
    specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
    eby eapply F_new, rb_acta.
  }
  assert (SB_RMW_HB: (sb' ∪ sb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) ⨾ hb' ⊆ sb' ⨾ hb').
  { case_union_2 _ _; [basic_solver|].
    simpl_rels; sin_rewrite RMW_SEQ_HB; basic_solver.
  }
  assert (HB_RMW_HB: (hb' ∪ hb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) ⨾ hb' ⊆ hb').
  { case_union_2 _ _.
    - arewrite (hb' ⨾ hb' ⊆ hb'); basic_solver.
    - simpl_rels; sin_rewrite RMW_SEQ_HB; basic_solver.
  }
  assert (RMW_SB_RMW: rmw⁻¹ ⨾ (sb' ∪ sb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) ⊆ ∅₂).
  { case_union_2 _ _; sin_rewrite RMW_SEQ_SB; basic_solver. }
  assert (RMW_HB_RMW: rmw⁻¹ ⨾ (hb' ∪ hb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) ⊆ ∅₂).
  { case_union_2 _ _; sin_rewrite RMW_SEQ_HB; basic_solver. }
  assert (HB_RMW_HB_LOC: (hb' ∪ hb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) |loc' ⨾ hb' ⊆ hb'|loc' ⨾ hb').
  { rewrite inter_union_l.
    case_union_2 _ _; [basic_solver|].
    rewrite inter_inclusion; simpl_rels; sin_rewrite RMW_SEQ_HB; basic_solver.
  }

  splits; auto.
  + (* Coherence *)
    red; red in COH.
    case_refl _; rewrite HB; case_union_2 _ _.
    - by apply irr_hb.
    - unfolder; ins; desf.
      apply F_new with (a := z).
      specialize (RMW_COR x z H2); destruct RMW_COR as (l & COR); desf.
      by apply hb_acta in H0.
    - rewrite ECO.
      relsf; repeat (apply irreflexive_union; split).
      * by rewrite crE, seq_union_r, irreflexive_union in COH; desf.
      * unfolder; ins; desf.
        -- apply F_new with (a := x).
           specialize (RMW_COR z x H1); destruct RMW_COR as (l & COR); desf.
           by apply hb_actb in H0.
        -- apply F_new with (a := z0).
           specialize (RMW_COR z z0 H1); destruct RMW_COR as (l & COR); desf.
           by apply hb_actb in H0.
      * unfolder; ins; desf.
        apply F_new with (a := z0).
        specialize (RMW_COR x z0 H3); destruct RMW_COR as (l & COR); desf.
        by apply hb_acta in H0.
      * unfolder; ins; desf.
        apply F_new with (a := z0).
        specialize (RMW_COR z z0 H1); destruct RMW_COR as (l & COR); desf.
        by apply hb_actb in H0.
    - rewrite ECO.
      relsf; repeat (apply irreflexive_union; split).
      * unfolder; ins; desf.
        apply F_new with (a := z).
        specialize (RMW_COR z0 z H2); destruct RMW_COR as (l & COR); desf.
        by apply eco_acta in H3.
      * unfolder; ins; desf.
        -- assert (EQ: x = z).
           { specialize (RMW_COR z0 z H2); destruct RMW_COR as (l & COR); desf.
             by apply (COR8 x). }
           apply COH with x.
           by unfolder; ins; desf; eexists; eauto.
        -- assert (EQ: z2 = z).
           { specialize (RMW_COR z0 z H2); destruct RMW_COR as (l & COR); desf.
             by apply (COR8 z2). }
           apply COH with x.
           unfolder; ins; desf.
           by exists z; split; auto.
      * unfolder; ins; desf.
        apply F_new with (a := z2).
        specialize (RMW_COR x z2 H5); destruct RMW_COR as (l & COR); desf.
        by apply hb_acta in H0.
      * unfolder; ins; desf.
        apply F_new with (a := z4).
        specialize (RMW_COR x z4 H7); destruct RMW_COR as (l & COR); desf.
        by apply hb_acta in H0.
  + (* Atomicity *)
    red; red in AT.
    rewrite RB, MO.
    case_union_2 _ _.
    - unfolder; ins; desf.
      apply F_new with (a := z0).
      specialize (RMW_COR x z0 H2); destruct RMW_COR as (l & COR); desf.
      by cdes WF; apply rb_acta in H0.
    - case_refl _.
      * unfolder; ins; desf.
        specialize (RMW_COR x z H0); destruct RMW_COR as (l & COR); desf.
        specialize (COR8 z0 H3); desf.
        by cdes WF; cdes WF_MO; apply MO_IRR with z.
      * unfolder; ins; desf.
        specialize (RMW_COR x z H0); destruct RMW_COR as (l & COR); desf.
        specialize (COR8 z1 H4); desf.
        unfold RC11_Model.rb in H2; unfolder in H2; desf.
        apply AT2 with z1.
        unfolder; ins; desf; eauto with rel.
  + (* Atomicity2 *)
    by apply NRMW_implies_atomic2.
  + (* SC *)
    red; red in SC; unfold RC11_Model.psc in *.
    assert (F_SC: F ∩₁ Sc ⊆₁ F' ∩₁ Sc').
    { unfolder; ins; desf.
      assert (LAB_EQ: lab x = lab' x).
      { apply LAB; red; ins.
        assert (W x).
        { specialize (RMW_COR_W x H2); destruct RMW_COR_W as (r & RMW_rx).
          cdes WF'; cdes WF_RMW; specialize (RMW_DOM r x RMW_rx).
          unfolder in RMW_DOM; desf.
        }
        solve_type_mismatch.
      }
      unfold RC11_Events.F, RC11_Events.Sc, RC11_Events.mod.
      by rewrite <- LAB_EQ.
    }
    assert (PSC_F: psc_f ⊆ psc_f').
    { unfold RC11_Model.psc_f in *.
      case_union_2 _ _.
      - rewrite HB; case_union_2 _ _.
        + rewrite F_SC; basic_solver 42.
        + arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗R⦘) 
            by cdes WF'; eapply domb_helper, transp_domb, rmw_doma.
          solve_type_mismatch 42.
      - rewrite HB at 1; case_union_2 _ _.
        + rewrite HB at 1; case_union_2 _ _.
          { rewrite ECO.
            case_union_4 _ _ (eco' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) (rmw ⨾ ⦗RMW'⦘ ⨾ eco' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹).
            2,3,4: by simpl_rels; (sin_rewrite HB_SEQ_RMW +
                                   sin_rewrite RMW_SEQ_HB); basic_solver.
            rewrite F_SC; basic_solver 42.
          }
          arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗R⦘) 
            by cdes WF'; eapply domb_helper, transp_domb, rmw_doma.
          solve_type_mismatch 42.
       + arewrite (F ∩₁ Sc ⊆₁ F' ∩₁ Sc').
         rewrite HB at 1; case_union_2 _ _.
         { rewrite ECO; relsf; unionL.
           - sin_rewrite RMW_SEQ_ECO; basic_solver.
           - case_refl _.
            + unionR left.
              unfolder; ins; desf.
              exists x; splits; auto.
              specialize (RMW_COR z1 z0 H3); destruct RMW_COR as (l & COR); desf.
              specialize (COR8 z3 H4); desf.
              by apply hb_trans with z0.
            + unionR right.
              clear_equivs ⦗RMW'⦘.
              hahn_frame.
              unfolder; ins; desf.
              assert (z = y).
              { specialize (RMW_COR z0 z H1); destruct RMW_COR as (l & COR); desf.
                specialize (COR8 y H2); desf. }
              desf.
         - simpl_rels; sin_rewrite RMW_SEQ_HB; basic_solver.
         - simpl_rels; sin_rewrite RMW_SEQ_HB; basic_solver.
        }
        arewrite (rmw⁻¹ ⊆ rmw⁻¹ ⨾ ⦗R⦘) 
            by cdes WF'; eapply domb_helper, transp_domb, rmw_doma.
        arewrite (⦗R⦘ ⨾ ⦗F' ∩₁ Sc'⦘ ⊆ ∅₂).
        { unfolder; ins; desf.
          assert (~ RMW' y) by solve_type_mismatch.
          specialize (LAB y H0).
          solve_type_mismatch 42.
        }
        basic_solver.
    }
    rewrite PSC_F.
    assert (SC_SB: ⦗Sc⦘ ⨾ sb' ⊆ ⦗Sc'⦘ ⨾ sb').
    { unfolder; ins; desf; split; auto; rename x into w.
      destruct (classic (RMW' w)).
      - specialize (RMW_COR_W w H2); destruct RMW_COR_W as [r].
        specialize (RMW_COR r w H3); destruct RMW_COR as (l & COR); desf.
        unfold RC11_Events.Sc, RC11_Events.mod, get_rmw_mod in *; desf.
      - unfold RC11_Events.Sc, RC11_Events.mod in *.
        by rewrite (LAB w H2) in H0.
    }
    assert (SB_SC: sb' ⨾ ⦗Sc⦘ ⊆ sb' ⨾ ⦗Sc'⦘).
    { unfolder; ins; desf; split; auto; rename y into w.
      destruct (classic (RMW' w)).
      - specialize (RMW_COR_W w H2); destruct RMW_COR_W as [r].
        specialize (RMW_COR r w H3); destruct RMW_COR as (l & COR); desf.
        unfold RC11_Events.Sc, RC11_Events.mod, get_rmw_mod in *; desf.
      - unfold RC11_Events.Sc, RC11_Events.mod in *.
        by rewrite (LAB w H2) in H1.
    }
    assert (PSC_BASE: psc_base ⊆ psc_base' ∪ psc_base' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹).
    { unfold RC11_Model.psc_base in *.
      repeat rewrite seq_union_l; unionL; repeat rewrite seq_union_r; unionL.
      - unfold RC11_Model.scb, RC11_Model.sb_neq_loc.
        rewrite SB, HB, MO, RB.
        relsf; unionL; simpl_rels.
(*         all: arewrite (Sc ⊆₁ Sc') by admit. *)
        + sin_rewrite SC_SB; simpl_rels; sin_rewrite SB_SC.
          repeat unionR left; eauto with rel.
        + unionR right.
          arewrite (⦗RMW'⦘ ⨾ rmw⁻¹ ⨾ ⦗Sc⦘ ⊆ ⦗Sc'⦘ ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹ ⨾ ⦗Sc⦘).
          { unfolder; ins; desf.
            splits; auto.
            rename y into r, x into w, H1 into RMW_rw.
            specialize (RMW_COR r w RMW_rw); destruct RMW_COR as (l & COR); desf.
            unfold get_rmw_mod in COR5.
            solve_mode_mismatch 42.
          }
          repeat unionR left.
          arewrite (⦗Sc⦘ ⨾ sb' ⊆ ⦗Sc'⦘ ⨾ sb') by admit.
          basic_solver 42.
        + 
      - admit.
      - admit.
      - simpl_rels.
        unfold RC11_Model.scb, RC11_Model.sb_neq_loc.
        rewrite SB, HB, MO, RB.
        repeat unionR right.
        relsf; unionL; simpl_rels.
        all: try (sin_rewrite RMW_SEQ_F; basic_solver).
        all: rewrite ?SAME_LOC'.
        all: try (arewrite (F ∩₁ Sc ⊆₁ F' ∩₁ Sc')).
        all: try ((sin_rewrite RMW_SEQ_SB +
                   sin_rewrite RMW_SEQ_HB +
                   sin_rewrite RMW_SEQ_RB +
                   sin_rewrite HB_RMW_HB_LOC +
                   sin_rewrite HB_SEQ_RMW +
                   sin_rewrite RMW_SEQ_MO); basic_solver 42).
        + basic_solver 42.
        + rewrite inclusion_minus_rel; repeat sin_rewrite SB_RMW_HB; simpl_rels;
          rewrite sb_in_hb at 2; do 2 arewrite (hb' ⨾ hb' ⊆ hb'); basic_solver 42.
        + rewrite inclusion_minus_rel; sin_rewrite RMW_SB_RMW; basic_solver 42.
        + basic_solver 42.
        + basic_solver 42.
        + rewrite inclusion_minus_rel;
          repeat sin_rewrite RMW_SB_RMW;
          basic_solver 42.
        + rewrite inclusion_minus_rel;
          repeat sin_rewrite RMW_SB_RMW;
          basic_solver 42.
        + rewrite inter_inclusion.
          sin_rewrite RMW_HB_RMW.
          basic_solver.
        + arewrite (hb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹ ⨾ rmw ⨾ ⦗RMW'⦘ ⊆ hb').
          { unfolder; ins; desf.
            specialize (RMW_COR z0 z H2); destruct RMW_COR as (l & COR); desf.
            specialize (COR8 y H3); desf.
          }
          case_refl _.
          * admit.
          * basic_solver 42.
    }
    by rewrite PSC_BASE.
  + (* No-thin-air *)
    do 2 red; red in NTA; rewrite SB, RF.
    remember (rf' ⨾ ⦗set_compl RMW'⦘) as r2; remember (rf' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) as r1'.
    remember (sb' ⨾ ⦗RMW'⦘ ⨾ rmw⁻¹) as r2'; remember sb' as r1.
    rewrite unionA with (r1 := r1), unionC with (r1 := r2').
    rewrite unionA with (r1 := r2), <- unionA with (r1 := r1).
    remember (r1 ∪ r2) as r; remember (r1' ∪ r2') as r'.
    assert (H1: r' ⨾ r ≡ ∅₂).
    { desf; split; [|basic_solver 42].
      relsf; unionL; simpl_rels.
      1,2: sin_rewrite RMW_SEQ_SB.
      3,4: sin_rewrite RMW_SEQ_RF.
      all: basic_solver.
    }
    assert (H2: r' ⨾ r' ≡ ∅₂).
    { desf; split; [|basic_solver 42].
      relsf; unionL; simpl_rels.
      1,2: sin_rewrite RMW_SEQ_RF.
      3,4: sin_rewrite RMW_SEQ_SB.
      all: basic_solver.
    }
    rewrite (pathp_helper event r r' H1 H2); unionL.
    - by desf; clear_equivs ⦗set_compl RMW'⦘.
    - rewrite rt_begin.
      cdes WF; cdes WF_SB; cdes WF_RF.
      relsf; unionL; red; desf; unfolder; ins; desf.
      1, 2: specialize (RMW_COR x z0 H4).
      all: try specialize (RMW_COR x z2 H6); destruct RMW_COR as (l & COR); desf.
      1, 2: apply (F_new z0).
      all: try apply (F_new z2).
      all: (apply RF_ACT in H0 + apply SB_ACT in H0); unfolder in H0; desf.
Admitted.

End EVENTS_TO_EDGES.

End RC11_Correspondence.


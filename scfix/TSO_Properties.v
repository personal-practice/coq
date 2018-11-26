(******************************************************************************)
(** * Properties of the TSO memory model *)
(******************************************************************************)
Require Import Classical List Relations Peano_dec.
Require Import Hahn HahnMinPath.
Require Import Basic TSO_Events TSO_Model.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section TSO_Properties.

Variable G : execution.

Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'mo'" := G.(mo).
Notation "'rb'" := G.(rb).
Notation "'hb'" := G.(hb).
Notation "'rfe'" := G.(rfe).

Notation "'[E]'" := ⦗fun a => In a acts⦘.
Notation "'[R]'" := ⦗is_r lab⦘.
Notation "'[W]'" := ⦗is_w lab⦘.
Notation "'[RMW]'" := ⦗fun a => is_rmw lab a /\ is_w lab a⦘.
Notation "'[F]'" := ⦗is_f lab⦘.
Notation "'[RW]'" := ⦗is_rw lab⦘.
Notation "'[WF]'" := ⦗is_wf lab⦘.
Notation "'[RMW_F]'" := ([RMW] ∪ [F]).
Notation "a |loc" := (restr_eq_rel (loc lab) a) (at level 1).

Notation "'Wf'" := G.(Wf).
Notation "'WfMO'" := G.(WfMO).
Notation "'WfSB'" := G.(WfSB).
Notation "'Consistent'" := G.(Consistent).

Lemma mo_act (WF: WfMO) : 
  mo ≡ [E] ⨾ mo ⨾ [E].
Proof.
  split; [apply WF| solve_type_mismatchT].
Qed.

Lemma mo_dom (WF: WfMO) : 
  mo ≡ [WF] ⨾ mo ⨾ [WF].
Proof.
  split; [apply WF| solve_type_mismatchT].
Qed.

Lemma rb_act (WF: Wf) : 
  rb ≡ [E] ⨾ rb ⨾ [E].
Proof.
  split; [| by solve_type_mismatchT].
  unfold TSO_Model.rb.
  cdes WF; rewrite mo_act at 1; auto.
  cdes WF; cdes WF_RF; rewrite RF_ACT at 1.
  solve_type_mismatchT 11.
Qed.

Lemma rb_dom (WF: Wf) : 
  rb ≡ [R] ⨾ rb ⨾ [W].
Proof.
  split; [| by solve_type_mismatchT].
  unfold TSO_Model.rb.
  cdes WF; rewrite mo_dom at 1; auto.
  cdes WF_RF; rewrite RF_DOM at 1.
  solve_type_mismatchT 15.
Qed.

Lemma sb_rf : sb ∪ rf ≡ sb ∪ rfe.
Proof.
  unfold TSO_Model.rfe, union, minus_rel; split; red; ins; desf; tauto.
Qed.

Lemma sb_rf_rfe (WF_SB: WfSB): 
  hb ≡ sb ∪ hb^? ⨾ rfe ⨾ sb^?.
Proof.
  unfold TSO_Model.hb.
  by rewrite cr_of_ct, sb_rf, path_ut_last, ct_of_trans, rt_of_trans with (r:=sb);
  cdes WF_SB.
Qed.

Lemma sb_rf_rfe2 (WF_SB: WfSB): 
  hb^? ⨾ rfe ⨾ hb^? ≡ hb^? ⨾ rfe ⨾ sb^?.
Proof.
  unfold TSO_Model.hb; rewrite cr_of_ct.
  unfold TSO_Model.rfe.
  split; [|by rewrite inclusion_r_rt; try edone; vauto].
  rewrite rtE at 2; relsf.
  apply inclusion_union_l; [by rewrite crE; relsf|].
  rewrite sb_rf_rfe; unfold TSO_Model.rfe; try done.
  relsf; apply inclusion_union_l; relsf.
  unfold TSO_Model.hb; rewrite cr_of_ct.
  arewrite ((rf \ sb) ⊆ (sb ∪ rf)＊) at 1.
  rels.
Qed.

Lemma hb_mo (CON : Consistent) : 
  [WF] ⨾ hb ⨾ [WF] ⊆ mo.
Proof.
  unfold seq, eqv_rel; red; ins; desf.
  cdes CON; cdes WF; cdes WF_MO.
  eapply tot_ex; try edone.
    - ins; splits; eauto.
      apply ct_end in H0.
      unfold seq, union in H0; desf.
      cdes WF_SB; apply domab_helper in SB_ACT; desf; eauto.
      cdes WF_RF; apply domab_helper in RF_ACT; desf; eauto.
    - ins; splits; eauto.
      apply ct_begin in H0.
      unfold seq, union in H0; desf.
      cdes WF_SB; apply domab_helper in SB_ACT; desf; eauto.
      cdes WF_RF; apply domab_helper in RF_ACT; desf; eauto.
    - intro; subst; eapply Cww; unfold seq; eexists; splits; eauto.
    - intro; subst; eapply hbI; edone.
Qed.

Lemma hb_mo_refl (CON : Consistent) : 
  [WF] ⨾ hb^? ⨾ [WF] ⊆ mo^?.
Proof.
  unfold TSO_Model.hb; rewrite cr_of_ct.
  rewrite rtE.
  relsf.
  repeat apply inclusion_union_l; rewrite ?seqA; try done.
  by unfold seq, eqv_rel, clos_refl; red; ins; desf; eauto.
  rewrite hb_mo; eauto with rel.
Qed.
  
Lemma irr_mo_rb (CON : Consistent) : irreflexive (mo ⨾ rb).
Proof.
  rewrite irreflexive_seqC.
  apply CON.
Qed.

(* Proposition K.1 *)
Proposition strong_Crfe (CON: Consistent): 
  irreflexive (rb ⨾ mo ⨾ hb^? ⨾ rfe ⨾ hb^?).
Proof.
sin_rewrite sb_rf_rfe2; try apply CON.
arewrite (rfe ⊆ [W] ⨾ rfe).
{ unfold TSO_Model.rfe.
  arewrite (rf ⊆ [W] ⨾ rf).
  by cdes CON; cdes WF; cdes WF_RF; rewrite RF_DOM at 1; basic_solver.
  solve_type_mismatchT 6.
}
arewrite (mo ⊆ mo ⨾ [WF]).
  cdes CON; cdes WF; rewrite mo_dom; eauto; solve_type_mismatchT 8.
arewrite ([W] ⊆ [WF]).
sin_rewrite hb_mo_refl; try by apply CON.
arewrite (mo ⨾ mo^? ⊆ mo).
  by rewrite crE; relsf; apply inclusion_union_l, rewrite_trans, CON.
rewrite crE; relsf; rewrite irreflexive_union.
split; try apply CON.
apply irreflexive_seqC; rewrite !seqA.
arewrite (rfe ⊆ rf).
unfold TSO_Model.rb.
arewrite (rf ⨾ rf⁻¹ ⊆ ⦗fun _ => True⦘); relsf.
by cdes CON; cdes WF; cdes WF_RF.
arewrite (restr_eq_rel (loc lab) mo ⊆ mo).
arewrite (mo ⨾ [W] ⊆ mo).
arewrite (mo ⨾ mo ⊆ mo).
  apply rewrite_trans, CON.
apply CON.
Qed.

Proposition strong_Csc (CON: Consistent): 
  irreflexive (rb ⨾ mo ⨾ hb^? ⨾ [RMW_F] ⨾ hb^?).
Proof.
rewrite mo_dom; try by apply CON.
rewrite !seqA.
arewrite ([RMW_F] ⊆ [WF] ⨾ [RMW_F]).
  by solve_type_mismatchT 8.
sin_rewrite hb_mo_refl; try by apply CON.
arewrite (mo ⨾ mo^? ⊆ mo).
  by rewrite crE; relsf; apply inclusion_union_l, rewrite_trans, CON.
arewrite ([WF] ⨾ mo ⊆ mo).
unfold TSO_Model.hb; rewrite cr_of_ct; rewrite rtE.
rewrite seq_union_r, seq_id_r, seq_union_r, seq_union_r.
rewrite !irreflexive_union; splits.
- arewrite (mo ⨾ [RMW_F] ⊆ mo).
    by solve_type_mismatchT.
  apply CON.
- rewrite sb_rf_rfe; [|apply CON].
  do 2 rewrite <- seqA.
  rewrite seq_union_r, !seqA.
  rewrite irreflexive_union; split.
  + apply CON.
  + arewrite (mo ⨾ [RMW_F] ⊆ mo).
      by solve_type_mismatchT.
    arewrite (sb^? ⊆ hb^?).
    apply strong_Crfe, CON.
Qed.

Lemma rfe_inc_sbrf : rfe ⊆ sb ∪ rf.
Proof. unfold TSO_Model.rfe. basic_solver. Qed.

Lemma hb_refl : hb^? ≡ (sb ∪ rf)＊.
Proof. by unfold TSO_Model.hb; rewrite cr_of_ct. Qed.

Proposition tso_acyclicity (CON: Consistent): 
  acyclic ([R] ⨾ hb  
           ∪ (sb ∪ rf)＊ ⨾ rfe 
           ∪ hb ⨾ [F]
           ∪ [F] ⨾ hb
           ∪ rb ∪ mo).
Proof.
assert (transitive mo).
  by apply CON.
eapply min_cycle1; try by eapply CON.
edone.
by relsf.
{ 
  rewrite !inclusion_seq_eqv_l, !inclusion_seq_eqv_r.
  arewrite (rfe ⊆ sb ∪ rf).
  rels.
  rewrite irreflexive_seqC.
  relsf.
  rewrite !irreflexive_union; splits; try apply CON.
  by apply irr_mo_rb.
}
splits.
- rewrite !inclusion_seq_eqv_l.
  arewrite (rfe ⊆ sb ∪ rf).
  relsf.
  arewrite_false (rb ⨾ ⦗fun x : act_id => ~ (In x acts /\ is_wf lab x)⦘).
    rewrite rb_dom, rb_act; try by apply CON.
    by solve_type_mismatchT 6.
  arewrite_false (mo ⨾ ⦗fun x : act_id => ~ (In x acts /\ is_wf lab x)⦘).
    rewrite mo_dom, mo_act; try by apply CON.
    by solve_type_mismatchT 6.
  rewrite !inclusion_seq_eqv_r.
  arewrite (sb ⊆ sb ∪ rf) at 2.
  arewrite (rf ⊆ sb ∪ rf) at 4.
  unfold TSO_Model.hb; rels; red; rels; apply CON.
- rewrite !inclusion_seq_eqv_l, !inclusion_seq_eqv_r.
  arewrite (rfe ⊆ sb ∪ rf).
  rels.
  rewrite !irreflexive_union; splits; rewrite ?seqA; try by apply CON.
  rewrite rb_dom; try by apply CON.
  apply irreflexive_seqC; rewrite !seqA.
  red; solve_type_mismatchT.
- arewrite (fun __ => (__ ∪ rb ∪ mo) ⨾
           ⦗fun x : act_id => ~ (In x acts /\ is_wf lab x)⦘ ⊆ __ ).
  { relsf.
    arewrite_false (rb ⨾ ⦗fun x : act_id => ~ (In x acts /\ is_wf lab x)⦘).
    rewrite rb_dom, rb_act; try by apply CON.
    solve_type_mismatchT.
    arewrite_false (mo ⨾ ⦗fun x : act_id => ~ (In x acts /\ is_wf lab x)⦘).
    rewrite mo_dom, mo_act; try by apply CON.
    solve_type_mismatchT.
    rels.
    by rewrite !inclusion_seq_eqv_r; rels.
  }
  arewrite (fun __ => (__ ∪ rb ∪ mo) ⨾
         ⦗fun x : act_id => ~ (In x acts /\ is_wf lab x)⦘ ⊆ __).
  { relsf.
    repeat apply inclusion_union_l; rewrite ?seqA;
      try by rewrite ?inclusion_seq_eqv_r, ?inclusion_seq_eqv_l; rels; eauto 5 with rel.

    rewrite rb_dom, rb_act; try by apply CON.
    rewrite ?seqA.
    arewrite_false (⦗fun a : act_id => In a acts⦘ ⨾
      [W] ⨾ ⦗fun x : act_id => ~ (In x acts /\ is_wf lab x)⦘ ).
      solve_type_mismatchT.
    by relsf.
    rewrite mo_dom, mo_act; try by apply CON.
    rewrite ?seqA.
    arewrite_false (⦗fun a : act_id => In a acts⦘ ⨾
      [WF] ⨾ ⦗fun x : act_id => ~ (In x acts /\ is_wf lab x)⦘).
      solve_type_mismatchT.
    by relsf.
  }

arewrite (
⦗fun a : act_id => In a acts /\ is_wf lab a⦘ ⨾
   ([R] ⨾ hb ∪ (sb ∪ rf) ＊ ⨾ rfe
    ∪ hb ⨾ [F] ∪ [F] ⨾ hb) ⊆
(sb ∪ rf) ＊ ⨾ rfe
    ∪ hb ⨾ [F] ∪ [F] ⨾ hb).
  { relsf.
    repeat apply inclusion_union_l; rewrite ?seqA.
    arewrite_false (⦗fun a : act_id => In a acts /\ is_wf lab a⦘ ⨾ [R]).
      by solve_type_mismatchT.
    all: rewrite ?inclusion_seq_eqv_r, ?inclusion_seq_eqv_l.
    all: try basic_solver 8.
  }
  arewrite_id (⦗fun x : act_id => ~ (In x acts /\ is_wf lab x)⦘).
  arewrite_id (⦗fun a : act_id => In a acts /\ is_wf lab a⦘).
  arewrite_id ([R]).
  arewrite_id ([F]) at 1.
  arewrite_id ([F]) at 1.
  arewrite_id ([F]) at 3.
  arewrite_id ([F]) at 3.
  arewrite (rfe ⊆  sb ∪ rf) at 1.
  arewrite (rfe ⊆  sb ∪ rf) at 2.
  rels.
  rewrite crE.
  case_union_2 ⦗fun _ : act_id => True⦘ _; rels.

  { arewrite (rfe ⊆  sb ∪ rf).
    arewrite_id ([F]).
    rels; relsf.
    unfold TSO_Model.hb; rewrite ct_ct.
    rewrite !irreflexive_union; splits; rewrite ?seqA;
    rels; try by apply CON.
  }
  arewrite (hb ⊆ (sb ∪ rf) ＊) at 1.
  arewrite (((sb ∪ rf)＊ ∪ rb ∪ mo) ⨾ mo ⊆ ((sb ∪ rf)＊ ∪ rb) ⨾ mo).
    { relsf.
      repeat apply inclusion_union_l; rewrite ?seqA; relsf.
      by rewrite rtE; relsf. 
    }
  rewrite seq_union_l.
  rewrite !irreflexive_union; splits; rewrite ?seqA.
  { apply irreflexive_seqC; rewrite !seqA.
    arewrite (rfe ⊆  sb ∪ rf).
    arewrite_id ([F]).
    rels.
    by apply CON.
  }
  relsf.
  rewrite !irreflexive_union; splits; rewrite ?seqA.
  unfold TSO_Model.hb; rewrite rt_of_ct; rewrite <- hb_refl.
  by apply strong_Crfe.
  rels.
  arewrite (hb ⊆ (sb ∪ rf)＊). rewrite rt_of_rt.
   by arewrite ([F] ⊆ [RMW_F]); rewrite <- hb_refl; apply strong_Csc.
  arewrite (hb ⊆ (sb ∪ rf)＊).
  arewrite (mo  ⊆ mo ⨾ (sb ∪ rf)＊).
  rels.
  by arewrite ([F] ⊆ [RMW_F]); rewrite <- hb_refl; apply strong_Csc.
Qed.

End TSO_Properties.
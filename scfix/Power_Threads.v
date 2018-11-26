(******************************************************************************)
(** * Thread properties of the Power memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Power_Events Power_Model Power_Domains Power_Locations
  Power_Automation Power_Irreflexive.
Set Implicit Arguments.

Section Power_Threads.

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

Lemma internal_has_tid a : I a <-> tid a <> None.
Proof. split; ins; repeat red in H; unfold is_init, tid in *; desf. Qed.

Lemma st_or_not_st (x y : event) : same_thread x y \/ ~ same_thread x y.
Proof.
  unfold Events.same_thread.
  destruct (tid x);
  destruct (tid y);
  try (by right; red; ins; desf).
  destruct (classic(t=t0)); (left+right); try split; auto; red; ins; desf.
Qed.

Lemma internal_or_external (r : relation event) : 
  r ≡ r∙ ∪ r∘.
Proof.
  red; split; unfolder; ins; desf.
  assert (same_thread x y \/ ~ same_thread x y) by apply st_or_not_st.
  desf; basic_solver.
Qed.

Lemma st_transp : same_thread ≡ same_thread⁻¹.
Proof.
  by split; unfolder; unfold Events.same_thread; ins; desf; split; rewrite <- H0. 
Qed.

Lemma st_inv a b : same_thread a b <-> same_thread b a.
Proof.
  by split; unfolder; unfold Events.same_thread; ins; desf; split; rewrite <- H0. 
Qed.

Lemma st_trans : transitive same_thread.
Proof.
  by red; ins; unfold Events.same_thread in *; desf; split; eauto; rewrite <- H1.
Qed.

Lemma st_implies_tid a b (ST: same_thread a b) : exists i, tid a = Some i /\ tid b = Some i.
Proof. red in ST; desf; destruct (tid a); try contradiction; eexists; eauto. Qed.

Lemma sb_implies_tid (WF: Wf) a b (SB: sb a b) : tid b <> None.
Proof.
  cdes WF; cdes WF_SB; cdes WF_ACTS; clear - SB SB_TID.
  specialize (SB_TID a b SB).
  unfolder in *; desf.
  - (* internal *) by red in SB_TID0; desf; rewrite <- SB_TID1.
  - (* init *) by red in SB_TID; desf; apply internal_has_tid.
Qed.

Lemma sb_not_init_implies_st (WF: Wf) a b (SB: sb a b) 
  (N_INIT: ~ is_init a) : same_thread a b.
Proof.
  cdes WF; cdes WF_SB; clear - SB N_INIT SB_TID.
  specialize (SB_TID _ _ SB); unfolder in *; desf.
  contradict N_INIT. red in SB_TID; desf; auto.
Qed.

Lemma sb_implies_init_st (WF: Wf) a b (SB: sb a b) : 
  same_thread a b \/ is_init a.
Proof.
  unfold Events.same_thread.
  destruct (classic(is_init a)).
  - (* init a *) by right.
  - (* ~ init a*) left. by apply sb_not_init_implies_st.
Qed.

Lemma sb_fork_implies_st (WF: Wf) a b c (SB1: sb a b) (SB2: sb a c) 
  (N_INIT: ~ is_init a) : same_thread b c.
Proof.
  assert (same_thread a b).
    by apply sb_not_init_implies_st.
  assert (same_thread a c).
    by apply sb_not_init_implies_st.
  rewrite st_inv in H.
  by apply st_trans with a.
Qed.

Lemma sb_seq_implies_st (WF: Wf) a b c (SB1: sb a b) (SB2: sb b c) : 
  same_thread b c.
Proof.
  cdes WF; cdes WF_ACTS.
  assert (~ is_init b) by (by apply internal_has_tid, sb_implies_tid with a).
  by apply sb_not_init_implies_st.
Qed.

Lemma sb_diamond_implies_st (WF: Wf) a b b' c (SB1: sb a b) (SB1': sb a b')
  (SB2: sb b c) (SB2': sb b' c) : same_thread b b'.
Proof.
  cdes WF; cdes WF_ACTS.
  assert (~ is_init b) by (by apply internal_has_tid, sb_implies_tid with a).
  assert (~ is_init b') by (by apply internal_has_tid, sb_implies_tid with a).
  assert (same_thread b c) by (by apply sb_not_init_implies_st).
  assert (same_thread c b') by (by apply st_inv, sb_not_init_implies_st).
  by apply st_trans with c.
Qed.

Lemma st_not_trans (WF: Wf) a b c (N_ST_ab: ~ same_thread a b) 
  (ST_bc: same_thread b c) : ~ same_thread a c.
Proof.
  red; ins.
  contradict N_ST_ab.
  apply st_trans with c; auto.
  by apply st_inv.
Qed.

Lemma false_to_irr A (r : relation A) a:
  irreflexive r -> (r a a -> False).
Proof. ins; eapply H; eauto. Qed.

Lemma rf_st_implies_sb a b (WF: Wf) (SC: acyclic (sb|loc ∪ rf ∪ rb ∪ mo))
  (RF: rf a b) (ST: same_thread a b) : sb a b.
Proof.
  cdes WF; cdes WF_SB; cdes WF_DEPS; cdes WF_RF.
  clear - RF ST WF SB_T SB_TOT RF_LOC SC
      DATA_IN_SB ADDR_IN_SB CTRL_IN_SB CTRLI_IN_SB.
  apply st_implies_tid in ST; desf.
  assert (sb a b \/ sb b a) by
    (eapply SB_TOT; only 3: solve_irreflexive; red; split; eauto; act_solver).
  desf.
  specialize (RF_LOC a b RF).
  destruct SC with a; unfolder.
  apply t_trans with b.
  - eauto 6 using t_step.
  - apply t_step; repeat left; split; auto.
    red; split; auto.
    assert (R b) by type_solver.
    unfold Power_Model.R, is_r in H0.
    unfold Power_Events.loc. destruct (lab b); desf.
Qed.

Lemma st_implies_sb (WF: Wf) a b (ST: same_thread a b)
  (ACT_a: In a acts) (ACT_b: In b acts) (NEQ_ab: a <> b):
  sb a b \/ sb b a.
Proof.
  cdes WF; cdes WF_SB.
  unfold Events.same_thread in ST.
  desf.
  apply not_none_implies_some in ST.
  desf.
  apply SB_TOT with x; auto; split; auto.
  congruence.
Qed.

Lemma not_sb2_implies_not_st (WF: Wf) a b (ACT_a: In a acts) (ACT_b: In b acts)
  (NEQ: a <> b) (N_SB1: ~ sb a b) (N_SB2: ~ sb b a) : 
    ~ same_thread a b.
Proof. red; ins; apply st_implies_sb in H; desf; eauto. Qed.

Lemma rmw_implies_st (WF: Wf) : rmw ⊆ same_thread.
Proof.
  cdes WF; cdes WF_RMW. clear - WF RMW_IMM.
  red; ins.
  assert (I x) by type_solver.
  apply RMW_IMM in H.
  red in H; desf.
  by apply sb_not_init_implies_st.
Qed.

End Power_Threads.

(* Automation *)
Ltac not_init_producer :=
  match goal with | G: power_execution |- _ =>
    let apply_i := (fun a => not_proven (I a); assert (I a) by type_solver) in
    repeat match goal with | a: event |- _ => apply_i a end
  end.

Ltac thread_producer :=
  match goal with | G: power_execution |- _ =>
    let apply_st := (fun x y t => not_proven (same_thread x y);
      assert (same_thread x y) by (by eapply t; eauto)) 
    with apply_st_with := (fun x y z t => not_proven (same_thread x y);
      assert (same_thread x y) by (by apply t with z; auto)) in
    repeat match goal with
    | [_:(same_thread ?a ?b) |- _] => apply_st b a st_inv
    | [_:(same_thread ?a ?b), _:(same_thread ?b ?c) |- _] => 
      apply_st_with a c b st_trans
    | [_:(sb G ?a ?b), _:(~ is_init ?a) |- _] => 
      apply_st a b sb_not_init_implies_st
    | [_:(sb G ?a ?b), _:(I ?a) |- _] => 
      apply_st a b sb_not_init_implies_st
    | [_:(rmw G ?a ?b) |- _] => 
      apply_st a b rmw_implies_st
    end
  end.

Ltac thread_solver :=
  match goal with | G: power_execution |- _ =>
    not_init_producer;
    thread_producer;
    match goal with
    | [_:?G |- ?G] => done
    | [_:(same_thread ?b ?a) |- same_thread ?a ?b] => by apply st_inv
    | [_:(same_thread ?a ?b), _:(same_thread ?b ?c) |- same_thread ?a ?c] => 
      by apply st_trans with b; auto
    | [ |- exists _, tid ?a = Some _ /\ tid ?b = Some _] =>
      by eapply st_implies_tid; eauto
    | [_:(same_thread ?a ?b), _:(tid ?a = Some _) |- tid ?b = Some _ ] =>
      assert (exists i, tid a = Some i /\ tid b = Some i) 
        by (by eapply st_implies_tid; eauto);
      desf; eauto
    | [_:(~ sb G ?a ?b), _:(~ sb G ?b ?a) |- ~ same_thread ?a ?b] =>
      red; ins; thread_solver
    | |- ~ same_thread ?a ?b => red; ins; thread_solver
    | [_:(~ sb G ?a ?b), _:(~ sb G ?b ?a), ST_:(same_thread ?a ?b) |- False] =>
      eapply st_implies_sb in ST_; desf; eauto; solve_irreflexive
    | |- sb G ?a ?b \/ sb G ?b ?a => 
      eapply st_implies_sb; desf; eauto; try act_solver; try (solve_irreflexive)
    | [ |- False] => contradiction
    end
  end.

(******************************************************************************)
(** ** Cycle Detection *)
(******************************************************************************)
Ltac cycle_detector0 a b :=
  match goal with | G: power_execution |- _ =>
    match goal with [CON:PowerConsistent G |- False] =>
      assert (_C_ := CON); destruct _C_ as (_&SC&_); unnw;
      apply SC with a; apply t_trans with b;
        loc_producer; unfolder; same_loc_producer;
        eauto 20 using t_step, t_trans;
      clear SC
    end
  end.

Ltac cycle_detector_unknown a :=
  match goal with [b:event |- False] =>
    (match goal with [_:_ _ a b |- _] => idtac end ||
     match goal with [_:_ _ b a |- _] => idtac end);
    by cycle_detector0 a b
  end.

Ltac cycle_detector :=
  match goal with | G: power_execution |- _ =>
    desf;
    match goal with
    | |- ?a <> ?b => red; ins; subst a; cycle_detector_unknown b
    | |- sb G ?a ?b => 
      assert (~ sb G b a) by cycle_detector;
      assert (sb G a b \/ sb G b a) by cycle_detector;
      desf
    | |- mo G ?a ?b =>
      remember (loc (lab G) a) as l;
      assert (~ mo G b a) by cycle_detector;
      assert (mo G a b \/ mo G b a) by cycle_detector;
      desf
    | |- ~ sb G ?a ?b => red; ins; cycle_detector0 a b
    | |- ~ mo G ?a ?b => red; ins; cycle_detector0 a b
    | |- sb G ?a ?b \/ sb G ?b ?a =>
      apply st_implies_sb; auto; try act_solver;
      try first [by solve_irreflexive | by cycle_detector]
    | |- mo G ?a ?b \/ mo G ?b ?a =>
      eapply writes_same_loc_implies_mo; eauto;
      repeat match goal with
      | |- (restrict_location G (W G) _) _ => split; try type_solver; loc_solver
      | |- In _ (acts G) => act_solver
      end;
      cycle_detector
    end
  end.
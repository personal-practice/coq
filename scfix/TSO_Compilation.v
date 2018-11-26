(******************************************************************************)
(** * Compilation correctness of the TSO memory model. *)
(******************************************************************************)
Require Import Classical List Relations Peano_dec.
Require Import Hahn.
Require Import Basic TSO_Model TSO_Properties.

(** This following theorem essentially proves the soundness of compilation to TSO: 
every TSO-CONerent execution graph can be mapped to a PromiseFree-CONerent execution graph.
We note that the condition [Cscu] of TSO CONerence is not used in the proof. *)
(*
Theorem ConsistentTSO_implies_CONerentPF acts sb rmw rf mo :
  ConsistentTSO acts sb rmw rf mo ->
  CONerent acts sb rmw rf (restr_eq_rel loc (restr_rel is_write mo))
           (restr_rel is_sc_fence mo).
Proof.
  unfold ConsistentTSO, CONerent, Wf, WfTSO; ins; desc; unnw.
  clear Cscu.

  assert (INC: inclusion (rf ⨾ tc (sb +++ rf)) (tc (sb +++ rf))).
    by eauto using inclusion_seq_mon, inclusion_r_t_t with rel. 
  assert (INC2: inclusion (clos_refl rf ⨾ tc (sb +++ rf)) (tc (sb +++ rf))).
    by eauto using inclusion_seq_mon, inclusion_r_t_t with rel. 

  assert (TOT:  is_total (fun a => In a acts /\ is_sc_fence a) (restr_rel is_sc_fence mo)).
    by unfold restr_rel; red in WF_MO; desc; red; ins; desf; eapply MO_TOT in NEQ; desf; eauto.
  splits; try done.
{
  red in WF_MO; desc; red; splits; eauto using restr_eq_trans, restr_rel_trans;
  unfold restr_eq_rel, restr_rel; ins; desf; eauto.
  unfold loc in *; destruct a as [??[]]; simpls; destruct b as [??[]]; simpls; vauto. 
  red; ins; desf; eauto.
  red; ins; desf; eapply MO_TOT in NEQ; desf; eauto; [left|right]; splits; eauto; congruence.
}
{
  red in WF_MO; desc; red; splits; eauto using restr_eq_trans, restr_rel_trans;
  unfold restr_eq_rel, restr_rel; ins; desf; eauto.
  red; ins; desf; eauto.
}

  all: red. 
  by rewrite hb_in_sb_rf, inclusion_restr_eq, inclusion_restr, INC; try done.
  by rewrite hb_in_sb_rf, inclusion_restr_eq, inclusion_restr; try done.
  by rewrite <- seqA, irreflexive_seqC, <- seqA, hb_in_sb_rf.
  
  by rewrite inclusion_seq_eqv_l, hb_in_sb_rf, <- !seqA, irreflexive_seqC, !seqA, INC, <- seqA. 
  by rewrite inclusion_seq_eqv_l, hb_in_sb_rf, <- !seqA, irreflexive_seqC, !seqA, INC, <- seqA. 
  by rewrite inclusion_seq_eqv_l, !hb_in_sb_rf, <- !seqA, irreflexive_seqC, !seqA, ct_ct, INC, <- seqA.

{
  rewrite hb_in_sb_rf, <- (seqA (clos_refl rf)), INC2, <- !seqA, irreflexive_seqC, !seqA; try done.
  intros a (b & B & c & C & d & D & e & E & A). 
  assert (MO: mo c d). {
    red in WF_MO; desc. 
    assert (NEQ: c <> d) by (intro; desf; eauto). 
    eapply MO_TOT in NEQ; desf; eauto.
        by edestruct Cww; vauto.
      by unfold restr_eq_rel, restr_rel in C; desc; eauto.
    by unfold restr_eq_rel, restr_rel in E; desc; eauto.
  }
  clear D; red in B; desf.
    apply inclusion_restr_eq, inclusion_restr in C; apply inclusion_restr in E.
    by eapply (Cww b); exists e; split; eauto; do 2 (eapply WF_MO; eauto).
  eapply sb_rf_to_ext_end in A; eauto; red in A; desf.
    eapply (Cscf a); exists c; split; vauto; exists e; split; vauto. 
      by eapply WF_MO; eauto; eapply E.
    by eexists e; split; vauto; split; ins; eapply E. 
  destruct A as (f & F & g & G & [A|A]); subst.
    red in WF_RF; red in G; desc. 
    assert (f = b) by (eapply RF_FUN; eauto); subst.
    assert (mo b e).
      apply inclusion_restr_eq, inclusion_restr in C; apply inclusion_restr in E.
      do 2 (eapply WF_MO; eauto).
    by eapply clos_refl_transE in F; desf; [eapply WF_MO | apply (Cww b); exists e]; eauto.
  eapply (Crfe a); exists c; split; vauto; eexists f; split; vauto.
  red in E; desf; eapply WF_MO; eauto.
  eapply clos_refl_transE in F; desf; eapply WF_MO; eauto.
  red in WF_MO; desc. 
  assert (NEQ: e <> f) by (intro; desf; eauto). 
  red in G; desc.
  eapply MO_TOT in NEQ; desf; eauto.
    by edestruct Cww; vauto.
  by red in WF_RF; desc; eauto.
}

 red in WF_MO; desc.
 eapply acyclic_decomp_u_total; eauto. 
   by unfold restr_rel; ins; desf; eauto 8. 
   by rewrite inclusion_restr, ct_of_trans, irreflexive_seqC, crtE, 
      seq_union_r, seq_id_r, irreflexive_union.
Qed.
*)

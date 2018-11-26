(******************************************************************************)
(** * Thread properties of the Power memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Dom RC11_Events RC11_Model.
Set Implicit Arguments.

Section Threads.

Variable G : execution.

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
(* Relations *)
Notation "'eco'" := G.(eco).
Notation "'rb'" := G.(rb).
Notation "'hb'" := G.(hb).
Notation "'psc_f'" := G.(psc_f).
Notation "'psc'" := G.(psc).
Notation "'sb_neq_loc'" := G.(sb_neq_loc).
Notation "'deps'" := G.(deps).

Lemma st_or_not_st (x y : event) : same_thread x y \/ ~ same_thread x y.
Proof. tauto. Qed.

Lemma internal_or_external (r : relation event) : 
  r ≡ r∙ ∪ r∘.
Proof. red; split; unfolder; ins; desf; tauto. Qed.

Lemma st_sym : same_thread ≡ same_thread⁻¹.
Proof. unfold same_thread; unfolder; split; ins; desf; splits; try done; congruence. Qed.

Lemma st_inv a b : same_thread a b <-> same_thread b a.
Proof. split; eapply st_sym. Qed.

Lemma st_trans : transitive same_thread.
Proof. unfold same_thread; intro; ins; desf; splits; eauto; congruence. Qed.

Lemma st_tid a b : same_thread a b <-> exists i, tid a = Some i /\ tid b = Some i.
Proof. split; ins; unfold same_thread in *; desf.
by destruct (tid a); eauto.
by splits; destruct (tid a); ins; congruence.
 Qed.

Lemma st_not_inita a b : same_thread a b -> ~is_init a.
Proof. ins; unfold same_thread in *; desf; destruct a; eauto. Qed.

Lemma st_not_initb a b : same_thread a b -> ~is_init b.
Proof. ins; unfold same_thread in *; desf; destruct b; eauto. Qed.

Lemma sb_implies_tid (WF: Wf G) a b (SB: sb a b) : tid b <> None.
Proof.
cdes WF; cdes WF_SB.
apply SB_TID in SB.
unfolder in *; unfold same_thread, init_pair, is_init in *; desf.
by rewrite <- SB1.
Qed.

Lemma sb_not_init_implies_st (WF: Wf G) a b (SB: sb a b) 
  (N_INIT: ~ is_init a) : same_thread a b.
Proof.
cdes WF; cdes WF_SB; eapply SB_TID in SB.
unfold init_pair in *.
generalize SB, SB_TID; basic_solver.
Qed.

Lemma sb_implies_init_st (WF: Wf G) a b (SB: sb a b) : 
  same_thread a b \/ is_init a.
Proof.
generalize (sb_not_init_implies_st WF a b SB); tauto.
Qed.

Lemma sb_fork_implies_st (WF: Wf G) a b c (SB1: sb a b) (SB2: sb a c) 
  (N_INIT: ~ is_init a) : same_thread b c.
Proof.
generalize (sb_not_init_implies_st WF a b SB1).
generalize (sb_not_init_implies_st WF a c SB2).
ins; eapply st_trans; eauto.
apply st_sym; basic_solver.
Qed.

Lemma no_sb_to_init (WF: Wf G) a b (SB: sb a b) :  ~is_init b.
Proof.
cdes WF; cdes WF_SB.
apply SB_TID in SB.
unfolder in *; desf.
all: unfold same_thread, init_pair, is_init in *; desf.
Qed.

Lemma no_rmw_to_init (WF: Wf G) a b (RMW: rmw a b) :  ~is_init b.
Proof.
cdes WF; cdes WF_RMW.
eapply no_sb_to_init; try done.
eby apply rmw_in_sb.
Qed.

Lemma sb_seq_implies_st (WF: Wf G) a b c (SB1: sb a b) (SB2: sb b c) : 
  same_thread b c.
Proof.
apply  sb_not_init_implies_st; try done.
eby eapply no_sb_to_init.
Qed.

Lemma sb_diamond_implies_st (WF: Wf G) a b b' c (SB1: sb a b) (SB1': sb a b')
  (SB2: sb b c) (SB2': sb b' c) : same_thread b b'.
Proof.
apply st_trans with c.
eapply sb_seq_implies_st; try edone.
apply st_inv; eapply sb_seq_implies_st; try edone.
Qed.

Lemma st_not_trans (WF: Wf G) a b c (N_ST_ab: ~ same_thread a b) 
  (ST_bc: same_thread b c) : ~ same_thread a c.
Proof.
  red; ins.
  contradict N_ST_ab.
  apply st_trans with c; auto.
  by apply st_inv.
Qed.

Lemma st_implies_sb (WF: Wf G) a b (ST: same_thread a b)
  (ACT_a: In a acts) (ACT_b: In b acts) (NEQ_ab: a <> b):
  sb a b \/ sb b a.
Proof.
  cdes WF; cdes WF_SB.
  unfold same_thread in ST.
  desf.
  apply not_none_implies_some in ST.
  desf.
  apply SB_TOT with x; auto; split; auto.
  congruence.
Qed.

Lemma rf_st_implies_sb a b (WF: Wf G) (COH: Coherent G)
  (RF: rf a b) (ST: same_thread a b) : sb a b.
Proof.
cdes WF.
  assert (sb a b \/ sb b a).
  { apply st_implies_sb; eauto.
     eapply rf_acta; eauto.
     eapply rf_actb; eauto.
     eby intro; subst; eapply irr_rf.
  }
  desf.
  exfalso.
  eapply COH; eexists; splits.
  eby eapply sb_in_hb.
  eby right; eapply rf_in_eco.
Qed.

Lemma not_sb2_implies_not_st (WF: Wf G) a b (ACT_a: In a acts) (ACT_b: In b acts)
  (NEQ: a <> b) (N_SB1: ~ sb a b) (N_SB2: ~ sb b a) : 
    ~ same_thread a b.
Proof. red; ins; apply st_implies_sb in H; desf; eauto. Qed.

Lemma no_rmw_from_init (WF: Wf G) a b (RMW: rmw a b) :  ~is_init a.
Proof.
cdes WF; cdes WF_ACTS.
apply rmw_doma in RMW; eauto.
destruct a; eauto.
specialize (LAB_INIT l).
unfold init_label in *.
exfalso; generalize RMW, LAB_INIT.
solve_type_mismatch.
Qed.

Lemma rmw_implies_st (WF: Wf G) : rmw ⊆ same_thread.
Proof.
cdes WF; cdes WF_RMW. clear - WF RMW_IMM.
red; ins.
apply sb_not_init_implies_st; eauto.
- by red in RMW_IMM; apply RMW_IMM.
- eby eapply no_rmw_from_init.
Qed.


(******************************************************************************)
(** ** SB immediate vs. adjacent  *)
(******************************************************************************)
Lemma sb_tot1 (WF: Wf G) : ⦗I⦘ ;; sb ;; sb^{-1} ⊆ sb^? ∪ sb^{-1}.
Proof.
cdes WF; cdes WF_SB.
rewrite SB_TID at 2; relsf.
rewrite transp_union; relsf.
unionL; cycle 1.
- unionR right.
  unfolder; ins; desf.
  eby apply SB_INIT; unfolder; splits; [unfold init_pair in *; desf; splits; eauto| eapply sb_acta].
- rewrite SB_TID at 1; relsf.
  unionL; [|solve_type_mismatch].
  clear_equivs ⦗I⦘.
  unfolder; ins; desf.
  cut (x <> y -> sb x y \/ sb y x).
  tauto.
  apply st_implies_sb; [done| |eapply sb_acta; eauto| eapply sb_acta; eauto].
  eapply st_trans; try edone.
  eapply st_sym; edone.
Qed.

Lemma sb_tot2  (WF: Wf G) : sb^{-1} ;; ⦗I⦘ ;; sb ⊆ sb^? ∪ sb^{-1}.
Proof.
cdes WF; cdes WF_SB.
rewrite SB_TID at 1; rewrite transp_union; relsf.
unionL; [|solve_type_mismatch].
rewrite SB_TID at 2; relsf.
unionL; [|solve_type_mismatch].
  clear_equivs ⦗I⦘.
  unfolder; ins; desf.
  cut (x <> y -> sb x y \/ sb y x).
  tauto.
  apply st_implies_sb; [done| |eapply sb_actb; eauto| eapply sb_actb; eauto].
  eapply st_trans; try edone.
  eapply st_sym; edone.
Qed.

Lemma sb_immediate_adjacent  (WF: Wf G) :
  forall a b, I a -> immediate sb a b <-> adjacent sb a b /\ sb a b.
Proof.
by apply immediate_adjacent; [apply sb_tot1|apply sb_tot2|apply WF|apply WF].
Qed.

End Threads.

(* Automation *)
Ltac thread_producer :=
  match goal with | G: execution |- _ =>
    let apply_st := (fun x y t => not_proven (same_thread G x y);
      assert (same_thread G x y) by (by eapply t; eauto)) 
    with apply_st_with := (fun x y z t => not_proven (same_thread G x y);
      assert (same_thread G x y) by (by apply t with z; auto)) in
    repeat match goal with
    | [_:(same_thread G ?a ?b) |- _] => apply_st b a st_inv
    | [_:(same_thread G ?a ?b), _:(same_thread G ?b ?c) |- _] => 
      apply_st_with a c b st_trans
    | [_:(sb G ?a ?b), _:(~ is_init _ ?a) |- _] => 
      apply_st a b sb_not_init_implies_st
    | [_:(sb G ?a ?b), _:(I G ?a) |- _] => 
      apply_st a b sb_not_init_implies_st
    | [_:(rmw G ?a ?b) |- _] => 
      apply_st a b rmw_implies_st
    end
  end.

Ltac thread_solver :=
  match goal with | G: execution |- _ =>
    thread_producer;
    match goal with
    | [_:?G |- ?G] => done
    | [_:(same_thread G ?b ?a) |- same_thread G ?a ?b] => by apply st_inv
    | [_:(same_thread G ?a ?b), _:(same_thread G ?b ?c) |- same_thread G ?a ?c] => 
      by apply st_trans with b; auto
    | [ |- exists _, tid G ?a = Some _ /\ tid G ?b = Some _] =>
      by apply st_tid; auto
    | [_:(same_thread G ?a ?b), _:(tid G ?a = Some _) |- tid G ?b = Some _ ] =>
      assert (exists i, tid G a = Some i /\ tid G b = Some i) 
        by (by apply st_tid);
      desf; eauto
    | [_:(~ sb G ?a ?b), _:(~ sb G ?b ?a) |- ~ same_thread G ?a ?b] =>
      red; ins; thread_solver G
    | |- ~ same_thread G ?a ?b => red; ins; thread_solver
    | [_:(~ sb G ?a ?b), _:(~ sb G ?b ?a), ST_:(same_thread G ?a ?b) |- False] =>
      apply st_implies_sb in ST_; desf; auto
    | |- sb G ?a ?b \/ sb G ?b ?a => 
      apply st_implies_sb; desf; eauto
    | [ |- False] => contradiction
    end
  end.
(******************************************************************************)
(** * Reasoning with multiple Power executions. *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Power_Events  Power_Model Power_Domains Power_Locations
  Power_Automation Power_Irreflexive Power_Threads Power_Helpers.

Set Implicit Arguments.
Remove Hints plus_n_O.

(* Unfold databases *)
Hint Unfold rb sync lwsync fence prop1 prop2 prop hb : derived_rels.
Hint Unfold Wf WfDEPS WfACTS WfSB WfRF WfMO WfRMW : wf_unfold.

(* Notations *)
Notation "G ⟪ r ⟫ G'" := (G.(r) ≡ G'.(r)) (at level 1).
Notation "G [ l ]  G'" := (G.(l) = G'.(l)) (at level 1).
Notation "rel |loc" := (fun G => (rel G) ∩ (same_loc G)) (at level 1).

(* Tactics *)
Ltac equiv_solver :=
  let solve_g := (fun g g' => 
    subst; (idtac + destruct g); (idtac + destruct g'); simpl; splits; auto
  ) in
  match goal with 
  | |- _ ?g ≡ _ ?g' => solve_g g g'
  | |- _ ?g = _ ?g' => solve_g g g'
  end.

Tactic Notation "assert" "{" ident(name) "}" uconstr(H) :=
  assert (name: H) by equiv_solver.

Tactic Notation "unfold_all" :=
  autounfold with derived_rels type_unfold.
Tactic Notation "unfold_all" "in" hyp(H):=
  autounfold with derived_rels type_unfold in H.
Tactic Notation "unfold_all" "in" "*":=
  autounfold with derived_rels type_unfold in *.

Tactic Notation "surround" "<" constr(s) ">" constr(x) "<" constr(s') ">" "{" constr(g) "}" :=
  arewrite (x g ⊆ ⦗s g⦘ ⨾ x g ⨾ ⦗s' g⦘) by domain_solver.
Tactic Notation "surround" "<" constr(s) ">" constr(x) "{" constr(g) "}" :=
  arewrite (x g ⊆ ⦗s g⦘ ⨾ x g) by domain_solver.
Tactic Notation "surround" uconstr(x) "<" uconstr(s) ">" "{" uconstr(g) "}" :=
  arewrite (x g ⊆ x g ⨾ ⦗s g⦘) by domain_solver.

Section Power_Executions.

Variables G G' : power_execution.

(* Relational equivalence helpers *)
Lemma rb_if_rf_mo (RF: G ⟪rf⟫ G') (MO: G ⟪mo⟫ G') : 
  G ⟪rb⟫ G'.
Proof. by unfold_all in *; rewrite RF, MO. Qed.

Lemma sync_if_sb (LAB: G [lab] G') (SB: G ⟪sb⟫ G') : 
  G ⟪sync⟫ G'.
Proof. by unfold_all in *; rewrite SB, LAB. Qed.

Lemma lwsync_if_sb (LAB: G [lab] G') (SB: G ⟪sb⟫ G') : 
  G ⟪lwsync⟫ G'.
Proof. by unfold_all in *; rewrite SB, LAB. Qed.

Lemma fence_if_sb (LAB: G [lab] G') (SB: G ⟪sb⟫ G') : 
  G ⟪fence⟫ G'.
Proof.
  unfold fence.
  arewrite (G ⟪sync⟫ G') by apply sync_if_sb.
  arewrite (G ⟪lwsync⟫ G') by apply lwsync_if_sb.
Qed.

Lemma fence_if_sync_lwsync (S1: G ⟪sync⟫ G') (S2: G ⟪lwsync⟫ G') : 
  G ⟪fence⟫ G'.
Proof. by unfold fence; rewrite S1, S2. Qed.

Lemma hb_if_ppo_sb_rf (LAB: G [lab] G')
  (PPO: G ⟪ppo⟫ G') (SB: G ⟪sb⟫ G') (RF: G ⟪rf⟫ G'):
  G ⟪hb⟫ G'.
Proof.
  unfold hb; rewrite PPO, RF.
  arewrite (G ⟪fence⟫ G') by apply fence_if_sb.
Qed.

Lemma hb_if_ppo_fence_rf (LAB: G [lab] G')
  (PPO: G ⟪ppo⟫ G') (FE: G ⟪fence⟫ G') (RF: G ⟪rf⟫ G'):
  G ⟪hb⟫ G'.
Proof.
  by unfold hb; rewrite PPO, RF, FE.
Qed.

Lemma prop1_if_rf_sb_ppo (LAB: G [lab] G')
  (RF: G ⟪rf⟫ G') (SB: G ⟪sb⟫ G') (PPO: G ⟪ppo⟫ G') :
  G ⟪prop1⟫ G'.
Proof.
  unfold prop1; rewrite RF.
  arewrite (G ⟪fence⟫ G') by apply fence_if_sb.
  arewrite (G ⟪hb⟫ G') by apply hb_if_ppo_sb_rf.
  by unfold_all in *; rewrite LAB.
Qed.

Lemma prop1_if_rf_fence_hb (LAB: G [lab] G')
  (RF: G ⟪rf⟫ G') (FE: G ⟪fence⟫ G') (HB: G ⟪hb⟫ G') :
  G ⟪prop1⟫ G'.
Proof.
  unfold prop1; rewrite RF, FE, HB.
  by unfold_all in *; rewrite LAB.
Qed.

Lemma prop2_if_mo_rf_sb_ppo (LAB: G [lab] G')
  (MO: G ⟪mo⟫ G') (RF: G ⟪rf⟫ G') (SB: G ⟪sb⟫ G') (PPO: G ⟪ppo⟫ G') :
  G ⟪prop2⟫ G'.
Proof.
  unfold prop2; rewrite MO, RF.
  arewrite (G ⟪rb⟫ G') by apply rb_if_rf_mo.
  arewrite (G ⟪fence⟫ G') by apply fence_if_sb.
  arewrite (G ⟪sync⟫ G') by apply sync_if_sb.
  arewrite (G ⟪hb⟫ G') by apply hb_if_ppo_sb_rf.
Qed.

Lemma prop2_if_mo_rf_fence_hb_sync (LAB: G [lab] G')
  (MO: G ⟪mo⟫ G') (RF: G ⟪rf⟫ G') (FE: G ⟪fence⟫ G') (HB: G ⟪hb⟫ G') 
  (SY: G ⟪sync⟫ G'):
  G ⟪prop2⟫ G'.
Proof.
  unfold prop2; rewrite MO, RF, FE, HB, SY.
  arewrite (G ⟪rb⟫ G') by apply rb_if_rf_mo.
Qed.

Lemma prop_if_mo_rf_sb_ppo (LAB: G [lab] G')
  (MO: G ⟪mo⟫ G') (RF: G ⟪rf⟫ G') (SB: G ⟪sb⟫ G') (PPO: G ⟪ppo⟫ G') :
  G ⟪prop⟫ G'.
Proof.
  unfold prop.
  arewrite (G ⟪prop1⟫ G') by apply prop1_if_rf_sb_ppo.
  arewrite (G ⟪prop2⟫ G') by apply prop2_if_mo_rf_sb_ppo.
Qed.

Lemma prop_if_mo_rf_hb_sync_fence (LAB: G [lab] G')
  (MO: G ⟪mo⟫ G') (RF: G ⟪rf⟫ G') (HB: G ⟪hb⟫ G')
  (SY: G ⟪sync⟫ G') (FE: G ⟪fence⟫ G') :
  G ⟪prop⟫ G'.
Proof.
  unfold prop.
  arewrite (G ⟪prop1⟫ G') by apply prop1_if_rf_fence_hb.
  arewrite (G ⟪prop2⟫ G') by apply prop2_if_mo_rf_fence_hb_sync.
Qed.

Lemma prop_if_prop1_prop2 (P1: G ⟪prop1⟫ G') (P2: G ⟪prop2⟫ G'):
  G ⟪prop⟫ G'.
Proof. by unfold prop; rewrite P1, P2. Qed.

Lemma ppo_if_ii_ic (LAB: G [lab] G') (II: G ⟪ii⟫ G') (IC: G ⟪ic⟫ G') :
  G ⟪ppo⟫ G'.
Proof. by unfold ppo; rewrite II, IC; unfold_all in *; rewrite LAB. Qed.

Lemma ii_if_ii0_ci0_cc0 (HII: G ⟪ii0⟫ G') (HCI: G ⟪ci0⟫ G') (HCC: G ⟪cc0⟫ G'):
  G ⟪ii⟫ G'.
Proof.
  red; split; red; ins;
  eapply ii_rec with (P:=ii _) (P0:=ic _) (P1:=ci _) (P2:=cc _);
  auto; ins; vauto;
  try (apply HII in H0);
  try (apply HCI in H0);
  try (apply HCC in H0);
  vauto.
Qed.

Lemma ic_if_ii0_ci0_cc0 (HII: G ⟪ii0⟫ G') (HCI: G ⟪ci0⟫ G') (HCC: G ⟪cc0⟫ G'):
  G ⟪ic⟫ G'.
Proof.
  red; split; red; ins.
  - apply ic_rec with (G:=G) (P:=ii G') (P0:=ic G') (P1:=ci G') (P2:=cc G');
    auto; ins; vauto;
    try (apply HII in H0);
    try (apply HCI in H0);
    try (apply HCC in H0);
    vauto.
  - apply ic_rec with (G:=G') (P:=ii G) (P0:=ic G) (P1:=ci G) (P2:=cc G);
    auto; ins; vauto;
    try (apply HII in H0);
    try (apply HCI in H0);
    try (apply HCC in H0);
    vauto.
Qed.

(* Consistency equivalence helpers *)
Definition consistency_iso G G' :=
  G [lab] G' /\
  G ⟪sb⟫ G' /\
  G ⟪mo⟫ G' /\
  G ⟪rf⟫ G' /\
  G ⟪rmw⟫ G' /\
  G ⟪ppo⟫ G'.

Lemma consistent_alt (WF: Wf G /\ Wf G'):
   consistency_iso G G' -> (PowerConsistent G' -> PowerConsistent G).
Proof.
  unfold consistency_iso, PowerConsistent.
  ins; desf; unnw.
  assert (RB: G ⟪rb⟫ G') by (by apply rb_if_rf_mo).
  assert (PR: G ⟪prop⟫ G') by (by apply prop_if_mo_rf_sb_ppo).
  assert (HB: G ⟪hb⟫ G') by (by apply hb_if_ppo_sb_rf).
  assert (SL: G ⟪same_loc⟫ G') by (by unfold Power_Model.same_loc; rewrite H).
  by splits; auto; rewrite ?H, ?H0, ?H1, ?H2, ?H3, ?H4, ?RB, ?PR, ?HB, ?SL.
Qed.

Definition consistency_iso2 G G' :=
  G [lab] G' /\
  G ⟪mo⟫ G' /\
  G ⟪rf⟫ G' /\
  G ⟪rmw⟫ G' /\
  G ⟪ii0⟫ G' /\
  G ⟪ci0⟫ G' /\
  G ⟪cc0⟫ G' /\
  G ⟪sync⟫ G' /\
  G ⟪fence⟫ G' /\
  G ⟪sb|loc⟫ G'.

Lemma consistent_alt2 (WF: Wf G /\ Wf G'):
   consistency_iso2 G G' -> (PowerConsistent G' -> PowerConsistent G).
Proof.
  unfold consistency_iso2, PowerConsistent.
  ins; desf.
  assert (II: G ⟪ii⟫ G') by (by apply ii_if_ii0_ci0_cc0).
  assert (IC: G ⟪ic⟫ G') by (by apply ic_if_ii0_ci0_cc0).
  assert (PPO: G ⟪ppo⟫ G') by (by apply ppo_if_ii_ic).
  assert (RB: G ⟪rb⟫ G') by (by apply rb_if_rf_mo).
  assert (HB: G ⟪hb⟫ G') by (by apply hb_if_ppo_fence_rf).
  assert (PR: G ⟪prop⟫ G') by (by apply prop_if_mo_rf_hb_sync_fence).
  splits; auto; by rewrite ?H0, ?H1, ?H2, ?H3, ?H4, ?H5, ?H6, ?H7, ?H8,
                           ?RB, ?ST, ?FE, ?HB, ?PR, ?PPO.
Qed.

Definition consistency_iso3 G G' :=
  G [lab] G' /\
  G ⟪mo⟫ G' /\
  G ⟪rf⟫ G' /\
  G ⟪rmw⟫ G' /\
  G ⟪prop1⟫ G' /\
  G ⟪prop2⟫ G' /\
  G ⟪hb⟫ G' /\
  G ⟪sb|loc⟫ G'.

Lemma consistent_alt3 (WF: Wf G /\ Wf G'):
   consistency_iso3 G G' -> (PowerConsistent G' -> PowerConsistent G).
Proof.
  unfold consistency_iso3, PowerConsistent.
  ins; desf.
  assert (RB: G ⟪rb⟫ G') by (by apply rb_if_rf_mo).
  assert (PR: G ⟪prop⟫ G') by (by apply prop_if_prop1_prop2).
  splits; auto; by rewrite ?H0, ?H1, ?H2, ?H3, ?H4, ?H5, ?H6, ?RB, ?PR.
Qed.

End Power_Executions.

(******************************************************************************)
(** * Domains of the Power memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Power_Events Power_Model.

Set Implicit Arguments.

Section Power_Domains.

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

Lemma rewrite_internal (r : relation event) : r∙ ⊆ r.
Proof. unfolder; ins; desf. Qed.

Lemma eqv_doma A (S: A -> Prop) :  doma ⦗S⦘  S.
Proof. apply doma_helper; unfolder; ins; desf; eexists; splits; eauto. Qed.

Lemma eqv_domb A (S: A -> Prop) :  domb ⦗S⦘  S.
Proof. apply domb_helper; unfolder; ins; desf; eexists; splits; eauto. Qed.

Lemma trivial_doma A (r: relation A) (S: A -> Prop) : 
  doma (⦗S⦘ ⨾ r) S.
Proof. apply doma_helper; rels. Qed.

Lemma trivial_domb A (r: relation A) (S: A -> Prop) : 
  domb (r ⨾ ⦗S⦘) S.
Proof. apply domb_helper; rewrite seqA; rels.  Qed.

Lemma rewrite_doma A (r: relation A) (S: A -> Prop) : 
  doma r S <-> r ⊆ ⦗S⦘ ⨾ r.
Proof. split; apply doma_helper. Qed.

Lemma rewrite_domb A (r: relation A) (S: A -> Prop) : 
  domb r S <-> r ⊆ r ⨾ ⦗S⦘.
Proof. split; apply domb_helper. Qed.

Lemma rewrite_dom A (r: relation A) (a b : A -> Prop) (H: r ⊆ a ✕ b) :
  r ⊆ ⦗a⦘ ⨾ r ⨾ ⦗b⦘.
Proof.
  unfolder in *; ins.
  specialize (H x y H0).
  desf; eexists; splits; desf; eexists; splits; eauto.
Qed.

Lemma transp_doma A (r: relation A) (d : A -> Prop) : domb r d ->  doma r⁻¹ d. 
Proof. unfolder; unfold domb, doma; ins; eapply H, REL. Qed.

Lemma transp_domb A (r: relation A) (d : A -> Prop) : doma r d ->  domb r⁻¹ d. 
Proof. unfolder; unfold domb, doma; ins; eapply H, REL. Qed.

Lemma union_doma A (r r' : relation A) (S: A -> Prop) :
  doma r S /\ doma r' S <-> doma (r ∪ r') S.
Proof.
  split; ins; unfolder in *; unfold doma in *; try split; ins; desf;
  try (by eapply H; eauto);
  try (by eapply H0; eauto).
Qed.

Lemma union_domb A (r r' : relation A) (S: A -> Prop) :
  domb r S /\ domb r' S <-> domb (r ∪ r') S.
Proof.
  split; ins; unfolder in *; unfold domb in *; try split; ins; desf;
  try (by eapply H; eauto);
  try (by eapply H0; eauto).
Qed.

Lemma set_union_doma A (r: relation A) (S S' : A -> Prop) :
  doma r S \/ doma r S' -> doma r (S ∪₁ S').
Proof.
  ins; desf.
  - by apply doma_implies with (r:=r) (d:=S); try (by ins; red; auto).
  - by apply doma_implies with (r:=r) (d:=S'); try (by ins; red; auto).
Qed.

Lemma set_union_domb A (r: relation A) (S S' : A -> Prop) :
  domb r S \/ domb r S' -> domb r (S ∪₁ S').
Proof.
  ins; desf.
  - by apply domb_implies with (r:=r) (d:=S); try (by ins; red; auto).
  - by apply domb_implies with (r:=r) (d:=S'); try (by ins; red; auto).
Qed.

Lemma inter_doma A (r r' : relation A) (S: A -> Prop) :
  doma r S \/ doma r' S -> doma (r ∩ r') S.
Proof.
  unfolder; ins; desf; unfold doma in *; ins; desf; eapply H; eauto.
Qed.

Lemma inter_domb A (r r' : relation A) (S: A -> Prop) :
  domb r S \/ domb r' S -> domb (r ∩ r') S.
Proof.
  unfolder; ins; desf; unfold domb in *; ins; desf; eapply H; eauto.
Qed.

Lemma seq_doma A (r r' : relation A) (S: A -> Prop) :
  doma r S -> doma (r ⨾ r') S.
Proof.
  ins; apply doma_helper.
  arewrite (r ⊆ ⦗S⦘ ⨾ r) at 1.
    by apply rewrite_doma.
  done.
Qed.

Lemma seq_domb A (r r' : relation A) (S: A -> Prop) :
  domb r' S -> domb (r ⨾ r') S.
Proof.
  ins; apply domb_helper.
  arewrite (r' ⊆ r' ⨾ ⦗S⦘) at 1.
    by apply rewrite_domb.
  done.
Qed.

Lemma restr_doma A B (r: relation A) (f: A -> B) (S: A -> Prop) :
  doma r S -> doma (restr_eq_rel f r) S.
Proof.
  unfolder; unfold doma.
  ins; desf; eapply H; eauto.
Qed.

Lemma restr_domb A B (r: relation A) (f: A -> B) (S: A -> Prop) :
  domb r S -> domb (restr_eq_rel f r) S.
Proof.
  unfolder; unfold domb.
  ins; desf; eapply H; eauto.
Qed.

Lemma only_doma A (r: relation A) (S S' : A -> Prop) : 
  r ⊆ ⦗S⦘ ⨾ r ⨾ ⦗S'⦘ -> r ⊆ ⦗S⦘ ⨾ r.
Proof.
  ins; unfolder in *; desf. ins; desf. eexists; splits; eauto.
  specialize (H x y H0); desf.
Qed.

Lemma only_domb A (r: relation A) (S S' : A -> Prop) : 
  r ⊆ ⦗S⦘ ⨾ r ⨾ ⦗S'⦘ -> r ⊆ r ⨾ ⦗S'⦘.
Proof.
  ins; unfolder in *; desf. ins; desf. eexists; splits; eauto.
  specialize (H x y H0); desf.
Qed.

Lemma internal_doma (r : relation event) (S : event -> Prop) : 
  r ⊆ ⦗S⦘ ⨾ r -> r∙ ⊆ ⦗S⦘ ⨾ r∙.
Proof. by ins; rewrite H at 1; unfolder; ins; desf; eexists; splits. Qed.

Lemma internal_domb (r : relation event) (S : event -> Prop) : 
  r ⊆ r ⨾ ⦗S⦘ -> r∙ ⊆ r∙ ⨾ ⦗S⦘.
Proof. by ins; rewrite H at 1; unfolder; ins; desf; eexists; splits. Qed.

Lemma external_doma (r : relation event) (S : event -> Prop) : 
  r ⊆ ⦗S⦘ ⨾ r -> r∘ ⊆ ⦗S⦘ ⨾ r∘.
Proof. by ins; rewrite H at 1; unfolder; ins; desf; eexists; splits. Qed.

Lemma external_domb (r : relation event) (S : event -> Prop) : 
  r ⊆ r ⨾ ⦗S⦘ -> r∘ ⊆ r∘ ⨾ ⦗S⦘.
Proof. by ins; rewrite H at 1; unfolder; ins; desf; eexists; splits. Qed.

Hint Resolve minus_doma minus_domb transp_doma transp_domb seq_doma seq_domb 
  only_doma only_domb internal_doma internal_domb external_doma external_domb
  restr_doma restr_domb trivial_doma trivial_domb eqv_doma eqv_domb inter_doma inter_domb
  set_union_doma set_union_domb
: domains.

Hint Rewrite rewrite_doma rewrite_domb rewrite_dom union_doma union_domb 
  doma_helper domb_helper domab_helper
: domains.

Ltac unfold_wf :=
  match goal with [WF:Wf |- _] => cdes WF;
    match goal with [D:WfDEPS,A:WfACTS,S:WfSB,RF:WfRF,M:WfMO,RM:WfRMW |- _] => 
      cdes D; cdes A; cdes S; cdes RF; cdes M; cdes RM; clear D A S RF M RM
    end
  end.

Ltac rewrite_cartesian_products :=
  repeat match goal with [DOM:_ ⊆ _ ✕ _ |- _] => apply rewrite_dom in DOM end.

Ltac simplify_domains :=
  try match goal with 
  (* Union *)
  | [ |- doma (_ ∪ _) _] => apply union_doma; splits
  | [ |- domb (_ ∪ _) _] => apply union_domb; splits
  (* Inter *)
  | [ |- doma (_ ∩ _) _] => apply inter_doma
  | [ |- domb (_ ∩ _) _] => apply inter_domb
  (* Transp *)
  | [ |- doma _⁻¹ _] => apply transp_doma
  | [ |- domb _⁻¹ _] => apply transp_domb
  (* Minus *)
  | [ |- doma (_ \ _) _] => apply minus_doma
  | [ |- domb (_ \ _) _] => apply minus_domb
  (* Restr *)
  | [ |- doma (restr_eq_rel _ _) _] => apply restr_doma
  | [ |- domb (restr_eq_rel _ _) _] => apply restr_domb
  (* Seq *)
  | [ |- doma (_ ⨾ _) _] => apply seq_doma
  | [ |- domb (_ ⨾ _) _] => apply seq_domb
  end.
  
Ltac domain_solver :=
  idtac + autounfold with composite_type_unfold;
  try (unfold_wf; rewrite_cartesian_products);
  idtac + unfold set_union;
  idtac + simplify_domains + (do 2 simplify_domains) + (do 3 simplify_domains);
  idtac + rewrite seqA + rewrite <- seqA;
  let apply_dom := (fun d => autorewrite with domains using apply d) in
  match goal with
  | |- _ \/ _ => left + right; domain_solver
  (* trivial *)
  | [ |- domb (_ ⨾ ⦗?b⦘) ?b] => apply trivial_domb
  | [ |- domb (⦗?a⦘ ⨾ _) ?a] => apply trivial_doma
  | [ |- doma ⦗?a⦘ ?a] => apply eqv_doma
  | [ |- domb ⦗?b⦘ ?b] => apply eqv_domb
  (* doma *)
  | |- ?r⁺ ⊆ ⦗_⦘ ⨾ ?r⁺ => apply doma_helper, ct_doma; domain_solver
  | [DOM:?r ⊆ ⦗?a⦘ ⨾ ?r ⨾ _ |- doma ?r ?a] => apply_dom (only_doma DOM)
  | [DOM:?r ⊆ ⦗?a⦘ ⨾ ?r ⨾ _ |- ?r ⊆ ⦗?a⦘ ⨾ ?r] => apply (only_doma DOM)
  | [DOM:?r ⊆ ⦗?a⦘ ⨾ ?r |- doma ?r ?a] => apply_dom (only_doma DOM)
  | [DOM:doma ?r ?a |- ?r ⊆ ⦗?a⦘ ⨾ ?r] => by apply doma_helper
  (* domb *)
  | |- ?r⁺ ⊆ ?r⁺ ⨾ ⦗_⦘ => apply domb_helper, ct_domb; domain_solver
  | [DOM:?r ⊆ _ ⨾ ?r ⨾ ⦗?b⦘ |- domb ?r ?b] => apply_dom (only_domb DOM)
  | [DOM:?r ⊆ _ ⨾ ?r ⨾ ⦗?b⦘ |- ?r ⊆ ?r ⨾ ?b] => apply (only_domb DOM)
  | [DOM:?r ⊆ ?r ⨾ ⦗?b⦘ |- domb ?r ?b] => apply_dom (only_domb DOM)
  | [DOM:domb ?r ?a |- ?r ⊆ ?r ⨾ ⦗?a⦘] => by apply domb_helper
  (* left_union *)
  | |- (?r ∪ ?r') ⊆ ⦗?A⦘ ⨾ (?r ∪ ?r') => 
    (arewrite (r ⊆ ⦗A⦘ ⨾ r) at 1 by domain_solver);
    (arewrite (r' ⊆ ⦗A⦘ ⨾ r') at 1 by domain_solver);
    by rewrite !seq_union_r
  (* dom -> incl *)
  | |- ?r ⊆ ⦗_⦘ ⨾ ?r => apply doma_helper; domain_solver
  | |- ?r ⊆ ?r ⨾ ⦗_⦘  => apply domb_helper; domain_solver
  | |- ?r ⊆ ⦗_⦘ ⨾ ?r ⨾ ⦗_⦘  => apply domab_helper; split; domain_solver
  (* db *)
  | |- doma _ _ => by eauto with domains
  | |- domb _ _ => by eauto with domains
  (* set_union *)
  | |- ?r ⊆ ⦗?A ∪₁ ?B⦘ ⨾?r => 
    apply doma_helper, set_union_doma; (left + right); domain_solver
  | |- ?r ⊆ ?r ⨾ ⦗?A ∪₁ ?B⦘ => 
    apply domb_helper, set_union_domb; (left + right); domain_solver
  end.


(*============================================================================*)

Hypothesis WF: Wf.

Lemma rf_doma : doma rf W.
Proof. domain_solver. Qed.

Lemma rf_domb : domb rf R.
Proof. domain_solver. Qed.

Lemma mo_doma : doma mo W.
Proof. domain_solver. Qed.

Lemma mo_domb : domb mo W.
Proof. domain_solver. Qed.

Lemma rmw_doma : doma rmw R.
Proof. domain_solver. Qed.

Lemma rmw_domb : domb rmw W.
Proof. domain_solver. Qed.

Lemma data_doma : doma data R.
Proof. domain_solver. Qed.

Lemma data_domb : domb data W.
Proof. domain_solver. Qed.

Lemma ctrl_doma : doma ctrl R.
Proof. by unfold_wf; apply doma_helper. Qed.

Lemma ctrli_doma : doma ctrl_isync R.
Proof. by unfold_wf; apply doma_helper. Qed.

Lemma addr_doma : doma addr R.
Proof. domain_solver. Qed.

Lemma addr_domb : domb addr RW.
Proof. domain_solver. Qed.

Lemma deps_doma : doma deps R.
Proof. unfold Power_Model.deps; auto using data_doma, addr_doma, ctrl_doma with rel. Qed.

Lemma rb_doma : doma rb R.
Proof. unfold Power_Model.rb; domain_solver. Qed.

Lemma rb_domb : domb rb W.
Proof. unfold Power_Model.rb; domain_solver. Qed.

Lemma rdw_doma : doma rdw R.
Proof. 
  unfold Power_Model.rdw; repeat (simplify_domains; try left).
  unfold Power_Model.rb; domain_solver.
Qed.

Lemma rdw_domb : domb rdw R.
Proof.
  unfold Power_Model.rdw; repeat (simplify_domains; try left); domain_solver.
Qed.

Hint Resolve rf_doma rf_domb mo_doma mo_domb rmw_doma rmw_domb data_doma 
  data_domb ctrl_doma ctrli_doma addr_doma deps_doma rb_doma rb_domb rdw_doma 
  rdw_domb
: domains.

Lemma rel_doma (r: relation event) : doma r (R ∪₁ W ∪₁ F).
Proof.
  red; ins.
  repeat autounfold with type_unfold; unfold set_union.
  unfold is_r, is_w, is_f_sync, is_f_lwsync.
  destruct (lab x); auto.
Qed.

Lemma rel_domb (r: relation event) : domb r (R ∪₁ W ∪₁ F).
Proof.
  red; ins.
  repeat autounfold with type_unfold; unfold set_union.
  unfold is_r, is_w, is_f_sync, is_f_lwsync.
  destruct (lab y); auto.
Qed.

Hint Resolve rel_doma rel_domb : domains.

Lemma loc_not_f a : loc lab a <> None -> ~ F a.
Proof.
  repeat autounfold with type_unfold; unfold set_union.
  ins; unfold is_f_sync, is_f_lwsync.
  apply and_not_or; split; unfold loc in H; destruct (lab a); desf.
Qed.

Lemma same_loc_doma : doma same_loc (R ∪₁ W).
Proof.
  apply doma_helper.
  arewrite (same_loc ⊆ ⦗R ∪₁ W ∪₁ F⦘ ⨾ same_loc) at 1 by domain_solver.
  unfold Power_Model.same_loc.
  repeat autounfold with type_unfold; unfold set_union; unfolder; ins; desf;
  repeat (eexists; splits; eauto); apply loc_not_f in H0;
  repeat autounfold with type_unfold in H0; unfold set_union in H0; desf;
  apply not_or_and in H0; desf.
Qed.

Lemma same_loc_domb : domb same_loc (R ∪₁ W).
Proof.
  apply domb_helper.
  arewrite (same_loc ⊆ same_loc ⨾ ⦗R ∪₁ W ∪₁ F⦘) at 1 by domain_solver.
  unfold Power_Model.same_loc.
  repeat autounfold with type_unfold; unfolder; ins; desf;
  splits; auto; rewrite H1 in H; apply loc_not_f in H;
  repeat autounfold with type_unfold in *; unfolder in *; intuition.
Qed.

Lemma sblocR_doma : doma (sb|loc ⨾ ⦗R⦘) (R ∪₁ W).
Proof. apply seq_doma, inter_doma; right; apply same_loc_doma. Qed.

Lemma psbloc_doma : doma psbloc (R ∪₁ W).
Proof.
  unfold Power_Model.psbloc; simplify_domains.
  clear_equivs ⦗I⦘.
  by apply sblocR_doma.
Qed.

Lemma psbloc_domb : domb psbloc R.
Proof. unfold Power_Model.psbloc; domain_solver. Qed.

Lemma addrsb_doma : doma (addr ⨾ sb) R.
Proof. domain_solver. Qed.

Lemma depsUaddrsb_doma : doma (deps ∪ addr ⨾ sb) R.
Proof. domain_solver. Qed.

Lemma detour_doma : doma detour W.
Proof.
  apply doma_helper.
  unfold Power_Model.detour.
  arewrite (mo∘ ⊆ ⦗W⦘ ⨾ mo∘) at 1.
    by apply external_doma, doma_helper, mo_doma.
  unfolder in *; ins; desf; eexists; splits; eauto.
Qed.

Lemma detour_domb : domb detour R.
Proof.
  apply domb_helper.
  unfold Power_Model.detour.
  arewrite (mo∘ ⊆ mo∘ ⨾ ⦗W⦘) at 1.
    by apply external_domb, domb_helper, mo_domb.
  unfolder in *; ins; desf; eexists; splits; eauto.
  eapply rf_domb; eauto.
Qed.

Lemma ppo_doma : doma ppo R.
Proof. unfold Power_Model.ppo. domain_solver. Qed.

Lemma ppo_domb : domb ppo RW.
Proof. unfold Power_Model.ppo, Power_Model.RW; basic_solver. Qed.

Lemma fence_domb : domb fence RW.
Proof.
  unfold Power_Model.fence.
  apply domb_helper.
  arewrite (sync ⊆ sync ⨾ ⦗RW⦘) by unfold Power_Model.sync; domain_solver.
  arewrite (lwsync ⊆ lwsync ⨾ ⦗RW⦘) by unfold Power_Model.lwsync; domain_solver.
  basic_solver 10.
Qed.

Hint Resolve sblocR_doma psbloc_doma psbloc_domb addrsb_doma depsUaddrsb_doma 
  detour_doma detour_domb ppo_doma ppo_domb fence_domb
: domains.

Lemma R_in_I : R ⊆₁ I.
Proof.
  repeat red; ins; unfold Power_Model.R, is_r, is_init in *; desf.
  cdes WF; cdes WF_ACTS; rewrite LAB_INIT in Heq.
  unfold init_label in Heq; desf.
Qed.

Lemma F_in_I : F ⊆₁ I.
Proof.
  red; ins; repeat autounfold with type_unfold in *.
  red; ins; unfold set_union, is_f_sync, is_f_lwsync, is_init in *; desf;
  cdes WF; cdes WF_ACTS; rewrite LAB_INIT in *; unfold init_label in *; desf.
Qed.

Lemma hb_domb : domb hb RW.
Proof.
  unfold Power_Model.hb.
  do 2 simplify_domains.
  - domain_solver.
  - domain_solver.
  - autounfold with composite_type_unfold; domain_solver.
Qed.

Lemma fence_doma : doma fence RW.
Proof.
  unfold Power_Model.fence.
  apply doma_helper.
  arewrite (sync ⊆ ⦗RW⦘ ⨾ sync) by unfold Power_Model.sync; domain_solver.
  arewrite (lwsync ⊆ ⦗RW⦘ ⨾ lwsync) by unfold Power_Model.lwsync; domain_solver.
  basic_solver 10.
Qed.

Hint Resolve hb_domb fence_doma : domains.

Lemma rfe_hb_domb : domb (rf∘ ⨾ hb＊) RW.
Proof.
  apply domb_helper.
  rewrite rtE; relsf; unionL.
  - unionR left; domain_solver.
  - unionR right; arewrite (hb⁺ ⊆ hb⁺ ⨾ ⦗RW⦘) at 1 by domain_solver.
Qed.

Lemma eco_doma : doma eco RW.
Proof. unfold Power_Model.eco; domain_solver. Qed.

Lemma eco_domb : domb eco RW.
Proof.
  unfold Power_Model.eco.
  rewrite crE; relsf.
  domain_solver.
Qed.

End Power_Domains.

Hint Resolve rf_doma rf_domb mo_doma mo_domb rmw_doma rmw_domb data_doma 
  data_domb ctrl_doma ctrli_doma addr_doma deps_doma rb_doma rb_domb rdw_doma 
  rdw_domb minus_doma minus_domb transp_doma transp_domb seq_doma seq_domb 
  only_doma only_domb external_doma external_domb restr_doma restr_domb 
  trivial_doma trivial_domb eqv_doma eqv_domb inter_doma inter_domb
  set_union_doma set_union_domb sblocR_doma psbloc_doma psbloc_domb addrsb_doma 
  depsUaddrsb_doma detour_doma detour_domb ppo_doma hb_domb fence_doma 
  rfe_hb_domb rel_doma rel_domb same_loc_doma same_loc_domb eco_doma eco_domb
: domains.

Hint Rewrite rewrite_doma rewrite_domb rewrite_dom union_doma union_domb 
  doma_helper domb_helper domab_helper
: domains.
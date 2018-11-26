(******************************************************************************)
(** * Definition of the Power memory model *)
(******************************************************************************)
Require Import Hahn.
Require Import Basic Power_Events.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Power_Model.

Record power_execution := 
  { acts        : list event ;
    lab         : event -> label ;
    (* Basic relations *)
    sb          : relation event ;
    rf          : relation event ;
    mo          : relation event ;
    rmw         : relation event ;
    (* Dependecies *)
    data        : relation event ;
    addr        : relation event ;
    ctrl        : relation event ;
    ctrl_isync  : relation event ;
  }.

Variable G : power_execution.

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

Definition E a := In a acts.
Definition R := (is_r lab).
Definition W := (is_w lab).
Definition F_sync := (is_f_sync lab).
Definition F_lwsync := (is_f_lwsync lab).
Definition RW := (R ∪₁ W).
Definition _WF := (W ∪₁ F_sync ∪₁ F_lwsync).
Definition F := (F_sync ∪₁ F_lwsync).

Definition same_loc := (fun x y => loc lab x <> None /\ loc lab x = loc lab y).

Notation "rel |loc" := (rel ∩ same_loc) (at level 1).
Notation "a ∙" := (a ∩ same_thread) (at level 1, format "a ∙").
Notation "a ∘" := (a \ same_thread) (at level 1, format "a ∘").
Definition restrict_location s l := fun a => s a /\ loc lab a = l.

Definition deps := data ∪ addr ∪ ctrl.

Definition rb := rf⁻¹ ⨾ mo.

Definition rdw := (rb∘ ⨾ rf∘)∙.

Definition detour := (mo∘ ⨾ rf∘)∙.

(******************************************************************************)
(** ** PPO components *)
(******************************************************************************)

(* Basic definition *)
Definition ii0 : relation event := addr ∪ data ∪ rdw ∪ rf∙.
Definition ci0 : relation event := ctrl_isync⨾ ⦗RW⦘ ∪ detour.
Definition cc0 : relation event := data ∪ ctrl ⨾ ⦗RW⦘ ∪ addr ⨾ sb^? ⨾ ⦗RW⦘.

Inductive ii x y : Prop :=
      II0   : ii0 x y -> ii x y
    | CI    : ci x y -> ii x y
    | IC_CI : forall z, ic x z -> ci z y -> ii x y
    | II_II : forall z, ii x z -> ii z y -> ii x y
with ic x y : Prop := 
    | II    : ii x y -> ic x y
    | CC    : cc x y -> ic x y
    | IC_CC : forall z, ic x z -> cc z y -> ic x y
    | II_IC : forall z, ii x z -> ic z y -> ic x y
with ci x y : Prop := 
      CI0   : ci0 x y -> ci x y
    | CI_II : forall z, ci x z -> ii z y -> ci x y
    | CC_CI : forall z, cc x z -> ci z y -> ci x y
with cc x y : Prop := 
      CC0   : cc0 x y -> cc x y
    | CI_   : ci x y -> cc x y
    | CI_IC : forall z, ci x z -> ic z y -> cc x y
    | CC_CC : forall z, cc x z -> cc z y -> cc x y.

Scheme ii_rec := Minimality for ii Sort Prop
  with ic_rec := Minimality for ic Sort Prop
  with ci_rec := Minimality for ci Sort Prop
  with cc_rec := Minimality for cc Sort Prop.

Combined Scheme ppo_comp_ind from ii_rec, ic_rec, ci_rec, cc_rec.

(* Relational definition *) 
Lemma ii_alt : ii ≡ ii0 ∪ ci ∪ ic⨾ci ∪ ii⨾ii.
Proof.
  unfold seq, union; split; red; ins; desf; eauto using ii.
  destruct H; eauto 8.
Qed.
Lemma ic_alt : ic ≡ ii ∪ cc ∪ ic⨾cc ∪ ii⨾ic.
Proof.
  unfold seq, union; split; red; ins; desf; eauto using ic.
  destruct H; eauto 8.
Qed.
Lemma ci_alt : ci ≡ ci0 ∪ ci⨾ii ∪ cc⨾ci.
Proof.
  unfold seq, union; split; red; ins; desf; eauto using ci.
  destruct H; eauto 8.
Qed.
Lemma cc_alt : cc ≡ cc0 ∪ ci ∪ ci⨾ic ∪ cc⨾cc.
Proof.
  unfold seq, union; split; red; ins; desf; eauto using cc.
  destruct H; eauto 8.
Qed.

(* Single-transition definition *)
Inductive L x y : Prop :=
  | L_cc      : cc0 x y -> L x y
  | L_Li      : Li x y -> L x y
  | L_L_cc    : forall z, L x z -> cc0 z y -> L x y
with Li x y : Prop :=
  | Li_ci     : ci0 x y -> Li x y
  | Li_ii     : ii0 x y -> Li x y
  | Li_L_ci   : forall z, L x z -> ci0 z y -> Li x y
  | Li_Li_ii  : forall z, Li x z -> ii0 z y -> Li x y.

Scheme L_rec := Minimality for L Sort Prop
  with Li_rec := Minimality for Li Sort Prop.

Combined Scheme L_comb from L_rec, Li_rec.

(* Preserved program order *)
Definition ppo := ⦗R⦘ ⨾ ii ⨾ ⦗R⦘ ∪ ⦗R⦘ ⨾ ic ⨾ ⦗W⦘.

(* Fence order *)
Definition sync := ⦗RW⦘ ⨾ sb ⨾ ⦗F_sync⦘ ⨾ sb ⨾ ⦗RW⦘.
Definition lwsync := (⦗RW⦘ ⨾ sb ⨾ ⦗F_lwsync⦘ ⨾ sb ⨾ ⦗RW⦘) \ (W ✕ R).
Definition fence := sync ∪ lwsync.

(* Power happens-before *)
Definition hb := ppo ∪ fence ∪ rf∘.

(* Propagation order *)
Definition prop1 := ⦗W⦘ ⨾ rf∘^? ⨾ fence ⨾ hb＊ ⨾ ⦗W⦘.
Definition prop2 := (mo∘ ∪ rb∘)^? ⨾ rf∘^? ⨾ (fence ⨾ hb＊)^? ⨾ sync ⨾ hb＊.
Definition prop := prop1 ∪ prop2.

(* Preserved sb-loc *)
Definition psbloc := ⦗I⦘ ⨾ sb|loc ⨾ ⦗R⦘ \ sb|loc ⨾ ⦗W⦘ ⨾ sb.

(* Extended coherence order *)
Definition eco := rf ∪ mo ⨾ rf^? ∪ rb ⨾ rf^?.

(******************************************************************************)
(** ** Well-formed relations *)
(******************************************************************************)
Definition WfACTS := 
  ⟪ ACTS_INIT : forall l, In (Init l) acts ⟫ /\
  ⟪ LAB_INIT  : forall l, lab (Init l) = init_label l ⟫.

Definition WfSB := 
  ⟪ SB_ACT    : sb ⊆ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘ ⟫ /\
  ⟪ SB_INIT   : init_pair ⨾ ⦗E⦘ ⊆ sb ⟫ /\
  ⟪ SB_IRR    : irreflexive sb ⟫ /\
  ⟪ SB_T      : transitive sb ⟫ /\
  ⟪ SB_TID    : sb ⊆ sb∙ ∪ init_pair ⟫ /\
  ⟪ SB_TOT    : forall i, is_total (E ∩₁ (fun a => tid a = Some i)) sb ⟫.

Definition WfRF := 
  ⟪ RF_ACT  : rf ⊆ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘ ⟫ /\
  ⟪ RF_DOM  : rf ⊆ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘ ⟫ /\
  ⟪ RF_LOC  : funeq (loc lab) rf ⟫ /\
  ⟪ RF_VAL  : funeq (val lab) rf ⟫ /\
  ⟪ RF_FUN  : functional rf⁻¹ ⟫ /\ 
  ⟪ RF_TOT  : forall b (IN: In b acts) (READ: R b), exists a, rf a b ⟫.

Definition WfMO :=
  ⟪ MO_ACT  : mo ⊆ ⦗E⦘ ⨾ mo ⨾ ⦗E⦘ ⟫ /\
  ⟪ MO_DOM  : mo ⊆ ⦗W⦘ ⨾ mo ⨾ ⦗W⦘ ⟫ /\
  ⟪ MO_LOC  : funeq (loc lab) mo ⟫ /\
  ⟪ MO_IRR  : irreflexive mo ⟫ /\
  ⟪ MO_T    : transitive mo ⟫ /\
  ⟪ MO_TOT  : forall l, is_total (fun a => E a /\ W a /\ (loc lab a = Some l)) mo ⟫.

Definition WfRMW := 
  ⟪ RMW_DOM       : rmw ⊆ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘ ⟫ /\
  ⟪ RMW_LOC       : funeq (loc lab) rmw ⟫ /\
  ⟪ RMW_IMM : rmw ⊆ sb|imm ⟫.

Definition WfDEPS :=
  ⟪ DATA        : data ⊆ ⦗R⦘ ;; data ;; ⦗W⦘⟫ /\
  ⟪ ADDR        : addr ⊆ ⦗R⦘ ;; addr ;; ⦗R ∪₁ W⦘⟫ /\
  ⟪ CTRL_CTLRI  : ctrl_isync ⊆ ctrl⟫ /\
  ⟪ CTRL_RE     : ctrl ⊆ ⦗R⦘ ;; ctrl⟫ /\
  ⟪ CTRLI_RE    : ctrl_isync ⊆ ⦗R⦘ ;; ctrl_isync⟫ /\
  ⟪ CTRL_SB     : ctrl ⨾ sb ⊆ ctrl⟫ /\
  ⟪ CTRLI_SB    : ctrl_isync ⨾ sb ⊆ ctrl_isync⟫ /\
  ⟪ RMW_DEPS    : rmw ⊆ data ∪ addr ∪ ctrl⟫ /\
  ⟪ RMW_SB      : rmw ⨾ sb ⊆ ctrl⟫ /\
  ⟪ DATA_IN_SB  : data ⊆ sb ⟫ /\
  ⟪ ADDR_IN_SB  : addr ⊆ sb ⟫ /\
  ⟪ CTRL_IN_SB  : ctrl ⊆ sb ⟫ /\
  ⟪ CTRLI_IN_SB : ctrl_isync ⊆ sb ⟫.

Definition Wf :=
  ⟪ WF_DEPS : WfDEPS ⟫ /\
  ⟪ WF_ACTS : WfACTS ⟫ /\
  ⟪ WF_SB   : WfSB ⟫ /\
  ⟪ WF_RF   : WfRF ⟫ /\
  ⟪ WF_MO   : WfMO ⟫ /\
  ⟪ WF_RMW  : WfRMW ⟫.

(* Consistency *)
Definition PowerConsistent :=
  ⟪ WF : Wf ⟫ /\
  ⟪ SC_PER_LOC: acyclic (sb|loc ∪ rf ∪ rb ∪ mo) ⟫ /\
  ⟪ OBSERVATION : irreflexive (rb∘ ⨾ prop ⨾ hb＊) ⟫ /\
  ⟪ PROPAGATION : acyclic (mo ∪ prop) ⟫ /\
  ⟪ POWER_ATOMICITY : rmw ∩ (rb∘ ⨾ mo∘) ⊆ ∅₂ ⟫ /\
  ⟪ POWER_NO_THIN_AIR: acyclic hb ⟫.

(******************************************************************************)
(** ** Outcomes  *)
(******************************************************************************)
Definition outcome (O: location -> value) :=
  forall l, exists w,
    W w /\
    loc lab w = Some l /\
    val lab w = Some (O l) /\
    max_elt mo w.

(******************************************************************************)
(** ** Helpers *)
(******************************************************************************)

Lemma in_acts (WF: Wf) a b
  (REL: (sb ∪ rf ∪ mo ∪ rb ∪ rmw ∪ data ∪ addr ∪ ctrl ∪ ctrl_isync) a b) :
  In a acts /\ In b acts.
Proof.
  cdes WF; cdes WF_SB; cdes WF_RF; cdes WF_MO; cdes WF_RMW; cdes WF_DEPS.
  unfolder in *; desf;
  (* deps -> sb*) try (assert (REL': sb a b) by by basic_solver);
  (* rmw -> sb*) try (assert (REL': sb a b) by (by apply RMW_IMM));
  (*deps*) try specialize (SB_ACT _ _ REL');
  (*sb*) try specialize (SB_ACT _ _ REL);
  (*rf*) try specialize (RF_ACT _ _ REL);
  (*mo*) try specialize (MO_ACT _ _ REL);
  unfolder in *; desf.
  (*rb*)red in REL; unfolder in *; desc; split;
    (*rf⁻¹*) try specialize (RF_ACT _ _ REL);
    (*mo*) try specialize (MO_ACT _ _ REL0);
    unfolder in *; desf.
Qed.

Lemma con_implies_wf : PowerConsistent -> Wf.
Proof. by ins; cdes H. Qed.

End Power_Model.

(* Export Hints *)
Hint Unfold is_r is_w is_f_sync is_f_lwsync : basic_type_unfold.
Hint Unfold set_union E R W F_sync F_lwsync RW _WF I F : type_unfold.
Hint Unfold RW _WF F : composite_type_unfold.
Hint Resolve con_implies_wf : rel rel_full.
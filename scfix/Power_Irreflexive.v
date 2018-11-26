(******************************************************************************)
(** * Irreflexive relations of the Power memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Power_Events Power_Model Power_Domains Power_Locations
  Power_Automation.

Set Implicit Arguments.

Section Power_Irreflexive.

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

Hypothesis WF: Wf.

Lemma sb_irr : irreflexive sb.
Proof. by unfold_wf. Qed.

Lemma mo_irr : irreflexive mo.
Proof. by unfold_wf. Qed.

Lemma rf_irr : irreflexive rf.
Proof.
  arewrite (rf ⊆ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘) by domain_solver.
  solve_irreflexive0.
Qed.

Lemma rb_irr : irreflexive rb.
Proof.
  arewrite (rb ⊆ ⦗R⦘ ⨾ rb ⨾ ⦗W⦘) by domain_solver.
  solve_irreflexive0.
Qed.

Lemma psbloc_irr : irreflexive psbloc.
Proof.
  apply irreflexive_inclusion with (r':=sb).
    by unfold Power_Model.psbloc; unfolder; ins; desf.
    by unfold_wf.
Qed.

End Power_Irreflexive.

(* Export Hints *)
Lemma false_to_irr A (r : relation A) a:
  irreflexive r -> (r a a -> False).
Proof. ins; eapply H; eauto. Qed.

Hint Resolve false_to_irr sb_irr mo_irr rf_irr rb_irr psbloc_irr : irreflexiveDb.
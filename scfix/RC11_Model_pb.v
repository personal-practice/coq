(******************************************************************************)
(** * Definitions of the axiomatic memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec.
Require Import Hahn.

Require Import Basic Dom RC11_Events RC11_Model RC11_Threads.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section PB.

Variable G : execution.

Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rmw'" := G.(rmw).
Notation "'rf'" := G.(rf).
Notation "'mo'" := G.(mo).
Notation "'eco'" := G.(eco).
Notation "'rb'" := G.(rb).
Notation "'sw'" := G.(sw).
Notation "'hb'" := G.(hb).
Notation "'psc_f'" := G.(psc_f).
Notation "'psc'" := G.(psc).
Notation "'sb_neq_loc'" := G.(sb_neq_loc).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).
Notation "'deps'" := G.(deps).
Notation "'same_loc'" := G.(same_loc).
Notation "rel |loc" := (rel ∩ same_loc) (at level 1).

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

Notation "type ~ mode" := (type ∩₁ mode) (at level 1).

Definition psbloc :=  ⦗fun a => ~ is_init a⦘ ⨾ (restr_eq_rel (loc lab) sb) ⨾ ⦗R⦘ \ 
                                       (restr_eq_rel (loc lab) sb) ⨾ ⦗W⦘ ⨾ sb.
Definition pbi := deps ∪ addr ;; sb ∪ ⦗R~Rlx ∪₁ W~Rel ∪₁ F⦘ ;; sb ∪ psbloc ∪ sb ;; ⦗FW~Rel⦘.
Definition pb := pbi ∪ rf∘.

Hypothesis WF: G.(Wf).

Lemma rfi_psbloc (COH:  irreflexive (hb ⨾ eco^?)): 
  rf∙ ⊆ pb.
Proof.
  cdes WF.
  unionR left -> left -> right.
  unfold psbloc; unfolder; splits; ins; desf.
  eby eapply st_not_inita.
  eby apply rf_st_implies_sb.
  eby apply WF_RF.
  eby eapply rf_domb.
  intro; desf; eapply COH.
  exists y; splits.
  eby eapply sb_in_hb.
  right; apply rb_in_eco; try done.
  red; unfolder; splits.
  - exists x; splits; [basic_solver|].
    apply sb_loc_in_mo; try edone.
    unfolder; eexists; splits; eauto.
    eby eapply rf_doma; eauto.
    red; splits; auto.
    rewrite H4.
    unfold loc; solve_type_mismatch.
  - apply or_not_and. left. intro; desf.
    by cdes WF_SB; apply SB_IRR in H3.
Qed.

(* Proposition G.1 *)
Proposition rf_pb (COH:  irreflexive (hb ⨾ eco^?)): 
  rf ⊆ pb.
Proof.
arewrite (rf ⊆ rf∘ ∪ rf∙).
  by unfolder; ins; destruct (classic (same_thread x y)); tauto.
by unionL; [vauto|rewrite rfi_psbloc].
Qed.

Proposition rmw_pbi: rmw ⊆ pbi.
Proof.
cdes WF; cdes WF_DEPS.
cdes WF_RMW.
rewrite RMW_DEPS.
unfold pbi, RC11_Model.deps.
basic_solver 10.
Qed.

(* Proposition G.2 *)
Proposition hb_pb (COH:  irreflexive (hb ⨾ eco^?)): 
  hb ⊆ sb ∪ pb^+.
Proof.
unfold RC11_Model.hb.
rewrite path_union.
assert (T: transitive sb) by by cdes WF; cdes WF_SB.
relsf.
unionL; auto with rel.
unionR right.
unfold RC11_Model.sw, RC11_Model.release, RC11_Model.rs, RC11_Model.useq.
arewrite ((sb|loc)^? ⊆ sb^?).
arewrite (⦗fun a : event => In a acts⦘ ⨾ ⦗W⦘ ⨾ sb^? ⨾ ⦗W~Rlx⦘⊆ sb^?) by basic_solver 10.
arewrite ((⦗W~Rel⦘ ∪ ⦗F~Rel⦘ ⨾ sb) ⨾ sb^? ⊆ (⦗W~Rel⦘ ∪ ⦗F~Rel⦘) ⨾ sb^?)
  by relsf; unionL; rewrite ?seqA; relsf.
arewrite (⦗R~Acq⦘ ∪ ⦗R~Rlx⦘ ⨾ sb ⨾ ⦗F~Acq⦘ ⊆ ⦗R~Rlx⦘ ⨾ sb^?)
  by unionL; solve_mode_mismatch.
arewrite (sb^? ⨾ sb^? ⊆ sb^?) by relsf.
arewrite (⦗R~Rlx⦘ ⨾ sb^? ⊆ pbi^?)
  by unfold pbi; basic_solver 10.
rewrite rmw_pbi.
arewrite (rf ⊆ pb) by apply rf_pb.
arewrite ((⦗W~Rel⦘ ∪ ⦗F~Rel⦘)  ⊆ ⦗FW~Rel⦘  ;; (⦗W~Rel⦘ ∪ ⦗F~Rel⦘))
  by rewrite <- !id_union; solve_type_mismatch.
arewrite ( sb^? ⨾ ⦗FW~Rel⦘ ⊆ pbi^*)
  by unfold pbi; rewrite crE; relsf; eauto 5 with rel.
arewrite (⦗F~Rel⦘ ⊆ ⦗F⦘) by solve_type_mismatch.
arewrite ((⦗W~Rel⦘ ∪ ⦗F⦘) ⨾ sb^? ⊆⦗R~Rlx ∪₁ W~Rel ∪₁ F⦘ ⨾ sb^?) by basic_solver 10.
arewrite (⦗R~Rlx ∪₁ W~Rel ∪₁ F⦘ ⨾ sb^? ⊆ pbi^*)
  by rewrite crE; relsf; unionL; unfold pbi; auto with rel.
arewrite (pbi ⊆ pb).
relsf; auto 8 with rel_full rel.
Qed.

End PB.
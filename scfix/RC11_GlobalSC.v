Require Import Classical List Relations Peano_dec.
Require Import Hahn.

Require Import Basic Dom RC11_Events RC11_Model RC11_PSC.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section GlobalSC.

Variable G : execution.

Notation "'acts'" := G.(acts).
Notation "'lab'" := G.(lab).
Notation "'sb'" := G.(sb).
Notation "'rmw'" := G.(rmw).
Notation "'rf'" := G.(rf).
Notation "'mo'" := G.(mo).
Notation "'eco'" := G.(eco).
Notation "'rb'" := G.(rb).
Notation "'hb'" := G.(hb).
Notation "'psc_f'" := G.(psc_f).
Notation "'psc'" := G.(psc).
Notation "'scb'" := G.(scb).
Notation "'sb_neq_loc'" := G.(sb_neq_loc).
Notation "'sb''" := (sb \ rmw).

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

Notation "type ~ mode" := (type ∩₁ mode) (at level 1).

Notation "'same_loc'" := G.(same_loc).
Notation "rel |loc" := (rel ∩ same_loc) (at level 1).

Implicit Type WF : Wf G.
Implicit Type NRMW : NO_RMW_EVENTS G.

Lemma global_sc_helper
  WF NRMW
  (HSC: ⦗RW~Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW~Sc⦘ ⊆ hb ⨾ ⦗F~Sc⦘ ⨾ hb) :
  ⦗F~Sc⦘ ⨾ hb ⨾ eco^? ⨾
    (⦗RW~Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb' ∪ eco) ⨾ ⦗RW~Sc⦘)^* ⨾
      eco^? ⨾ hb ⨾ ⦗F~Sc⦘ ⊆ psc_f⁺.
Proof.
assert (transitive eco).
  by apply eco_trans; assumption.
assert (transitive hb).
  by apply hb_trans; assumption.
eapply rt_ind_left with (P:= fun __ => ⦗F~Sc⦘ ⨾
  hb ⨾ eco ^? ⨾ __ ⨾ eco ^? ⨾ hb ⨾ ⦗F~Sc⦘).
- eauto with rel.
- relsf.
  arewrite (hb ⨾ eco ^? ⨾ hb ⊆ hb ∪ hb ⨾ eco ⨾ hb).
    by rewrite crE; relsf.
  apply inclusion_step_t, inclusion_refl2.
- intros k IH.
  arewrite (⦗RW~Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb' ∪ eco) ⨾ ⦗RW~Sc⦘ ⊆
                           ⦗RW~Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW~Sc⦘ ∪ eco) by basic_solver 42.
  rewrite HSC.
  arewrite (⦗F~Sc⦘ ⨾ hb ⨾ eco ^? ⨾ (hb ⨾ ⦗F~Sc⦘ ⨾ hb ∪ eco) ⊆ 
                           ⦗F~Sc⦘ ⨾ hb ⨾ eco ^? ⨾ hb ⨾ ⦗F~Sc⦘ ⨾ hb ⨾ eco^? ∪ ⦗F~Sc⦘ ⨾ hb ⨾ eco^?)
    by basic_solver 42.
  relsf.
  rewrite !seqA, IH.
  apply inclusion_union_l; try done.
  arewrite (psc_f⁺ ⊆ ⦗F~Sc⦘ ⨾ psc_f⁺).
    by apply doma_helper, ct_doma, doma_helper2.
  rewrite <- !seqA with (r3 := psc_f⁺).
  arewrite (⦗F~Sc⦘ ⨾ hb ⨾ eco ^? ⨾ hb ⨾ ⦗F~Sc⦘ ⊆ psc_f).
    unfold RC11_Model.psc_f; basic_solver 10.
  rewrite ct_begin at 2; basic_solver.
Qed.

Lemma RW_scb_RW :
  ⦗RW~Sc⦘ ⨾ scb ⨾ ⦗RW~Sc⦘ ⊆
    ⦗RW ~ Sc⦘ ⨾
    (sb ∪ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ∪ ⦗RW⦘ ⨾ hb |loc ⨾ ⦗RW⦘ ∪ mo ∪ rb)
      ⨾ ⦗RW ~ Sc⦘.
Proof.
  unfold RC11_Model.scb; basic_solver 42.
Qed.

Lemma global_sc
  WF NRMW
  (COH: irreflexive (hb ⨾ eco^?))
  (HSC: ⦗RW~Sc⦘ ⨾ (sb' ∪ sb' ⨾ hb ⨾ sb') ⨾ ⦗RW~Sc⦘ ⊆ hb ⨾ ⦗F~Sc⦘ ⨾ hb)
  (ACYC: acyclic psc_f) : acyclic psc.
Proof.
assert (transitive eco).
  by apply eco_trans; assumption.
assert (transitive hb).
  by apply hb_trans; assumption.
eapply acyc_dom with (d:= RW~Sc) (e:= F~Sc); try edone.
- unfold RC11_Model.psc, RC11_Model.psc_base, RC11_Model.psc_f; unionL.
  arewrite (⦗Sc⦘ ≡ ⦗RW~Sc⦘ ∪ ⦗F~Sc⦘) by solve_type_mismatch 42.
  basic_solver 42.
  basic_solver 42.
- solve_type_mismatch 6.
- unfold RC11_Model.psc, RC11_Model.psc_base, RC11_Model.psc_f; relsf; rewrite !seqA.
  arewrite_false !(⦗RW~Sc⦘ ⨾ ⦗F~Sc⦘).
    solve_type_mismatch 6.
  arewrite_false !( ⦗F~Sc⦘ ⨾ ⦗RW~Sc⦘).
    solve_type_mismatch 6.
  rels.
  arewrite (⦗RW~Sc⦘ ⨾ ⦗Sc⦘ ⊆ ⦗RW~Sc⦘).
  arewrite (⦗Sc⦘ ⨾ ⦗RW~Sc⦘ ⊆ ⦗RW~Sc⦘).
  rewrite RW_scb_RW.
  rewrite hb_loc_in_eco; auto.
  arewrite (sb_neq_loc ⊆ sb').
    by apply sb_neq_loc_in_sb_minus_rmw; auto.
  arewrite (sb ⊆ sb' ∪ rmw) at 1.
    by unfold inclusion, minus_rel, union; ins; tauto.
  rewrite rmw_in_rb at 2; auto.
  rewrite mo_in_eco; auto.
  rewrite rb_in_eco; auto.
  rewrite <- !unionA.
  relsf.
  arewrite (⦗RW~Sc⦘ ⨾ sb' ⨾ ⦗RW~Sc⦘ ⊆ hb ⨾ ⦗F~Sc⦘ ⨾ hb).
    by rewrite <- HSC; rels.
  arewrite (⦗RW~Sc⦘ ⨾ sb' ⨾ hb ⨾ sb' ⨾ ⦗RW~Sc⦘ ⊆ hb ⨾ ⦗F~Sc⦘ ⨾ hb).
    by rewrite <- HSC; rels; basic_solver 10.
  eapply acyclic_mon with (r := hb ⨾ ⦗F~Sc⦘ ⨾ hb ∪ ⦗RW~Sc⦘ ⨾ eco ⨾ ⦗RW~Sc⦘).
  2: repeat apply inclusion_union_l; rels.
  apply acyclic_utt; splits.
  * apply transitiveI; arewrite_id ⦗F~Sc⦘ at 1; relsf.
  * apply transitiveI.
    arewrite_id ⦗RW~Sc⦘ at 2; relsf.
    arewrite_id ⦗RW~Sc⦘ at 2; relsf.
  * arewrite_id ⦗F~Sc⦘ at 1; relsf.
    by apply irr_hb.
  * arewrite_id ⦗RW~Sc⦘; relsf.
    by apply irr_eco.
  * arewrite (⦗F~Sc⦘ ⊆ ⦗F~Sc⦘ ⨾ ⦗F~Sc⦘).
      by basic_solver.
    do 2 (apply acyclic_seqC; try rewrite !seqA).
    eapply acyclic_mon with (r := psc_f); try done.
    unfold RC11_Model.psc_f.
    basic_solver 12.
- by rewrite psc_f_f.
- rewrite psc_rw_rw; try assumption.
  rewrite RW_scb_RW.
  arewrite (
    sb ∪ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ∪ ⦗RW⦘ ⨾ hb|loc ⨾ ⦗RW⦘ ∪ mo ∪ rb 
      ⊆ sb' ∪ sb' ⨾ hb ⨾ sb' ∪ eco
  ).
  { arewrite (sb ⊆ sb' ∪ rmw).
      by apply inclusion_union_minus. 
    rewrite rmw_in_rb at 2; try assumption.
    rewrite rb_in_eco, mo_in_eco, sb_neq_loc_in_sb_minus_rmw, hb_loc_in_eco; try assumption.
    basic_solver 10.
  }
  sin_rewrite psc_rw_f; try assumption.
  sin_rewrite psc_f_rw; try assumption.
  rewrite psc_f_f; try assumption.
  arewrite_id ⦗RW~Sc⦘ at 1.
  arewrite_id ⦗RW~Sc⦘ at 3.
  rels.
  rewrite <- !seqA with (r3 := psc_f ^*), global_sc_helper; try assumption.
  red; rels.
Qed.

(* Definition change_mode (l: label) (m: mode) : label := 
  match l with
  | Aload l v _ => Aload l v m
  | Astore l v _ => Astore l v m
  | Afence _ => Afence m
  end. *)
  
(* Definition change_modes (G: execution) (A: event -> Prop) (m: mode): execution :=
  Build_execution 
    acts
    (fun a => if (A a) then change_mode (lab a) m else lab a)
    sb rmw rf mo. *)

(* Lemma transf_g
  (NO_SC: ⦗Sc⦘ ≡ ∅₂)
  A (A_SUB: A ⊆₁ R_acq ∪₁ W_rel)
  (A1: ⦗A⦘ ⨾ (sb' ∪ sb'⨾hb⨾sb') ⨾ ⦗A⦘ ⊆ hb ⨾ ⦗F~Sc⦘ ⨾ hb)
  (A2: ⦗A⦘ ⨾ rmw ≡ rmw ⨾ ⦗A⦘)
  (G' : execution) (CHANGE: G' = G)
  : consistent G'.
Proof.
Admitted. *)

End GlobalSC.
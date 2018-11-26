Require Import Classical List Relations Peano_dec.
Require Import Hahn.

Require Import Basic RC11_Events RC11_Model.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section PSC.

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
Notation "'sb_neq_loc'" := G.(sb_neq_loc).
Notation "'scb'" := G.(scb).

Notation "'same_loc'" := G.(same_loc).
Notation "a |loc" := (a ∩ same_loc) (at level 1).

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

(* Definition psc_base_expanded_naive := 
    ⦗Sc⦘ ⨾ sb ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ hb_loc ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ mo ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ rb ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ sb ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗Sc⦘ ⨾ hb_loc ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗Sc⦘ ⨾ mo ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗Sc⦘ ⨾ rb ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ sb ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ hb_loc ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ mo ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ rb ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ sb ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ hb_loc ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ mo ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ rb ⨾ hb ⨾ ⦗F~Sc⦘.

Lemma psc_base_expanded_naive_eq : psc_base ≡ psc_base_expanded_naive.
Proof.
  unfold psc_base, scb, psc_base_expanded_naive; relsf.
  rewrite !seqA.
  split; repeat apply inclusion_union_l; eauto 8 with rel.
  all: try (repeat (apply inclusion_union_r; constructor); done).
  by rewrite sb_neq_loc_in_sb at 1; rewrite sb_neq_loc_in_hb at 1; 
  sin_rewrite !hb_hb; eauto 35 with rel.
  all: rewrite sb_neq_loc_in_hb at 1; rewrite sb_neq_loc_in_sb at 1; sin_rewrite !hb_hb.
  all: try (repeat (apply inclusion_union_r; constructor); done).
Qed. *)

(* Definition psc_base_expanded_typ := 
    ⦗RW~Sc⦘ ⨾ scb ⨾ ⦗RW~Sc⦘
  ∪ ⦗RW~Sc⦘ ⨾ (sb ∪ hb_loc ∪ mo ∪ rb) ⨾ hb^? ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb^? ⨾ (sb ∪ hb_loc ∪ mo ∪ rb) ⨾ ⦗RW~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb^? ⨾ (sb ∪ hb_loc ∪ mo ∪ rb) ⨾ hb^? ⨾ ⦗F~Sc⦘.

Lemma psc_base_expanded_typ_eq : psc_base ≡ psc_base_expanded_typ.
Proof.
split.
- rewrite psc_base_expanded_naive_eq.
unfold psc_base_expanded_naive, psc_base_expanded_typ.
repeat try (arewrite (⦗Sc⦘ ⊆ ⦗RW~Sc⦘ ∪ ⦗F~Sc⦘);[
solve_type_mismatch 8| ]).

unfold scb.
rewrite !crE.
relsf.
repeat apply inclusion_union_l.
all: try (repeat (apply inclusion_union_r; constructor); done).
all:rewrite !seqA.
all: try (repeat (apply inclusion_union_r; constructor); done).
arewrite (sb_neq_loc ⨾ hb ⨾ sb_neq_loc ⊆ sb ⨾ hb).
admit.
all: try (repeat (apply inclusion_union_r; constructor); done).
arewrite (sb_neq_loc ⨾ hb ⨾ sb_neq_loc ⊆  hb ⨾ sb).

admit.
all: try (repeat (apply inclusion_union_r; constructor); done).
arewrite (sb_neq_loc ⨾ hb ⨾ sb_neq_loc ⊆  hb ⨾ sb).
admit.
all: try (repeat (apply inclusion_union_r; constructor); done).
- 
rewrite psc_base_expanded_naive_eq.
unfold psc_base_expanded_naive, psc_base_expanded_typ.
repeat try (arewrite (⦗RW~Sc⦘ ⊆ ⦗Sc⦘); [ solve_type_mismatch |]).
unfold scb.
rewrite !crE.
relsf.
repeat apply inclusion_union_l.
all: try (repeat (apply inclusion_union_r; constructor); done).
rewrite !seqA.
all: try (repeat (apply inclusion_union_r; constructor); done).

unfold
arewrite (⦗Sc⦘ ≡ ⦗RW~Sc⦘ ∪ ⦗F~Sc⦘).
solve_type_mismatch 8.
arewrite (⦗Sc⦘ ≡ ⦗RW~Sc⦘ ∪ ⦗F~Sc⦘).
solve_type_mismatch 8.
relsf.
unfold .
 scb, psc_base_expanded_naive; relsf.
  rewrite !seqA.
  split; repeat apply inclusion_union_l; eauto 8 with rel.
  all: try (repeat (apply inclusion_union_r; constructor); done).
  by rewrite sb_neq_loc_in_sb at 1; rewrite sb_neq_loc_in_hb at 1; 
  sin_rewrite !hb_hb; eauto 35 with rel.
  all: rewrite sb_neq_loc_in_hb at 1; rewrite sb_neq_loc_in_sb at 1; sin_rewrite !hb_hb.
  all: try (repeat (apply inclusion_union_r; constructor); done).
Qed. *)

(* Definition psc_f_expanded_naive := 
    ⦗F~Sc⦘ ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ eco ⨾ hb ⨾ ⦗F~Sc⦘.

Lemma psc_f_expanded_naive_eq : psc_f ≡ psc_f_expanded_naive.
Proof. 
  by unfold psc_f, psc_f_expanded_naive; relsf; rewrite !seqA.
Qed.
*)

Lemma scb_in_hb_eco (WF: Wf G) : scb ⊆ hb ∪ eco.
Proof.
unfold RC11_Model.scb.
rewrite hb_loc_in_hb.
arewrite (sb_neq_loc ⊆ hb); unionL; eauto with rel rel_full.
arewrite !(hb ⨾ hb ⊆ hb); auto with rel.
Qed.

Lemma psc_sc (WF: Wf G) : psc ⊆ ⦗Sc⦘ ⨾ psc ⨾ ⦗Sc⦘.
Proof.
unfold RC11_Model.psc, RC11_Model.psc_base, RC11_Model.psc_f.
assert (H: F~Sc ⊆₁ Sc) by  solve_type_mismatch.
basic_solver 42.
Qed.

Lemma psc_f_f (WF: Wf G) : (⦗F~Sc⦘ ⨾ psc ⨾ ⦗F~Sc⦘) ⊆ psc_f.
Proof.
unfold RC11_Model.psc; relsf.
apply inclusion_union_l.
2: arewrite_id (⦗F~Sc⦘); rels.
unfold psc_base; relsf; rewrite !seqA.
arewrite_id ⦗Sc⦘; rels.
rewrite scb_in_hb_eco; try assumption.
relsf.
rewrite eco_dom; try assumption; rewrite ?seqA.
arewrite_false !(⦗F~Sc⦘ ⨾ ⦗RW⦘).
  by solve_type_mismatch.
rels.
arewrite_false !(⦗RW⦘ ⨾ ⦗F~Sc⦘).
  by solve_type_mismatch.
rels.
arewrite !(hb ⨾ hb ⊆ hb).
arewrite_id (⦗RW⦘).
unfold RC11_Model.psc_f; relsf; rewrite !seqA.
unionL; eauto 6 with rel.
Qed.

Lemma psc_rw_rw (WF: Wf G) : ⦗RW~Sc⦘ ⨾ psc ⨾ ⦗RW~Sc⦘ ⊆ 
  ⦗RW~Sc⦘ ⨾ scb ⨾ (⦗RW~Sc⦘).
Proof.
unfold RC11_Model.psc, RC11_Model.psc_base; relsf; rewrite !seqA.
unfold RC11_Model.psc_f.
arewrite_false !(⦗F~Sc⦘ ⨾ ⦗RW~Sc⦘); rels.
    solve_type_mismatch.
arewrite_false !(⦗RW~Sc⦘ ⨾ ⦗F~Sc⦘); rels.
    solve_type_mismatch.
arewrite_id (⦗Sc⦘); rels.
Qed.

Lemma psc_rw_f (WF: Wf G) : ⦗RW~Sc⦘ ⨾ psc ⨾ ⦗F~Sc⦘ ⊆ 
  ⦗RW~Sc⦘ ⨾ eco^? ⨾ hb ⨾ (⦗F~Sc⦘).
Proof.
unfold RC11_Model.psc, RC11_Model.psc_base, RC11_Model.psc_f; relsf; rewrite !seqA.
rewrite scb_in_hb_eco; auto; relsf.
arewrite_id (⦗Sc⦘); rels.
rewrite eco_dom at 1; auto; rewrite ?seqA.
arewrite_false !(⦗RW~Sc⦘ ⨾ ⦗F~Sc⦘); rels.
    solve_type_mismatch.
arewrite_false !(⦗RW⦘ ⨾ ⦗F~Sc⦘); rels.
    solve_type_mismatch.
arewrite !(hb ⨾ hb ⊆ hb).
repeat apply inclusion_union_l; try basic_solver 8.
Qed.

Lemma psc_f_rw (WF: Wf G) : ⦗F~Sc⦘ ⨾ psc ⨾ ⦗RW~Sc⦘ ⊆ 
  ⦗F~Sc⦘ ⨾ hb ⨾ eco^? ⨾ (⦗RW~Sc⦘).
Proof.
unfold RC11_Model.psc, RC11_Model.psc_base, RC11_Model.psc_f; relsf; rewrite !seqA.
rewrite scb_in_hb_eco; auto; relsf.
arewrite_id (⦗Sc⦘); rels.
rewrite eco_dom at 1; auto; rewrite ?seqA.
arewrite_false !( ⦗F~Sc⦘ ⨾ ⦗RW~Sc⦘); rels.
    solve_type_mismatch.
arewrite_false !(⦗F~Sc⦘ ⨾ ⦗RW⦘); rels.
    solve_type_mismatch.
arewrite !(hb ⨾ hb ⊆ hb).
repeat apply inclusion_union_l; try basic_solver 10.
Qed.

(* Definition psc_expanded_naive := 
    ⦗Sc⦘ ⨾ sb ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ hb_loc ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ mo ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ rb ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ sb ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗Sc⦘ ⨾ hb_loc ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗Sc⦘ ⨾ mo ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗Sc⦘ ⨾ rb ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ sb ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ hb_loc ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ mo ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ rb ⨾ ⦗Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb ⨾ eco ⨾ hb ⨾ ⦗F~Sc⦘.

Lemma psc_expanded_naive_eq (WF: Wf) : psc ≡ psc_expanded_naive.
unfold psc, psc_expanded_naive.
rewrite psc_base_expanded_naive_eq, psc_f_expanded_naive_eq.
unfold psc_base_expanded_naive, psc_f_expanded_naive.
  split; repeat apply inclusion_union_l; eauto 8 with rel.
  all: try (repeat (apply inclusion_union_r; constructor); done).
  by sin_rewrite sb_in_hb; sin_rewrite !hb_hb;
     repeat (apply inclusion_union_r; constructor).
  by rewrite hb_loc_in_hb at 1; sin_rewrite hb_hb; sin_rewrite hb_hb; 
    relsf; try done.
  by sin_rewrite mo_in_eco;
     repeat (apply inclusion_union_r; constructor).
  by sin_rewrite rb_in_eco;
     repeat (apply inclusion_union_r; constructor).
Qed. *)

(*
Lemma psc_expanded_eq (WF: Wf) : psc ≡ psc_expanded. 
Proof.
  assert (X: ⦗F~Sc⦘ ⊆ ⦗Sc⦘).
    by unfold is_sc, is_sc_f, mod, eqv_rel, inclusion; ins; desf. 

  rewrite psc_expanded_naive_eq.
  unfold psc_expanded_naive, psc_expanded; relsf.
  split; repeat apply inclusion_union_l; eauto 8 with rel;
  eauto 15 with rel.
  by rewrite sb_in_hb at 1; sin_rewrite !hb_hb; eauto 12 with rel.
  by rewrite sb_in_hb at 1; sin_rewrite !hb_hb; eauto 12 with rel.
  by rewrite sb_in_hb at 1; sin_rewrite !hb_hb; eauto 12 with rel.

  by rewrite fence_hb_r; repeat apply inclusion_union_l; eauto 20 with rel.
  by rewrite fence_hb_l; repeat apply inclusion_union_l; eauto 8 with rel; 
     eauto 20 with rel.
Qed.


Lemma acyclic_case_split2 A (R : relation A) (f : A -> Prop) :
  acyclic R <->
  acyclic (restr_rel (fun x => ~ f x) R) /\ irreflexive (⦗f⦘ ⨾ R ⁺).
Proof.
  rewrite acyclic_case_split with (f := fun x => ~ f x), seq_eqv_l;
  unfold irreflexive; intuition; eauto. 
Qed. 

Lemma inclusion_seq_cr_r A (r r' r'' : relation A) :
  r ⊆ r' -> r ⊆ r' ⨾ r'' ^?. 
Proof.
  by rewrite crE; relsf.
Qed.


Lemma path_red_dom A (r r' : relation A) (f : A -> Prop) 
  (INCL : r ⨾ ⦗f⦘ ⨾ r ⊆ r' ⁺)
  (INCL1 : ⦗fun x => ~ f x⦘ ⨾ r ⨾ ⦗f⦘ ⨾ r' ⊆ r' ⁺)
  (L : ⦗fun x => ~ f x⦘ ⨾ r ⨾ ⦗fun x => ~ f x⦘ ⊆ r' ⁺) :
  r ⁺ ⊆ 
  r ∪ r ⨾ ⦗fun x => ~ f x⦘ ⨾ r ⨾ ⦗f⦘ 
    ∪ r ^? ⨾ r' ⁺ ⨾ (⦗fun x : A => ~ f x⦘ ⨾ r ⨾ ⦗f⦘) ^?.
Proof.
  assert (K: r ≡ ⦗f⦘ ⨾ r ∪ ⦗fun x => ~ f x⦘ ⨾ r).
    rewrite !seq_eqv_l; unfold union; split; red; ins; desf; tauto.
  assert (K': r ≡ r ⨾ ⦗f⦘ ∪ r ⨾ ⦗fun x => ~ f x⦘).
    rewrite !seq_eqv_r; unfold union; split; red; ins; desf; tauto.
  assert (M: r ⨾ r ⊆ r' ⁺ ∪ r ⨾ ⦗fun x => ~ f x⦘ ⨾ r).
    by rewrite K at 2; relsf.

  apply inclusion_t_ind_left; relsf. 
  rewrite (crE r); relsf; rewrite ?seqA.
  sin_rewrite !M; relsf; rewrite ?seqA.
  repeat apply inclusion_union_l; eauto 12 using inclusion_seq_cr_r with rel.

{
  rewrite K' at 2; relsf; sin_rewrite L.
  repeat apply inclusion_union_l; eauto 12 using inclusion_seq_cr_r with rel.
}
{
  rewrite K' at 2; relsf; sin_rewrite L; rewrite !seqA.
  repeat apply inclusion_union_l; eauto 12 using inclusion_seq_cr_r with rel.
  by unfold seq, eqv_rel; red; ins; desf.
}
  by sin_rewrite ct_ct; eauto with rel.

  rewrite K' at 2; relsf; sin_rewrite L; rewrite ?seqA.
  repeat apply inclusion_union_l; eauto 12 using inclusion_seq_cr_r with rel.
    rewrite ct_begin at 1; rewrite !seqA; sin_rewrite INCL1.
    by seq_rewrite ct_rt; eauto with rel.
  sin_rewrite ct_ct; eauto 10 with rel.
Qed. 

Lemma acyclic_red_dom A (r r' : relation A) (f : A -> Prop) 
  (INCL : r ⨾ ⦗f⦘ ⨾ r ⊆ r' ⁺)
  (INCL1 : ⦗fun x => ~ f x⦘ ⨾ r ⨾ ⦗f⦘ ⨾ r' ⊆ r' ⁺)
  (INCL2 : ⦗fun x => ~ f x⦘ ⨾ r ⨾ ⦗fun x => ~ f x⦘ ⊆ r' ⁺)
  (INCL3 : r' ⨾ ⦗f⦘ ⨾ r ⨾ ⦗fun x => ~ f x⦘ ⊆ r' ⁺)
  (IRR : irreflexive r)
  (IRR' : irreflexive (r' ⁺ ⨾ ⦗f⦘ ⨾ r ⨾ ⦗f⦘)) 
  (ACYC : acyclic r') :
  acyclic r. 
Proof.
  assert (K: r ≡ ⦗f⦘ ⨾ r ∪ ⦗fun x => ~ f x⦘ ⨾ r).
    rewrite !seq_eqv_l; unfold union; split; red; ins; desf; tauto.
  assert (K': r ≡ r ⨾ ⦗f⦘ ∪ r ⨾ ⦗fun x => ~ f x⦘).
    rewrite !seq_eqv_r; unfold union; split; red; ins; desf; tauto.

  unfold acyclic; rewrite path_red_dom; eauto.
  rewrite !crE; relsf.
  rewrite !irreflexive_union; intuition.
{
  by rewrite irreflexive_seqC, !seqA, INCL, inclusion_seq_eqv_l;
     eapply irreflexive_inclusion, ACYC; eauto with rel.
}{
  rewrite irreflexive_seqC, !seqA, ct_begin. 
  by sin_rewrite INCL1; rewrite ct_rt. 
}{
  rewrite K; relsf; rewrite seqA, irreflexive_union; split. 

  rewrite <- seqA, irreflexive_seqC, K'; relsf; rewrite ?seqA.
  rewrite irreflexive_union; split; ins. 
  by rewrite ct_end, seqA; sin_rewrite INCL3; rewrite rt_ct. 

  rewrite K'; relsf; rewrite !seqA, ct_begin at 1. 
  by sin_rewrite INCL1; sin_rewrite INCL2; rewrite ct_rt, ct_ct, unionK.
}{
  rewrite irreflexive_seqC, !seqA, INCL, inclusion_seq_eqv_l. 
  eapply irreflexive_inclusion, ACYC; etransitivity; 
  try apply ct_ct; eauto with rel. 
}
Qed.

Lemma restr_relE  A (r : relation A) (f : A -> Prop) : 
  restr_rel f r ≡ ⦗f⦘ ⨾ r ⨾ ⦗f⦘.
Proof.
  rewrite seq_eqv_r, seq_eqv_l; unfold restr_rel. 
  split; red; tauto.
Qed.  


Definition psc_alt3 := 
    ⦗Sc⦘ ⨾ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ sb ⨾ ⦗Sc⦘
  ∪ eco
  ∪ hb ⨾ ⦗F~Sc⦘
  ∪ ⦗F~Sc⦘ ⨾ hb.

Lemma acyclic_psc_alt3 (WF: Wf) : acyclic psc_alt3 -> acyclic psc. 
Proof.
  rewrite psc_expanded_eq in *; ins; desf.
  eapply irreflexive_inclusion, H. 
  unfold psc_expanded, psc_alt3.
  apply inclusion_t_ind; eauto with rel. 
  repeat apply inclusion_union_l; eauto 15 with rel.
  by rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r; eauto 10 with rel.
  by rewrite inclusion_seq_eqv_l; eauto 10 with rel.
  by rewrite inclusion_seq_eqv_l; eauto 10 using inclusion_step2_ct with rel.
  by rewrite inclusion_seq_eqv_r; eauto 10 using inclusion_step2_ct with rel.
  by rewrite inclusion_seq_eqv_r, <- seqA; 
     eauto 10 using inclusion_step2_ct with rel.
  by rewrite <- seqA; etransitivity; try eapply ct_ct;
     eauto 10 using inclusion_step2_ct with rel.
Qed.

Definition psc_alt2 := 
    ⦗Sc⦘ ⨾ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ⨾ ⦗Sc⦘
  ∪ ⦗Sc⦘ ⨾ sb ⨾ ⦗Sc⦘
  ∪ eco
  ∪ hb ⨾ ⦗F~Sc⦘ ⨾ hb.

Lemma acyclic_psc_alt2 
   (WF: Wf) (HB: irreflexive hb) (ACYC: acyclic psc_alt2) : acyclic psc. 
Proof.
  ins; apply acyclic_psc_alt3; try done.
  unfold psc_alt3, psc_alt2 in *.
  revert ACYC.
  set (r := ⦗Sc⦘ ⨾ sb_neq_loc ⨾ hb ⨾ sb_neq_loc ⨾ ⦗Sc⦘
         ∪ ⦗Sc⦘ ⨾ sb ⨾ ⦗Sc⦘ ∪ eco).

  assert (X : r ⨾ ⦗F~Sc⦘ ⊆ hb ⨾ ⦗F~Sc⦘).
  { 
     subst r; relsf; rewrite !seqA.
     rewrite sb_neq_loc_in_hb, sb_in_hb; sin_rewrite !hb_hb.
     rewrite !(inclusion_seq_eqv_l (dom:=Sc)), seq_eco_sc_f; relsf.
  }

  assert (Y : ⦗F~Sc⦘ ⨾ r ⊆ ⦗F~Sc⦘ ⨾ hb).
  { 
     subst r; relsf.
     rewrite sb_neq_loc_in_hb, sb_in_hb; sin_rewrite !hb_hb.
     rewrite !(inclusion_seq_eqv_r).
     rewrite !(inclusion_seq_eqv_l (dom:=Sc)), seq_sc_f_eco; relsf.
  }

  revert X Y; generalize r; clear r; ins.
  eapply acyclic_red_dom with (f := F~Sc); eauto;
  relsf; rewrite ? seqA; seq_rewrite ? seq_eqvK. 

  all: repeat apply inclusion_union_l;
  eauto 10 using inclusion_seq_eqv_l, inclusion_seq_eqv_r, inclusion_step2_ct with rel.
  all: try solve [unfold seq, eqv_rel; red; ins; desf; done]. 

  by sin_rewrite X; rewrite seqA, inclusion_seq_eqv_r; eauto with rel.
  
  by sin_rewrite X; rewrite seqA; eauto with rel.
  by sin_rewrite Y; rewrite inclusion_seq_eqv_l; eauto with rel.
  by rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r; eauto with rel.

  by rewrite 2!inclusion_seq_eqv_l; eauto using inclusion_step2_ct with rel.
  by rewrite 2!inclusion_seq_eqv_l; eauto using inclusion_step2_ct with rel.
  by rewrite inclusion_seq_eqv_l, Y; eauto using inclusion_step2_ct with rel.

  by rewrite 2!inclusion_seq_eqv_l; sin_rewrite hb_hb; 
     eauto using inclusion_step2_ct with rel.
  by rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r; 
     eauto using inclusion_step2_ct with rel.
  by rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r; 
     eauto using inclusion_step2_ct with rel.
  by rewrite inclusion_seq_eqv_r; sin_rewrite X; rewrite seqA; 
     eauto using inclusion_step2_ct with rel.
  by sin_rewrite Y; rewrite seqA, inclusion_seq_eqv_l, inclusion_seq_eqv_r;
     sin_rewrite hb_hb; eauto using inclusion_step2_ct with rel.
  by rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r; 
     sin_rewrite hb_hb; eauto using inclusion_step2_ct with rel.

  rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r.
  rewrite unionA, unionK, irreflexive_union; split; ins.
  by eapply irreflexive_inclusion, ACYC; eauto with rel.
    
  rewrite inclusion_seq_eqv_r, inclusion_seq_eqv_l with (rel:=r).
  rewrite unionA, unionK, irreflexive_union; split; ins.
    by eapply irreflexive_inclusion, ACYC; eauto 10 using inclusion_t_r_t with rel.
  rewrite ct_end, !seqA; relsf.
  sin_rewrite X; rewrite seqA, inclusion_seq_eqv_r.
  rewrite irreflexive_union; split; ins;
  eapply irreflexive_inclusion, ACYC; rewrite ct_end; apply seq_mori; eauto with rel.
  rewrite inclusion_seq_eqv_l at 1; rewrite hb_hb; eauto with rel.
Qed. 
*)

(*Hypothesis (CON: consistent).*)
(*Definition consistent :=
  << WF   : Wf >> /\
  << COH  : irreflexive (hb ⨾ clos_refl eco) >> /\
  << AT   : irreflexive (rmw ⨾ transp rmw ⨾ rf⁻¹) >> /\
  << SC   : acyclic psc >> /\
  << SBRF : acyclic (sb ∪ rf) >>.
*)


End PSC.
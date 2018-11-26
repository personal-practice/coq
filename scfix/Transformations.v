(******************************************************************************)
(** * Correctness of Program Transformations *)
(******************************************************************************)
Require Import Classical List Relations Peano_dec.
Require Import ClassicalDescription IndefiniteDescription.
Require Import Hahn.
Require Import Basic.
Require Import RC11_Events RC11_Model.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section Transformation.

Variables Gsrc Gtgt : execution.

(* Target notation *)
Notation "'acts`'" := Gtgt.(acts).
Notation "'lab`'" := Gtgt.(lab).
Notation "'loc`'" := (loc lab`).
Notation "'val`'" := (val lab`).
Notation "'mod`'" := (mod lab`).

Notation "'sb`'" := Gtgt.(sb).
Notation "'rf`'" := Gtgt.(rf).
Notation "'mo`'" := Gtgt.(mo).
Notation "'rs`'" := Gtgt.(rs).
Notation "'release`'" := Gtgt.(release).
Notation "'sw`'" := Gtgt.(sw).
Notation "'rb`'" := Gtgt.(rb).
Notation "'hb`'" := Gtgt.(hb).
Notation "'data`'" := Gtgt.(data).
Notation "'addr`'" := Gtgt.(addr).
Notation "'ctrl`'" := Gtgt.(ctrl).
Notation "'deps`'" := Gtgt.(deps).
Notation "'eco`'" := Gtgt.(eco).
Notation "'same_loc`'" := Gtgt.(same_loc).
Notation "r |loc`" := (r ∩ same_loc`) (at level 1).
Notation "'psc`'" := Gtgt.(psc).
Notation "'psc_base`'" := Gtgt.(psc_base).
Notation "'psc_f`'" := Gtgt.(psc_f).
Notation "'scb`'" := Gtgt.(scb).
Notation "'conflicting`'" := Gtgt.(conflicting).
Notation "'race`'" := Gtgt.(race).
Notation "'racy`'" := Gtgt.(racy).

Notation "'E`'" := Gtgt.(E).
Notation "'F`'" := (F lab`).
Notation "'R`'" := (R lab`).
Notation "'W`'" := (W lab`).
Notation "'RMW`'" := (RMW lab`).
Notation "'RW`'" := (RW lab`).
Notation "'FR`'" := (FR lab`).
Notation "'FW`'" := (FW lab`).
Notation "'Na`'" := (Only_Na lab`).
Notation "'Rlx`'" := (Rlx lab`).
Notation "'Rel`'" := (Rel lab`).
Notation "'Acq`'" := (Acq lab`).
Notation "'Acqrel`'" := (Acqrel lab`).
Notation "'Sc`'" := (Sc lab`).

(* Source notation *)
Notation "'acts'" := Gsrc.(acts).
Notation "'lab'" := Gsrc.(lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).

Notation "'sb'" := Gsrc.(sb).
Notation "'rf'" := Gsrc.(rf).
Notation "'mo'" := Gsrc.(mo).
Notation "'rs'" := Gsrc.(rs).
Notation "'release'" := Gsrc.(release).
Notation "'sw'" := Gsrc.(sw).
Notation "'rb'" := Gsrc.(rb).
Notation "'hb'" := Gsrc.(hb).
Notation "'data'" := Gsrc.(data).
Notation "'addr'" := Gsrc.(addr).
Notation "'ctrl'" := Gsrc.(ctrl).
Notation "'deps'" := Gsrc.(deps).
Notation "'eco'" := Gsrc.(eco).
Notation "'same_loc'" := Gsrc.(same_loc).
Notation "r |loc" := (r ∩ same_loc) (at level 1).
Notation "'psc'" := Gsrc.(psc).
Notation "'psc_base'" := Gsrc.(psc_base).
Notation "'psc_f'" := Gsrc.(psc_f).
Notation "'scb'" := Gsrc.(scb).
Notation "'conflicting'" := Gsrc.(conflicting).
Notation "'race'" := Gsrc.(race).
Notation "'racy'" := Gsrc.(racy).

Notation "'E'" := Gsrc.(E).
Notation "'F'" := (F lab).
Notation "'R'" := (R lab).
Notation "'W'" := (W lab).
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

Definition valid_transformation :=
  (consistent Gtgt -> consistent Gsrc) /\
  (racy` ⊆ racy).

(* Lemma I.1: Strengthening *)
Section Strengthening.

Hypothesis ACTS: acts = acts`.
Hypothesis SB: sb ≡ sb`.
Hypothesis RF: rf ≡ rf`.
Hypothesis MO: mo ≡ mo`.
Hypothesis DATA: data ≡ data`.
Hypothesis ADDR: addr ≡ addr`.
Hypothesis CTRL: ctrl ≡ ctrl`.
Hypothesis S_R: R ≡₁ R`.
Hypothesis S_W: W ≡₁ W`.
Hypothesis S_F: F ≡₁ F`.
Hypothesis S_L: loc = loc`.
Hypothesis S_V: val = val`.
Hypothesis M_Na: Na ≡₁ Na`.
Hypothesis M_RLX: Rlx ⊆₁ Rlx`.
Hypothesis M_REL: Rel ⊆₁ Rel`.
Hypothesis M_ACQ: Acq ⊆₁ Acq`.
Hypothesis M_ACQREL: Acqrel ⊆₁ Acqrel`.
Hypothesis M_SC: Sc ⊆₁ Sc`.
Hypothesis LAB_INIT: forall l : location, lab (Init l) = lab` (Init l).

Lemma eqv_inter A (P P' : A -> Prop) : ⦗P ∩₁ P'⦘ ≡ ⦗P⦘ ∩ ⦗P'⦘.
Proof. basic_solver. Qed.

Tactic Notation "cassert" uconstr(H) :=
  let ID := fresh in try (assert (ID := H); crewrite ID).

Ltac oto_basic := rewrite ?eqv_inter;
  crewrite ACTS; crewrite SB; crewrite RF; crewrite MO; crewrite DATA;
  crewrite ADDR; crewrite CTRL; crewrite S_R; crewrite S_W; crewrite S_F;
  crewrite S_L; crewrite S_V; crewrite M_Na; crewrite M_RLX; crewrite M_REL;
  crewrite M_ACQ; crewrite M_ACQREL; crewrite M_SC; crewrite LAB_INIT.

(* Lemma S_E: E ≡₁ E`.
Proof. by unfold RMW_Model.E; oto_basic. Qed.

Lemma S_RW: RW ≡₁ RW`.
Proof.
  unfold RMW_Events.RW; unfolder.
  ins; split; ins; desf; (apply S_R in H + apply S_W in H); auto.
Qed.

Lemma SAME_LOC: same_loc ≡ same_loc`.
Proof. by unfold RMW_Model.same_loc; oto_basic. Qed.
 
Lemma RS: rs ⊆ rs`.
Proof.
  unfold RMW_Model.rs.
  cassert S_E; cassert SAME_LOC.
  by oto_basic.
Qed.

Lemma REL: rel ⊆ rel`.
Proof.
  unfold RMW_Model.rel.
  cassert RS.
  by oto_basic.
Qed.

Lemma SW: sw ⊆ sw`.
Proof.
  unfold RMW_Model.sw.
  cassert REL.
  by oto_basic.
Qed.

Lemma HB: hb ⊆ hb`.
Proof.
  unfold RMW_Model.hb.
  cassert SW.
  by oto_basic.
Qed.

Lemma RB: rb ≡ rb`.
Proof.
  unfold RMW_Model.rb.
  cassert S_E.
  by oto_basic.
Qed.

Lemma ECO: eco ≡ eco`.
Proof.
  unfold RMW_Model.eco.
  cassert RB.
  by oto_basic.
Qed.

Lemma SCB: scb ⊆ scb`.
Proof.
  unfold RMW_Model.scb, RMW_Model.sb_neq_loc, RMW_Model.sb_loc, RMW_Model.hb_loc.
  cassert HB; cassert RB; cassert SAME_LOC; cassert S_RW.
  by oto_basic.
Qed.

Lemma PSC_BASE: psc_base ⊆ psc_base`.
Proof.
  unfold RMW_Model.psc_base.
  cassert HB; cassert SCB.
  by oto_basic.
Qed.

Lemma PSC_F: psc_f ⊆ psc_f`.
Proof.
  unfold RMW_Model.psc_f.
  cassert HB; cassert ECO.
  by oto_basic.
Qed.

Lemma PSC: psc ⊆ psc`.
Proof.
  unfold RMW_Model.psc.
  cassert PSC_BASE; cassert PSC_F.
  by oto_basic.
Qed.

Ltac cassert_all :=
  cassert S_E; cassert S_RW; cassert SAME_LOC; cassert RS; cassert REL;
  cassert SW; cassert HB; cassert RB; cassert ECO; cassert SCB;
  cassert PSC_BASE; cassert PSC_F; cassert PSC.

Ltac oto := try solve [by oto_basic | cassert_all; by oto_basic].

Lemma strengthening : valid_transformation.
Proof with red; splits; oto.
  split.
  - (* Consistent *)
    red; unfold consistent; unnw; ins; desf; splits.
    + (* Wf *)
      cdes H; red; splits.
      * (* WfACTS *) cdes WF_ACTS...
      * (* WfSB *) cdes WF_SB...
      * (* WfRF *)
        cdes WF_RF...
        (* RF_TOT *)
        oto_basic.
        ins; specialize (RF_TOT b).
        apply S_R in READ; intuition.
        by desf; exists a; apply RF.
      * (* WfMO *)
        cdes WF_MO...
        (* MO_TOT *)
        oto_basic.
        ins; specialize (MO_TOT l).
        unfold is_total in *.
        ins; desf; apply S_W in IWa0; apply S_W in IWb0; auto.
      * (* WfDEPS *) cdes WF_DEPS...
    + (* Coherent *) cdes H0...
    + (* Atomic *) cdes H1...
    + (* PSC *) cdes H2...
    + (* No-thin-air *) cdes H3...
  - (* Racy *)
    unfold RMW_Model.racy, RMW_Model.race, RMW_Model.conflicting.
    oto.
Qed.
 *)
End Strengthening.

End Transformation.

(*
Definition transformation := rmw_execution -> rmw_execution.

Definition valid_transformation (Gsrc: rmw_execution) (Tr: transformation) :=
  consistent (Tr Gsrc) -> consistent Gsrc.

Definition strengthening : transformation := fun Gsrc =>
  Gsrc.

Lemma strengthening_valid : valid_transformation Gr strengthening.
Proof.
  red.
  unfold strengthening.
  done.
Qed. *)

(* 
Definition mapR (g : event -> event) R := 
  (fun a b => exists a' b', g a' = a /\ g b' = b /\ R a' b').
  
Definition add_beween R A B new := (fun a b : event => 
  R a b \/ A a /\ b = new \/ a = new /\ B b).

Lemma add_f_wf acts sb rmw rf mo sc
    (WF: Wf acts sb rmw rf mo sc)
    A B (NRMW: forall a b, A a /\ B b -> ~ rmw a b)
    i (TID: forall a, A a \/ B a <-> thread a = i \/ is_init a) 
    f (NINf: ~ In f acts) (TIDf: thread f = i)  (LABf: lab f = Afence Orel)
    acts' (ACTS': acts' = f :: acts)
    sb' (SB': sb' = add_beween sb A B f) :
    Wf acts' sb' rmw rf mo sc.
Proof.
unfold Wf, WfACTS, WfSB, WfRMW, WfRF, WfMO, WfSC in *; desc; subst; splits; eauto using in_cons.
Admitted.

Lemma add_f acts sb rmw rf mo sc
    (COH: Coherent acts sb rmw rf mo sc)
    A B (NRMW: forall a b, A a /\ B b -> ~ rmw a b)
    i (TID: forall a, A a \/ B a <-> thread a = i \/ is_init a) 
    f (NINf: ~ In f acts) (LABf: lab f = Afence Orel) (TIDf: thread f = i)
    acts' (ACTS': acts' = f :: acts)
    sb' (SB': sb' = add_beween sb A B f) :
    Coherent acts' sb' rmw rf mo sc.
Proof.
red; splits; red; splits.
red; splits.

Lemma add_f acts sb rmw rf mo sc
    (COH: Coherent acts sb rmw rf mo sc)
    A B (NRMW: forall a b, A a /\ B b -> ~ rmw a b)
    i (forall a, A a \/ B a <-> thread a = i \/
    f (NINf: ~ In f acts) (LABf: lab f = Afence Orel) (
    acts' (ACTS': acts' = f :: acts)
    sb' (SB': sb' = add_beween sb A B f) :
    Coherent acts' sb' rmw rf mo sc.
Proof.


Admitted.

Lemma rel_to_rlx acts sb rmw rf mo sc
    (COH: Coherent acts sb rmw rf mo sc)
    g (TID: forall a, thread (g a) = thread a)
(AAA: forall a, g a = a \/ exists l v prev, 
        lab a = Astore l v Orel /\ lab (g a) = Astore l v Orlx /\
        immediate sb prev a /\ lab prev = Afence Orel)
    acts' (ACTS': acts' = map g acts)
    sb' (SB': sb' = mapR g sb)
    rmw' (RMW': rmw' = mapR g rmw)
    rf' (RF': rf' = mapR g rf)
    mo' (MO': mo' = mapR g mo)
    sc' (SC': sc' = mapR g sc) :
    Coherent acts' sb' rmw' rf' mo' sc'.
Proof.
Admitted. *)
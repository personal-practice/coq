(******************************************************************************)
(** * Automation for the Power memory model *)
(******************************************************************************)

Require Import Classical List Relations Peano_dec Omega.
Require Import Hahn.
Require Import Basic Power_Events Power_Model Power_Domains Power_Locations.

Set Implicit Arguments.

Tactic Notation "solve_type_mismatchP" int_or_var(index) := 
  (repeat
    autounfold with type_unfold basic_type_unfold composite_type_unfold in *);
  basic_solver index.

Tactic Notation "solve_type_mismatchP" := 
  solve_type_mismatchP 4.

Tactic Notation "prepare_wf" "as" ident(ID) :=
  match goal with | G: power_execution |- _ =>
    (match goal with | WF: Wf G |- _ => idtac end) ||
    (try match goal with | CON: PowerConsistent G |- _ =>
      assert (ID: Wf G) by by apply con_implies_wf
    end)
  end.

Tactic Notation "prepare_wf" :=
  let H := fresh in prepare_wf as H.

Ltac unfold_wf := prepare_wf;
  match goal with | G: power_execution |- _ =>
    match goal with [WF:Wf G |- _] => cdes WF;
      match goal with 
      [D:WfDEPS G, A:WfACTS G, S:WfSB G, RF:WfRF G, M:WfMO G, RM:WfRMW G |- _] => 
        cdes D; cdes A; cdes S; cdes RF; cdes M; cdes RM; clear D A S RF M RM
      end
    end
  end.

Ltac rewrite_cartesian_products :=
  repeat match goal with [DOM:_ ⊆ _ ✕ _ |- _] => apply rewrite_dom in DOM end.

Ltac simplify_domains :=
  match goal with 
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
  (* TODO set_union *)
  end.

Ltac act_solver := prepare_wf;
  match goal with | G: power_execution |- _ =>
  match goal with | WF: G.(Wf) |- _ =>
    unfolder in *; desf;
    match goal with
    | |- E _ _ => red; act_solver
    | |- In ?e _ =>
      by repeat match goal with [e':event |- _] =>
        match goal with
        | [REL:(_ G e e') |- _] => clear - WF REL;
          eapply (in_acts WF) with (a := e) (b := e'); basic_solver 42
        | [REL:(_ G e' e) |- _] => clear - WF REL;
          eapply (in_acts WF) with (a := e') (b := e); basic_solver 42
        end
      end
    end; unfold union; eauto
  end
  end.

Ltac domain_solver := prepare_wf;
  idtac + autounfold with composite_type_unfold;
  try (unfold_wf; rewrite_cartesian_products);
  idtac + unfold set_union;
  idtac + simplify_domains + (do 2 simplify_domains) + (do 3 simplify_domains);
  idtac + rewrite seqA + rewrite <- seqA;
  let apply_dom := (fun d => autorewrite with domains using apply d) in
  let apply_acts := 
    (unfolder; ins; splits; auto; repeat (eexists; splits; eauto); act_solver) 
  in
  match goal with
  | |- _ \/ _ => left + right; domain_solver
  (* equivalence *)
  | |- _ ≡ _ => red; split; [| basic_solver 42]; domain_solver
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
  (* sets *)
  | |- ⦗_⦘ ⊆ _ => 
    unfolder; ins; desf; repeat (eexists; splits; eauto); solve_type_mismatchP
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
  (* in acts *)
  | |- _ ⊆ ⦗E _⦘ ⨾ _ ⨾ ⦗E _⦘ => apply_acts
  | |- _ ⊆ ⦗E _⦘ ⨾ _ => apply_acts
  | |- _ ⊆ _ ⨾ ⦗E _⦘ => apply_acts
  end.

Ltac loc_producer := prepare_wf;
  match goal with | G: power_execution |- _ =>
    unfold psbloc, same_loc in *; unfolder in *; desf; 
    match goal with | WF:Wf G |- _ =>
      let apply_loc := (fun x y L =>
        not_proven (loc (lab G) x = loc (lab G) y);
        assert (loc (lab G) x = loc (lab G) y) by (eapply L; eauto)
      ) in
      repeat match goal with
      | [L:(restrict_location G _ _ _) |- _] => red in L; desf
      | [_:(rf G ?a ?b) |- _] => apply_loc a b rf_loc
      | [_:(mo G ?a ?b) |- _] => apply_loc a b mo_loc
      | [_:(rmw G ?a ?b) |- _] => apply_loc a b rmw_loc
      | [_:(rb G ?a ?b) |- _] => apply_loc a b rb_loc
      | [_:(eco G ?a ?b) |- _] => apply_loc a b eco_loc
      end
    end
  end.

Ltac loc_solver_base :=
  unfold same_loc in *; desf;
  (by eauto with locations || loc_producer; congruence).

Ltac type_solver := prepare_wf; first[
  solve_type_mismatchP |
  match goal with | G: power_execution |- _ =>
    idtac + unfold RW, _WF, F in *;
    unfolder in *; desf;
    match goal with
    | |- _ /\ _ => split; type_solver
    | |- _ \/ _ => (left + right); type_solver
    | |- restrict_location _ _ _ _ => red; split; [type_solver | loc_solver_base]
    | |- ~ is_init _ =>
      (unfold psbloc in *; unfolder in *; desf) ||
      (apply R_in_I; auto; type_solver) ||
      (eapply F_in_I; eauto; type_solver)
    | |- I ?a =>
      (unfold psbloc in *; unfolder in *; desf) ||
      (eapply R_in_I; eauto; type_solver) ||
      (eapply F_in_I; eauto; type_solver)
    | |- W G ?a =>
     match goal with 
      | L:(restrict_location G (W G) _ a) |- _ => red in L; desf
      | _:(data G _ a) |- _ => eapply data_domb
      | _:(rmw G _ a) |- _ => eapply rmw_domb
      | _:(rf G a _) |- _ => eapply rf_doma
      | _:(mo G a _) |- _ => eapply mo_doma
      | _:(mo G _ a) |- _ => eapply mo_domb
      | _:(rb G _ a) |- _ => eapply rb_domb
      | _:(detour G a _) |- _ => eapply detour_doma
      end
    | |- R G ?a =>
      match goal with
      | L:(restrict_location G (R G) _ a) |- _ => red in L; desf
      | _:(ctrl G a _) |- _ => eapply ctrl_doma
      | _:(ctrl_isync G a _) |- _ => eapply ctrli_doma
      | _:(data G a _) |- _ => eapply data_doma
      | _:(addr G a _) |- _ => eapply addr_doma
      | _:(deps G a _) |- _ => eapply deps_doma
      | _:(rmw G a _) |- _ => eapply rmw_doma
      | _:(rf G _ a) |- _ => eapply rf_domb
      | _:(rb G a _) |- _ => eapply rb_doma
      | _:(rdw G a _) |- _ => eapply rdw_doma
      | _:(rdw G _ a) |- _ => eapply rdw_domb
      | _:(psbloc G _ a) |- _ => eapply psbloc_domb
      | _:(detour G _ a) |- _ => eapply detour_domb
      | _:(ppo G a _) |- _ => eapply ppo_doma
      | _:(detour G _ a) |- _ => eapply detour_domb
      end
    | |- RW G ?a =>
      match goal with
      | _:(addr G _ a) |- _ => eapply addr_domb
      end
    end; eauto
  end
].

Ltac loc_solver_extended :=
  match goal with | G: power_execution |- _ =>
    match goal with
    | |- same_loc G _ _ => 
      red; split; auto; (loc_solver_base || loc_solver_extended)
    | |- loc (lab G) ?a <> None =>
      unfold same_loc in *; desf; apply RW_has_loc; type_solver
    end
  end.

Ltac loc_solver := prepare_wf; (loc_solver_extended || loc_solver_base).

Ltac same_loc_producer := prepare_wf;
  match goal with | G: power_execution |- _ =>
    let apply_same_loc := (fun x y =>
      not_proven (same_loc G x y);
      assert (same_loc G x y) by (split; loc_solver)
    ) in
    repeat match goal with
    | _:(sb G ?a ?b) |- _ => apply_same_loc a b
    end
  end.

(******************************************************************************)
(** ** Irreflexiveness *)
(******************************************************************************)
Ltac solve_irreflexive0 :=
  match goal with
  | |- irreflexive (⦗_⦘ ⨾ _ ⨾ ⦗_⦘) => 
    red; unfolder; ins; desf; type_solver
  end.

Ltac solve_irreflexive := prepare_wf; first [
  solve_irreflexive0 |
  match goal with | G: power_execution |- _ =>
    try match goal with | |- ?a <> ?b => red; ins; subst end;
    eauto with irreflexiveDb
  end
].
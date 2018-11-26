Require Import Hahn.

Set Implicit Arguments.

Lemma eqv_empty_is_empty (A: Type) : ⦗@set_empty A⦘ ≡ ∅₂.
Proof. basic_solver. Qed.

Lemma ct_begin_absorb A (r r' : relation A) :
  r ⨾ r' ⊆ r'⁺ -> r ⨾ r'⁺ ⊆ r'⁺.
Proof.
  ins; rewrite ct_begin at 1; sin_rewrite H; apply ct_rt.
Qed.  

Lemma ct_end_absorb A (r r' : relation A) :
  r ⨾ r' ⊆ r⁺ -> r⁺ ⨾ r' ⊆ r⁺.
Proof.
  by ins; rewrite ct_end at 1; rewrite seqA, H, rt_ct.
Qed. 

Lemma inclusion_seq_ct1 A (r1 r2 r: relation A) : 
  r1 ⊆ r⁺ -> r2 ⊆ r＊ -> r1 ⨾ r2 ⊆ r⁺.
Proof.
  intros -> ->; apply ct_rt.
Qed.

Lemma inclusion_seq_ct2 A (r1 r2 r: relation A) : 
  r1 ⊆ r＊ -> r2 ⊆ r⁺ -> r1 ⨾ r2 ⊆ r⁺. 
Proof.
  intros -> ->; apply rt_ct.
Qed.

Hint Resolve inclusion_seq_ct1 inclusion_seq_ct2 : rel_full.
Hint Resolve inclusion_t_r_t inclusion_r_t_t inclusion_seq_l inclusion_seq_r inclusion_t_t2 : rel_full.
Hint Resolve inclusion_rt_rt2 inclusion_seq_rt : rel_full.

Lemma path_union A (r1 r2: relation A) : 
  (r1 ∪ r2)^+ ≡ r1^+ ∪ (r1^* ;; r2 ;; r1^*)^+.
Proof.
  split; cycle 1.
    by auto 10 with rel rel_full.
  apply inclusion_t_ind_right; auto 8 with rel_full rel. 
  relsf; unionL; auto 6 with rel rel_full.
  rewrite ct_end_absorb; auto with rel.
  rewrite !seqA; rels; auto with rel.
Qed.


(******************************************************************************)
(** ** Notation *)
(******************************************************************************)
Notation "a ✕ b" := (fun x y => a x /\ b y) (at level 1, format "a ✕ b").
Notation "rel |imm" := (immediate rel) (at level 1).

(******************************************************************************)
(** ** Adjacency (new file in hahn?)  *)
(******************************************************************************)

Definition adjacent A (rel: relation A) a b :=
  << LA_ac : forall c, rel b c -> rel a c >> /\ 
  << LA_ca : forall c, rel c b -> rel^? c a >> /\
  << LA_cb : forall c, rel c a -> rel c b >> /\
  << LA_bc : forall c, rel a c -> rel^? b c >>.

Definition adjacentW A (rel: relation A) a b :=
  << LA_ac : forall c, rel b c -> rel a c >> /\ 
  << LA_cb : forall c, rel c a -> rel c b >>.

Lemma adjacent_weaken A (rel: relation A) a b : 
  adjacent rel a b -> adjacentW rel a b.
Proof. unfold adjacent, adjacentW; intuition. Qed.

Lemma immediate_adjacent A (r: relation A) (dom: A -> Prop)
  (STOT1: ⦗dom⦘ ;; r ;; r^{-1} ⊆ r^? ∪ r^{-1})
  (STOT2: r^{-1} ;; ⦗dom⦘ ;; r ⊆ r^? ∪ r^{-1})
  (T: transitive r) (IRR: irreflexive r):  
  forall a b, dom a -> immediate r a b <-> adjacent r a b /\ r a b.
Proof.
unfold adjacent; unfolder in *; ins.
split; splits; desf; ins.
1, 3: by eauto with rel.
assert (AA: dom a /\ (exists z : A, r a z /\ r c z) ) by eauto.
by specialize (STOT1 a c AA) ; desf; [auto|exfalso; eauto |econs].
assert (AA: (exists z : A, r z b /\ dom z /\ r z c) ) by eauto.
by specialize (STOT2 b c AA) ; desf; [auto|econs | exfalso; eauto].
 apply LA_bc in R1; apply LA_ca in R2; desf; eapply IRR, T; eauto.
Qed.

Lemma adjacent_uniqe1 A (r: relation A) (ACYC: acyclic r):
  forall a b c : A,  r a b ->  r a c -> adjacent r a b -> adjacent r a c -> b = c.
Proof.
ins; unfold adjacent in *; desc.
assert (r^? b c) by eauto.
assert (r^? c b) by eauto.
unfolder in *; desf.
by exfalso; eapply ACYC; eapply t_trans; econs; eauto.
Qed.

Lemma adjacent_uniqe2 A (r: relation A) (ACYC: acyclic r):
  forall a b c : A,  r b a ->  r c a -> adjacent r b a -> adjacent r c a -> b = c.
Proof.
ins; unfold adjacent in *; desc.
assert (r^? b c) by eauto.
assert (r^? c b) by eauto.
unfolder in *; desf.
by exfalso; eapply ACYC; eapply t_trans; econs; eauto.
Qed.

(******************************************************************************)
(** ** Tactics *)
(******************************************************************************)
Tactic Notation "arewrite" uconstr(EQ) "at" integer_list(indices) :=
  let H := fresh in
  assert (H : EQ); [eauto 4 with rel rel_full; try done|
                    rewrite H at indices; clear H; rewrite ?seqA].

Tactic Notation "arewrite" uconstr(EQ) "by" tactic(t) :=
  let H := fresh in
    assert (H: EQ) by (by t; eauto with rel rel_full);
    first [seq_rewrite H|sin_rewrite H]; clear H; rewrite ?seqA; try done.

Tactic Notation "arewrite" uconstr(EQ) "at" integer_list(indices) "by" tactic(t) :=
  let H := fresh in
    assert (H : EQ) by (by t; eauto with rel rel_full);
    rewrite H at indices; clear H; rewrite ?seqA; try done.

Tactic Notation "arewrite_false" constr(exp) "at" integer_list(indices) :=
  arewrite (exp ≡ fun _ _ => False) at indices; [split;[|vauto]|].

Tactic Notation "arewrite_id" constr(exp) "at" integer_list(indices) :=
  arewrite (exp ⊆ ⦗fun _ => True⦘) at indices.

Tactic Notation "clear_equivs" uconstr(EQ) "at" integer_list(indices) :=
  arewrite_id EQ at indices; simpl_rels.

Tactic Notation "clear_equivs" uconstr(EQ):=
  arewrite_id !EQ; simpl_rels.

Ltac not_proven H := 
  match goal with
  | [ _ : H |- _ ] => fail 1
  | _ => idtac
  end.

Tactic Notation "case_rt"  uconstr(x) "at" int(index) :=
  simpl_rels; rewrite rtE with (r := x) at index;
  (case_union_2 _ (x⁺) || case_union_2 ⦗fun _ => True⦘ _).
Tactic Notation "case_rt"  uconstr(x) := case_rt x at 1.

Tactic Notation "crewrite" hyp(H) :=
  try (rewrite !H || rewrite <- !H || setoid_rewrite H || setoid_rewrite <- H).

Tactic Notation "rotate" int_or_var(i) := do i (
 rewrite <- ?seqA; (apply irreflexive_seqC || apply acyclic_seqC); rewrite ?seqA
).
Tactic Notation "rotate" := rotate 1.

(******************************************************************************)
(** ** Hahn *)
(******************************************************************************)

Lemma leading_refl A (r r' e : relation A) : r ⊆ r' -> r ⊆ e^? ⨾ r'.
Proof.
  firstorder.
Qed.

(******************************************************************************)
(** ** Domains *)
(******************************************************************************)
Lemma dom_inter A (r r': relation A) (S: A -> Prop) : 
  (⦗S⦘ ⨾ r ⨾ ⦗S⦘) ∩ r' ≡ ⦗S⦘ ⨾ (r ∩ r') ⨾ ⦗S⦘.
Proof.
  basic_solver.
Qed.

Lemma dom_inter2 A (r r': relation A) (S S' : A -> Prop) : 
  ⦗S⦘ ⨾ ((⦗S'⦘ ⨾ r ⨾ ⦗S'⦘) ∩ r') ⨾ ⦗S⦘ ≡ ⦗S⦘ ⨾ ⦗S'⦘ ⨾ (r ∩ r') ⨾ ⦗S'⦘ ⨾ ⦗S⦘.
Proof.
  basic_solver 42.
Qed.

Lemma dom_imm X (r: relation X) (A : X -> Prop) :
    ⦗A⦘ ⨾ r|imm ⨾ ⦗A⦘  ⊆ (⦗A⦘⨾ r ⨾ ⦗A⦘)|imm.
Proof.
  basic_solver.
Qed.

(******************************************************************************)
(** ** Totality *)
(******************************************************************************)
Lemma total_enclose A (r: relation A) (S: A -> Prop):
  is_total S r -> is_total S (⦗S⦘ ⨾ r ⨾ ⦗S⦘).
Proof.
  unfold is_total; ins; specialize (H a IWa b IWb NEQ); desf;
  (left + right); basic_solver 42.
Qed.

(******************************************************************************)
(** ** Extras *)
(******************************************************************************)
Lemma not_none_implies_some A (o : option A) (N_NONE: o <> None) : 
  exists x, o = Some x.
Proof. destruct o; eauto; contradiction. Qed.

Lemma doma_helper2 A (r : relation A) d : doma (⦗d⦘ ⨾ r) d.
Proof. rels. Qed.

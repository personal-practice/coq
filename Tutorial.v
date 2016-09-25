(*
  Introduction
*)
Theorem my_first_proof : (forall A : Prop, A -> A).
Proof.
  intros A.
  intros proof_of_A.
  exact proof_of_A.
Qed.

(*
  Proofs with ->
*)
Theorem forward_small : (forall A B : Prop, A -> (A->B) -> B).
Proof.
  intros A.
  intros B.
  intros proof_of_A.
  intros A_implies_B.
  pose (proof_of_B := A_implies_B proof_of_A).
  exact proof_of_B.
Qed.

Theorem backward_small : (forall A B : Prop, A -> (A->B)->B).
Proof.
  intros A B.
  intros proof_of_A A_implies_B.
  refine (A_implies_B _).
    exact proof_of_A.
Qed.

Theorem backward_large : (forall A B C : Prop, A -> (A->B) -> (B->C) -> C).
Proof.
  intros A B C.
  intros proof_of_A A_implies_B B_implies_C.
  refine (B_implies_C _).
    refine (A_implies_B _).
      exact proof_of_A.
Qed.

Theorem backward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
  intros A B C.
  intros proof_of_A A_implies_B A_imp_B_imp_C.
  refine (A_imp_B_imp_C _ _).
    exact proof_of_A.

    refine (A_implies_B _).
      exact proof_of_A.
Qed.

Theorem forward_huge : (forall A B C : Prop, A -> (A->B) -> (A->B->C) -> C).
Proof.
  intros A B C.
  intros proof_of_A A_implies_B A_imp_B_imp_C.
  pose (proof_of_B := A_implies_B proof_of_A).
  pose (proof_of_C := A_imp_B_imp_C proof_of_A proof_of_B).
  exact proof_of_C.
Show Proof.
Qed.

(*
  Boolean
*)

(*Inductive False : Prop := .

Inductive True : Prop :=
  | I : True.*)

(*Inductive bool : Set :=
  | true : bool
  | false : bool.*)

Theorem True_can_be_proven : True.
  exact I.
Qed.

Definition not (A : Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

Theorem False_cannot_be_proven : ~False.
Proof.
  unfold not.
  intros proof_of_False.
  exact proof_of_False.
Qed.

Theorem False_cannot_be_proven_again : ~False.
Proof.
  intros proof_of_false.
  case proof_of_false.
Qed.

Theorem thm_true_imp_true : True -> True.
Proof.
  intros proof_of_True.
  exact I.
Qed.

Theorem thm_false_imp_true : False -> True.
Proof.
  intros proof_of_false.
  exact I.
Qed.

Theorem thm_false_imp_false : False -> False.
Proof. 
  intros proof_of_false.
  case proof_of_false.
Qed.

Theorem thm_true_imp_false : ~(True -> False).
Proof.
  intros T_imp_F.
  refine (T_imp_F _).
   exact I.
Qed.

Theorem absurd2 : forall A C : Prop, A -> ~ A -> C.
Proof.
  intros A C.
  intros proof_of_A proof_that_A_cannot_be_proven.
  unfold not in proof_that_A_cannot_be_proven.
  pose (proof_of_False := proof_that_A_cannot_be_proven proof_of_A).
  case proof_of_False.
Qed.

Require Import Bool.

Theorem true_is_True : Is_true true.
Proof.
  simpl.
  exact I.
Qed.

Theorem not_eqb_true_false : ~(Is_true (eqb true false)).
Proof.
  simpl.
  exact False_cannot_be_proven.
Qed.

Theorem eqb_a_a : (forall a : bool, Is_true (eqb a a)).
Proof.
  intros a.
  case a.
    (*Suppose a is true*)
    simpl.
    exact I.
    (*Suppose a is false*)
    simpl.
    exact I.
Qed.

Theorem thm_eqb_a_t : (forall a:bool, (Is_true (eqb a true)) -> (Is_true a)).
Proof.
  intros a.
  case a.
    (*Suppose a is true*)
    simpl.
    intros proof_of_true.
    exact I.
    (*Suppose a is false*)
    simpl.
    intros proof_of_false.
    case proof_of_false.
Qed.

(*
  AND and OR
*)
Theorem left_or : (forall A B : Prop, A -> A \/ B).
Proof.
  intros A B.
  intros proof_of_A.
  pose (proof_of_A_or_B := or_introl proof_of_A : A \/ B).
  exact proof_of_A_or_B.
Qed.

Theorem right_or : (forall A B : Prop, B -> A \/ B).
Proof.
  intros A B.
  intros proof_of_B.
  refine (or_intror _).
    exact proof_of_B.
Qed.

Theorem or_commutes : (forall A B : Prop, A \/ B -> B \/ A).
Proof.
  intros A B.
  intros A_or_B.
  case A_or_B.
    intros proof_of_A.
    refine (or_intror _).
      exact proof_of_A.

    intros proof_of_B.
    refine (or_introl _).
      exact proof_of_B.
Qed.

Theorem both_and : (forall A B : Prop, A -> B -> A /\ B).
Proof.
  intros A B.
  intros proof_of_A proof_of_B.
  refine (conj _ _).
    exact proof_of_A.

    exact proof_of_B.
Qed.

Theorem and_commutes : (forall A B, A /\ B -> B /\ A).
Proof.
  intros A B.
  intros A_and_B.
  destruct A_and_B as [ proof_of_A proof_of_B ].
  refine (conj _ _).
    exact proof_of_B.
    exact proof_of_A.
  (*case A_and_B.
    intros proof_of_A proof_of_B.
    refine (conj _ _).
      exact proof_of_B.
      
      exact proof_of_A.*)
Qed.

Theorem orb_is_or : (forall a b, Is_true (orb a b) <-> Is_true a \/ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    intros H.
    case a, b.
      (*T T*)
      simpl.
      refine (or_introl _).
        exact I.
      (*T F*)
      exact (or_introl I).
      (*F T*)
      exact (or_intror I).
      (*F F*)
      simpl in H.
      case H.
  intros H.
  case a, b.
    (*T T*)
    simpl.
    exact I.
    (*T F*)
    exact I.
    (*F T*)
    exact I.
    (*F F*)
    case H.
      (*H is (or_introl A)*)
      intros A.
      simpl in A.
      case A.
      
      (*H is (or_intror B)*)
      intros B.
      simpl in B.
      case B.
Qed.

Theorem andb_is_and : (forall a b, Is_true (andb a b) <-> Is_true a /\ Is_true b).
Proof.
  intros a b.
  unfold iff.
  refine (conj _ _).
    intros H.
    case a, b.
      (*T T*)
      simpl.
      exact (conj I I).
      (*T F*)
      simpl in H.
      case H.
      (*F T*)
      simpl in H.
      case H.
      (*F F*)
      simpl in H.
      case H.
     intros H.
     case a, b.
      (*T T*)
      simpl.
      exact I.
      (*T F*)
      simpl in H.
      destruct H as [A B].
      case B.
      (*F T*)
      simpl in H.
      destruct H as [A B].
      case A.
      (*F F*)
      simpl in H.
      destruct H as [A B].
      case A.
Qed.

(*
  Existence and Equality
*)
Definition basic_predicate := 
  (fun a => Is_true (andb a true)).

Theorem thm_exists_basics : (ex basic_predicate).
Proof.
  pose (witness := true).
  refine (ex_intro basic_predicate witness _).
    unfold basic_predicate.
    simpl.
    exact I.
Qed.

Theorem thm_exists_basics_again : (exists a, Is_true (andb a true)).
Proof. 
  pose (witness := true).
  refine (ex_intro _ witness _).
    simpl.
    exact I.
Qed.

Theorem thm_forall_exists : (forall b, (exists a, Is_true(eqb a b))).
Proof.
  intros b.
  case b.
    (*b is True*)
    pose (witness := true).
    refine (ex_intro _ witness _).
      simpl.
      exact I.
    (*b is False*)
    pose (witness := false).
    refine (ex_intro _ witness _).
      simpl.
      exact I.
Qed.

Theorem thm_forall_exists_again : (forall b, (exists a, Is_true(eqb a b))).
Proof.
  intros b.
  refine (ex_intro _ b _).
  exact (eqb_a_a b).
Qed.

Theorem forall_exists : (forall P : Set->Prop, (forall x, ~(P x)) -> ~(exists x, P x)).
Proof.
  intros P.
  intros forall_x_not_Px.
  unfold not.
  intros exists_x_Px.
  destruct exists_x_Px as [witness proof_of_Pwitness].
  pose (not_Pwitness := forall_x_not_Px witness).
  unfold not in not_Pwitness.
  pose (proof_of_False := not_Pwitness proof_of_Pwitness).
  case proof_of_False.
Qed.
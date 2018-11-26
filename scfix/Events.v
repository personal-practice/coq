(******************************************************************************)
(** * Model-independent events *)
(******************************************************************************)
Require Import Hahn.
Require Import Basic.

Set Implicit Arguments.
Remove Hints plus_n_O.

Definition act_id := nat.
Definition thread_id := nat.
Definition location := nat.
Definition value := nat.

Inductive event :=
  | Init (l: location)
  | Act (id: act_id) (i: thread_id).

Definition is_init a := 
  match a with 
  | Init _ => True
  | _ => False
  end.

Definition init_pair a b := is_init a /\ ~ is_init b.

Definition tid a :=
  match a with
  | Init _ => None
  | Act _ i => Some i
  end.

Definition same_thread := (fun x y => tid x <> None /\ tid x = tid y).
Notation "a ∙" := (a ∩ same_thread) (at level 1, format "a ∙").
Notation "a ∘" := (a \ same_thread) (at level 1, format "a ∘").

Definition I := (fun a => ~ is_init a).

Hint Unfold init_pair I : type_unfolderDb.

(******************************************************************************)
(** ** Decidable equality *)
(******************************************************************************)

Require Import Omega.

Lemma eq_dec_events :
  forall x y : event, {x = y} + {x <> y}.
Proof.
repeat decide equality.
Qed.

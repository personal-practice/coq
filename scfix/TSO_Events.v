(******************************************************************************)
(** * Events of the TSO memory model *)
(******************************************************************************)
Require Import Classical List Relations Peano_dec.
Require Import Hahn HahnMinPath.
Require Import Basic.

Set Implicit Arguments.
Remove Hints plus_n_O.

Section TSO_events.

  Definition act_id := nat.
  Definition thread_id := option nat.
  Definition location := nat.
  Definition value := nat.

  Inductive label := 
    | Aload (l: location) (v: value)
    | Astore (l: location) (v: value)
    | Armw (l: location) (vr: value) (vw: value)
    | Afence.

  Variable lab : act_id -> label.

  Definition loc a :=
    match lab a with
    | Aload l _
    | Astore l _
    | Armw l _ _ => Some l
    | _ => None
    end.

  Definition valr a :=
    match lab a with
    | Aload  _ v 
    | Armw _ v _ => Some v
    | _ => None
    end.
  
  Definition valw a :=
    match lab a with
    | Astore _ v
    | Armw _ _ v => Some v
    | _ => None
    end.

  Definition is_r a := 
    match lab a with
    | Aload  _ _ => True
    (* | Armw _ _ _  *)
    | _ => False
    end.

  Definition is_w a := 
    match lab a with
    | Astore _ _ => True
    (* | Armw _ _ _  *)
    | _ => False
    end.

  Definition is_rmw a := 
    match lab a with
    | Armw _ _ _ => True
    | _ => False
    end.
  
  Definition is_f a := 
    match lab a with
    | Afence => True
    | _ => False
    end.

  Definition is_rw a : Prop := is_r a \/ is_w a.
  Definition is_rf a : Prop := is_r a \/ is_f a.
  Definition is_wf a : Prop := is_f a \/ is_w a.

  Lemma rw_has_location a (RW: is_rw a) : exists l, loc a = Some l.
  Proof. unfold loc, is_rw, is_r, is_w, is_rmw in *. desf; eauto. Qed.

  Definition init_label l :=  (Astore l 0).
  Definition is_init a := a = 0 /\ exists l, lab a = init_label l.
  Definition init_pair a b := is_init a /\ ~ is_init b.

End TSO_events.

Hint Unfold is_r is_w is_rmw is_f is_rw is_rf is_wf is_init init_label init_pair
: type_unfolderDbT.

Tactic Notation "type_unfolderT" := 
  repeat autounfold with type_unfolderDbT in *.

Tactic Notation "solve_type_mismatchT" int_or_var(index) :=
  (idtac + type_unfolderT); basic_solver index.

Tactic Notation "solve_type_mismatchT" := 
  solve_type_mismatchT 4.
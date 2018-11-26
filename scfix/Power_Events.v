(******************************************************************************)
(** * Events of the Power memory model *)
(******************************************************************************)
Require Import Hahn.
Require Import Basic Events.
Require Export Events.

Set Implicit Arguments.
Remove Hints plus_n_O.

Inductive label := 
  | Aload (l: location) (v: value)
  | Astore (l: location) (v: value)
  | Afence_lwsync
  | Afence_sync.

Definition init_label l :=  (Astore l 0).

Section Labels.

Variable lab : event -> label.

Definition loc a :=
  match lab a with
  | Aload l _
  | Astore l _ => Some l
  | _ => None
  end.

Definition val a :=
  match lab a with
  | Aload  _ v 
  | Astore _ v => Some v
  | _ => None
  end.

Definition is_r a := 
  match lab a with
  | Aload  _ _ => True
  | _ => False
  end.

Definition is_w a := 
  match lab a with
  | Astore _ _ => True
  | _ => False
  end.

Definition is_f_sync a := 
  match lab a with
  | Afence_sync => True
  | _ => False
  end.

Definition is_f_lwsync a :=
  match lab a with
  | Afence_lwsync => True
  | _ => False
  end.

End Labels.

Lemma eq_dec_labels :
  forall x y : label, {x = y} + {x <> y}.
Proof.
repeat decide equality.
Qed.
(******************************************************************************)
(** * Events of the RC11 memory model *)
(******************************************************************************)
Require Import Hahn.
Require Import Basic Events.
Require Export Events.

Set Implicit Arguments.
Remove Hints plus_n_O.

Inductive mode := NA | RLX | REL | ACQ | ACQREL | SC.

Inductive mode_r := Rna | Rrlx | Racq | Rsc.

Inductive mode_w := Wna | Wrlx | Wrel | Wsc.

Inductive mode_rw := RWrlx | RWacq | RWrel | RWacqrel | RWsc.

Inductive mode_f := Facq | Frel | Facqrel | Fsc.

Inductive label := 
  | Aload (l:location) (v:value) (o:mode_r)
  | Astore (l:location) (v:value) (o:mode_w)
  | Armw (l:location) (vr:value) (vw:value) (o:mode_rw)
  | Afence (o:mode_f).

Definition init_label l :=  (Astore l 0 Wna).

Section Labels.

Variable lab : event -> label.

Definition loc a :=
  match lab a with
  | Aload l _ _
  | Astore l _ _
  | Armw l _ _ _ => Some l
  | _ => None
  end.

Definition valr a :=
  match lab a with
  | Aload  _ v _
  | Armw _ v _ _ => Some v
  | _ => None
  end.

Definition valw a :=
  match lab a with
  | Astore _ v _
  | Armw _ _ v _ => Some v
  | _ => None
  end.

Definition val a :=
  match lab a with
  | Aload _ v _
  | Astore _ v _ => Some v
  | _ => None
  end.

Definition modr a :=
  match lab a with
  | Aload _ _ o => Some o
  | _ => None
  end.

Definition mod a :=
  match lab a with
  | Armw _ _ _ o =>
    match o with
    | RWrlx => RLX
    | RWacq => ACQ
    | RWrel => REL
    | RWacqrel => ACQREL
    | RWsc => SC
    end
  | Aload _ _ o => 
    match o with
    | Rna => NA
    | Rrlx => RLX
    | Racq => ACQ
    | Rsc => SC
    end
  | Astore _ _ o =>
    match o with
    | Wna => NA
    | Wrlx => RLX
    | Wrel => REL
    | Wsc => SC
    end
  | Afence o =>
    match o with
    | Facq => ACQ
    | Frel => REL
    | Facqrel => ACQREL
    | Fsc => SC
    end
  end.

Definition Only_Na a := 
  match mod a with
  | NA => True
  | _ => False
  end.

Definition Rlx a := 
  match mod a with
  | NA => False
  | _ => True
  end.

Definition Rel a :=
  match mod a with
  | NA | RLX | ACQ => False
  | _ => True
  end.

Definition Acq a :=
  match mod a with
  | NA | RLX | REL => False
  | _ => True
  end.

Definition Acqrel a :=
  match mod a with
  | ACQREL | SC => True
  | _ => False
  end.

Definition Sc a :=
  match mod a with
  | SC => True
  | _ => False
  end.

Definition R a :=
  match lab a with
  | Aload  _ _ _ | Armw _ _ _ _ => True
  | _ => False
  end.

Definition W a :=
  match lab a with
  | Astore _ _ _ | Armw _ _ _ _ => True
  | _ => False
  end.

Definition F a :=
  match lab a with
  | Afence _ => True
  | _ => False
  end.

Definition RMW a :=
  match lab a with
  | Armw _ _ _ _ => True
  | _ => False
  end.

Definition RW := R ∪₁ W.
Definition FR := F ∪₁ R.
Definition FW := F ∪₁ W.

Lemma rw_has_location a (H: RW a) : exists l, loc a = Some l.
Proof.
  unfold loc, RW, R, W in *; unfolder in *; desf; eauto.
Qed.

End Labels.

Hint Unfold is_init set_union set_inter R W F RMW RW FR FW : type_unfolderDb.
Tactic Notation "type_unfolder" :=  repeat autounfold with type_unfolderDb in *.

Tactic Notation "solve_type_mismatch" int_or_var(index) := 
  type_unfolder; basic_solver index.

Tactic Notation "solve_type_mismatch" :=  solve_type_mismatch 4.

Hint Unfold set_union set_inter mod Rlx Rel Acq Acqrel Sc : mode_unfolderDb.
Tactic Notation "mode_unfolder" :=  repeat autounfold with mode_unfolderDb in *.

Tactic Notation "solve_mode_mismatch" int_or_var(index) := 
  mode_unfolder; basic_solver index.

Tactic Notation "solve_mode_mismatch" :=  solve_mode_mismatch 4.

Tactic Notation "solve_mismatch" int_or_var(index) := 
  split; [solve_type_mismatch index | solve_mode_mismatch index].

Tactic Notation "solve_mismatch" :=  solve_mismatch 4.

Lemma eq_dec_labels :
  forall x y : label, {x = y} + {x <> y}.
Proof.
repeat decide equality.
Qed.
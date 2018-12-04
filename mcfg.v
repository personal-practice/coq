Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
(* Require Import Coq.Strings.String. *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Export ExtLib.Structures.Monads.
Import MonadNotation.

Require Import Coq.Program.Basics.

From QuickChick Require Import QuickChick Tactics Instances.
Import QcNotation.
Import QcDefaultNotation. Open Scope qc_scope.

Require Import Equalities.

Set Bullet Behavior "Strict Subproofs".

Inductive symbol := a | b | c.
Instance symbol_dec (x y : symbol) : Dec (x = y).
Proof. dec_eq. Defined.
Derive Show for symbol.

Definition word := list symbol.
Instance word_dec (x y : word) : Dec (x = y).
Proof. dec_eq. Defined.

Definition example_dyck : word := [a;b;c;a;b;c;a;a;b;b;c;c].
Definition example_dyck2 : word := [a;a;b;c;a;b;c;a;a;b;b;c;c;b;c].

Definition count (s: symbol) (w : word) : nat :=
  count_occ (fun x y => dec_if_dec_eq x y (symbol_dec x y)) w s.

Compute (count a example_dyck).

Fixpoint proper_prefixes' (a b c : nat) (w : word) : bool :=
  if (a <? b) || (b <? c) then
    false
  else
    match w with
    | [] => true
    | s :: w' => 
        match s with
        | a => proper_prefixes' (a + 1) b c w'
        | b => proper_prefixes' a (b + 1) c w' 
        | c => proper_prefixes' a b (c + 1) w' 
        end
    end.

Definition proper_prefixes : word -> bool := proper_prefixes' 0 0 0.

Definition dyck (w : word) : Prop :=
  (count a w = count b w) /\
  (count b w = count c w) /\
  (proper_prefixes w = true).
 
Definition dyckb (w : word) : bool :=
  (count a w =? count b w) &&
  (count b w =? count c w) &&
  (eqb (proper_prefixes w) true).

Example test_isdyck :
  dyck example_dyck.
Proof. firstorder. Qed.

Example test_isdyck2 :
  dyckb example_dyck = true.
Proof. firstorder. Qed.

Derive (Show, GenSized, Shrink, Arbitrary) for symbol.

Definition insert (i : nat) (s : symbol) (w : word) : word :=
  firstn i w ++ [s] ++ skipn i w.
(* Compute (insert 1 c [a; a; a; b; c; b; c]). *)

Fixpoint genDyckSized (size : nat) : G word :=
  match size with
  (* step: non-deterministically insert abc-triplet *)
  | (S (S (S size'))) =>
    w <- genDyckSized size';;
    (* insert 'a' *)
    ai <- choose (0, length w) ;;
    wa <- ret (insert ai a w) ;;
    (* insert 'b' *)
    bi <- choose (ai + 1, length w + 1) ;;
    wab <- ret (insert bi b wa) ;;
    (* insert 'c' *)
    ci <- choose (bi + 1, length w + 2) ;;
    wabc <- ret (insert ci c wab) ;;
    ret wabc
  (* base: empty Dyck word *)
  | _ => ret [a; b; c]
  end.

Instance genDyck : Gen word :=
  { arbitrary := sized genDyckSized }.

Definition genDyckWord : G word := @arbitrary word genDyck.

Sample genDyckWord.

Definition index : Type := nat.

Definition indexed_word : Type := list (index * symbol).

Definition Match : Type := index * index * index.

Definition Policy : Type := word -> list Match.

Fixpoint cmp'
  (s_a : list index) (s_ab : list (index * index)) (w : indexed_word) : list Match :=
  match w with
  | [] => []
  | (i,x) :: rest =>
    match x with
    | a => cmp' (s_a ++ [i]) s_ab rest
    | b => let ai := last s_a 0
           in  cmp' (removelast s_a) (s_ab ++ [(ai, i)]) rest
    | c => let (ai, bi) := last s_ab (0, 0) 
           in  (ai, bi, i) :: cmp' s_a (removelast s_ab) rest
    end
  end.
  
Fixpoint indexWord (i : nat) (w : word) : indexed_word :=
  match w with
  | []    => []
  | x::xs => (i, x) :: indexWord (S i) xs
  end.

Definition cmp : Policy := compose (cmp' [] []) (indexWord 0).
(* Compute (example_dyck, cmp example_dyck).
Compute (example_dyck2, cmp example_dyck2). *)

Definition getIndices' (m : Match) : list index :=
  match m with
  (x, y, z) => [x; y; z]
  end.

Definition getIndices (m : list Match) : list index :=
  concat (map getIndices' m).

Fixpoint splitWord' (ass bs cs : nat) (acc dw : word) : list word :=
  match dw with
  | (x::dw') =>
    match x with
    | a => splitWord' (ass + 1) bs cs (acc ++ [a]) dw'
    | b => splitWord' ass (bs + 1) cs (acc ++ [b]) dw'
    | c => 
      let cs'  := cs + 1 in
      let acc' := acc ++ [c] in
      if (ass =? bs) && (bs =? cs') then
        acc' :: splitWord' 0 0 0 [] dw'
      else
        splitWord' ass bs cs' acc' dw'
    end
  | [] => []
  end.

Definition splitWord : word -> list word := splitWord' 0 0 0 [].
(* Compute (splitWord [a;b;c;a;b;c;a;a;b;b;c;c;a;b;c]). *)

Instance shrinkDyck : Shrink word :=
  { shrink := splitWord }.

Definition spec (w w' : word) :=
  dyckb (w ++ w') && dyckb (w' ++ insert 0 c w).
(* QuickChick spec. *)

Definition should_fail (w : word) :=
  dyckb w && (59 <=? length w) ==> dyckb (w ++ [a;b] ++ w).
(* Extract Constant defNumTests => "10000".
Extract Constant defNumDiscards => "(2 * defNumTests)".
Extract Constant defNumShrinks => "1000".
Extract Constant defSize => "60".
QuickChick should_fail. *)

Definition rev_word (w : word) : word :=
  map (fun s => match s with a => c | b => b | c => a end) (rev w).
(* Compute (rev_word example_dyck). *)

Definition reverse_preserves_dyck (w : word) :=
  dyckb w ==> dyckb (rev_word w).
(* QuickChick reverse_preserves_dyck. *)

Definition cmp_preserves_indices (w : word) :=
  dyckb w ==> (length (getIndices (cmp w)) =? length w).
(* QuickChick cmp_preserves_indices. *)

Definition Range : Type := index * index.
Definition RangeMatch : Type := Range * Range * Range.

Definition singularRange (i: index) : Range := (i, i).


Definition range_lt (r1 r2 : Range) : bool :=
  match r1, r2 with
  | (x, _), (y, _) => x <? y
  end.
  
Definition rangem_lt (r1 r2 : RangeMatch) : bool :=
match r1, r2 with
| (x, _, _), (y, _, _) => range_lt x y
end.

Require Import List.
Require Import Arith.
Require Import Sorted.
Require Import Recdef.
Function bubble (l : list Range) {measure length} : list Range :=
  match l with
  | [] => []
  | [n] => [n]
  | n1 :: n2 :: l' =>
    if range_lt n1 n2 then
      n1 :: (bubble (n2 :: l'))
    else n2 :: (bubble (n1 :: l'))
  end.
Proof.
  auto. auto.
Defined.
Function bubble_sort (l : list Range) : list Range :=
  match l with
  | [] => []
  | n :: l' => bubble (n :: (bubble_sort l'))
  end.
(* Compute (bubble_sort [(0,0); (9,10); (7,8)]). *)

Definition getRangeMatch (rs : list Range) : option RangeMatch :=
  match rs with
  | [x; y; z] => Some (x, y, z)
  | _         => None
  end.
  
Function collapse' (cont : nat) (rs : list Range) {measure length rs} : list Range :=
  if cont =? 3 then
    rs
  else match rs with
  | [] => []
  | [x] => [x]
  | (x1,x2) :: (y1,y2) :: rs' =>
    if (x2 + 1) =? y1 then
      collapse' (cont + 1) ((x1, y2) :: rs')
    else
      (x1, x2) :: collapse' cont ((y1, y2) :: rs')
  end.
Proof.
all: unfold length; auto.
Defined.
(* Compute (collapse' 0 [(0,3); (4,10); (17,18)]). *)

Definition collapse (r1 r2 : RangeMatch) : option RangeMatch :=
  match r1 with | ((x, x'), (y, y'), (z, z')) =>
  match r2 with | ((k, k'), (l, l'), (m, m')) =>
    getRangeMatch
      (collapse' 0
        (bubble_sort [(x,x'); (y, y'); (z, z'); (k, k'); (l, l'); (m, m')]))
  end
  end.
(* Compute (collapse ((10,11), (15,17), (18,20)) ((12,13), (14,15), (30,40))). *)

Definition collapsible (r1 r2 : RangeMatch) : bool :=
  match collapse r1 r2 with
  | Some _ => true
  | None   => false
  end.

Definition mkRangeMatch (m : Match) : RangeMatch := 
  match m with
  | (i, j, k) => ((i, i), (j, j), (k, k))
  end.

Definition rangify : list Match -> list RangeMatch := map mkRangeMatch.


Require Import Coq.Init.Nat.
Definition test (w : word) :=
  let ranges := rangify (cmp w) in
  let rangePairs := filter (uncurry rangem_lt) (list_prod ranges ranges) in
  let existN := fun n f l => n <=? length (filter f l) in
  (dyckb w) && (30 <? length w)
    ==> existN (length w / 3) (uncurry collapsible) rangePairs.
(*     ==> existsb (uncurry collapsible) rangePairs. *)
Extract Constant defNumTests => "100000".
Extract Constant defNumDiscards => "(2 * defNumTests)".
Extract Constant defNumShrinks => "10000".
Extract Constant defSize => "50".
QuickChick test.

(*******************
** Typeclasses

(* Must be inductive *)
(* Derive ArbitrarySizedSuchThat for dyck.  *)

Definition genWordSized := @genListSized symbol GenSizedsymbol.

Definition wordGen (n : nat) : G word := @arbitrarySized word genWordSized n.
(* Sample (wordGen 10). *)

(* Definition dyckGen : G (option word) := suchThatMaybe (wordGen 261) dyckb. *)

(* Definition wordProp (g : nat -> G word) n :=
  forAll (g n) (fun t => @collect (length t) true).
QuickChick (wordProp wordGen 5). *)
*)

(*******************
** Alternative designs

0. Boolean
Definition is_dyck (w : string): bool :=
  (count "a" w =? count "b" w) &&
  (count "b" w =? count "c" w) &&
  (proper_prefixes 0 0 0 w).

Definition IsDyck (w : string) : Prop := is_dyck w = true.

Example test_isdyck :
  IsDyck "abcabcaabbcc".
Proof. reflexivity. Qed.

1. Proposition
Definition IsDyck_Prop (w : string): Prop :=
  (count "a" w = count "b" w) /\
  (count "b" w = count "c" w) /\
  (proper_prefixes 0 0 0 w).

2. Inductive Propoposition
Inductive is_Dyck : string -> Prop :=
  | Empty : is_Dyck ""
  | Insert : forall w', is_Dyck w' -> is_Dyck (String "a" w').

Example prove_dyck : is_Dyck "aaaa".
Proof. repeat constructor. Qed.

Inductive Dyck : string -> string -> string -> Prop :=
| Base : Dyck "a" "b" "c"
| Step : forall x y z l m n u v w,
            Dyck x y z
         -> Dyck l m n
         -> Interleave x y z l m n u v w (* TODO *)
         -> Dyck u v w.

Example test_Dyck :
  Dyck "aa" "bb" "cc".
Proof.
  apply (Step "a" "b" "c" "a" "b" "c"); constructor.
Qed.

Inductive Dyck : (string*string*string) -> Prop :=
| Base : Dyck ("a"%string, "b"%string, "c"%string)
| Step : forall x y z l m n, Dyck (x, y, z)
                          -> Dyck (l, m, n)
                          -> Dyck ((x ++ l)%string, (y ++ m)%string, (z ++ n)%string).

(forall w', is_true (prefix w' w)
         -> (count "a" w' >= count "b" w' >= count "c" w'))


(* Definition ValidSplit (x y z l m n k q r : word) : Prop :=
  ~ (k = []) /\ ~ (q = []) /\ ~ (r = []) /\
  True
  .

Infix "+++" := app (right associativity, at level 60) : list_scope.
*)

(* Inductive Dyck : word -> word -> word -> Prop :=
| Base : Dyck [a] [b] [c]
| Step : forall x y z l m n k q r,
           Dyck x y z
           -> Dyck l m n
           -> ValidSplit x y z l m n k q r
           -> Dyck k q r.
*) 
 
(* Inductive Dyck : word -> word -> word -> Prop :=
| Base : Dyck [a] [b] [c]
| Step : forall x y z l m n,
           Dyck x y z
           -> Dyck l m n
           -> Dyck (x +++ l) (y +++ m) (z +++ n).

Instance Dyck_deq (x y z : word) : Dec (Dyck x y z).
Proof.
Admitted.

Conjecture dyckTest : forall x y z, dyck (x +++ y +++ z) -> dyck ((a::x) +++ (b::y) +++ (c::z)).

QuickChick dyckTest.

Theorem sound (x y z : word) : Dyck x y z -> dyck (x ++ y ++ z).
Proof.
  intro DW.
  induction DW; firstorder.
  - admit.
  - admit.
  - admit.
Admitted. *)

(*
Fixpoint insertAt {A} (i : nat) (x : A) (xs : list A) : list A :=
  match i with
  | O => x :: xs
  | S i' =>
    match xs with
    | [] => []
    | x' :: xs' => x' :: insertAt i' x xs'
    end
  end.

Fixpoint genDyckWord (sz : nat) : G word :=
  let base := [a; b; c]
  in match sz with
  | O => ret base
  | S sz' =>
    freq [ (1, ret base) ;
           (sz, xs <- genDyckWord sz';; 
                ai <- choose (0, length xs);;
                bi <- choose (ai + 1, length xs + 1);;
                ci <- choose (bi + 1, length xs + 2);;
                ret (insertAt ci c (insertAt bi b (insertAt ai a xs))))  ]
  end.

Sample (genDyckWord 10).
*)

********************)
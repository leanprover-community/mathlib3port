/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro

! This file was ported from Lean 3 source module data.list.defs
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Basic
import Mathbin.Tactic.Cache
import Mathbin.Data.Rbmap.Basic
import Mathbin.Data.Rbtree.DefaultLt

/-!
## Definitions on lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains various definitions on lists. It does not contain
proofs about these definitions, those are contained in other files in `data/list`
-/


namespace List

open Function Nat

universe u v w x

variable {α β γ δ ε ζ : Type _}

instance [DecidableEq α] : SDiff (List α) :=
  ⟨List.diff⟩

#print List.splitAt /-
/-- Split a list at an index.

     split_at 2 [a, b, c] = ([a, b], [c]) -/
def splitAt : ℕ → List α → List α × List α
  | 0, a => ([], a)
  | succ n, [] => ([], [])
  | succ n, x :: xs =>
    let (l, r) := split_at n xs
    (x :: l, r)
#align list.split_at List.splitAt
-/

/-- An auxiliary function for `split_on_p`. -/
def splitOnPAux {α : Type u} (P : α → Prop) [DecidablePred P] :
    List α → (List α → List α) → List (List α)
  | [], f => [f []]
  | h :: t, f => if P h then f [] :: split_on_p_aux t id else split_on_p_aux t fun l => f (h :: l)
#align list.split_on_p_aux List.splitOnPAux

/- warning: list.split_on_p -> List.splitOnP is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (P : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α P], (List.{u1} α) -> (List.{u1} (List.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, (α -> Bool) -> (List.{u1} α) -> (List.{u1} (List.{u1} α))
Case conversion may be inaccurate. Consider using '#align list.split_on_p List.splitOnPₓ'. -/
/-- Split a list at every element satisfying a predicate. -/
def splitOnP {α : Type u} (P : α → Prop) [DecidablePred P] (l : List α) : List (List α) :=
  splitOnPAux P l id
#align list.split_on_p List.splitOnP

/- warning: list.split_on -> List.splitOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], α -> (List.{u1} α) -> (List.{u1} (List.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BEq.{u1} α], α -> (List.{u1} α) -> (List.{u1} (List.{u1} α))
Case conversion may be inaccurate. Consider using '#align list.split_on List.splitOnₓ'. -/
/-- Split a list at every occurrence of an element.

    [1,1,2,3,2,4,4].split_on 2 = [[1,1],[3],[4,4]] -/
def splitOn {α : Type u} [DecidableEq α] (a : α) (as : List α) : List (List α) :=
  as.splitOnP (· = a)
#align list.split_on List.splitOn

#print List.concat /-
/-- Concatenate an element at the end of a list.

     concat [a, b] c = [a, b, c] -/
@[simp]
def concat : List α → α → List α
  | [], a => [a]
  | b :: l, a => b :: concat l a
#align list.concat List.concat
-/

#print List.head? /-
/-- `head' xs` returns the first element of `xs` if `xs` is non-empty;
it returns `none` otherwise -/
@[simp]
def head? : List α → Option α
  | [] => none
  | a :: l => some a
#align list.head' List.head?
-/

/- warning: list.to_array -> List.toArray is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (l : List.{u1} α), Array'.{u1} (List.length.{u1} α l) α
but is expected to have type
  forall {α : Type.{u1}}, (List.{u1} α) -> (Array.{u1} α)
Case conversion may be inaccurate. Consider using '#align list.to_array List.toArrayₓ'. -/
/-- Convert a list into an array (whose length is the length of `l`). -/
def toArray (l : List α) : Array' l.length α where data v := l.nthLe v.1 v.2
#align list.to_array List.toArray

/- warning: list.nthd -> List.getD is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, α -> (List.{u1} α) -> Nat -> α
but is expected to have type
  forall {α : Type.{u1}}, (List.{u1} α) -> Nat -> α -> α
Case conversion may be inaccurate. Consider using '#align list.nthd List.getDₓ'. -/
/-- "default" `nth` function: returns `d` instead of `none` in the case
  that the index is out of bounds. -/
def getD (d : α) : ∀ (l : List α) (n : ℕ), α
  | [], _ => d
  | x :: xs, 0 => x
  | x :: xs, n + 1 => nthd xs n
#align list.nthd List.getD

#print List.getI /-
/-- "inhabited" `nth` function: returns `default` instead of `none` in the case
  that the index is out of bounds. -/
def getI [h : Inhabited α] (l : List α) (n : Nat) : α :=
  getD default l n
#align list.inth List.getI
-/

#print List.modifyNthTail /-
/-- Apply a function to the nth tail of `l`. Returns the input without
  using `f` if the index is larger than the length of the list.

     modify_nth_tail f 2 [a, b, c] = [a, b] ++ f [c] -/
@[simp]
def modifyNthTail (f : List α → List α) : ℕ → List α → List α
  | 0, l => f l
  | n + 1, [] => []
  | n + 1, a :: l => a :: modify_nth_tail n l
#align list.modify_nth_tail List.modifyNthTail
-/

#print List.modifyHead /-
/-- Apply `f` to the head of the list, if it exists. -/
@[simp]
def modifyHead (f : α → α) : List α → List α
  | [] => []
  | a :: l => f a :: l
#align list.modify_head List.modifyHead
-/

#print List.modifyNth /-
/-- Apply `f` to the nth element of the list, if it exists. -/
def modifyNth (f : α → α) : ℕ → List α → List α :=
  modifyNthTail (modifyHead f)
#align list.modify_nth List.modifyNth
-/

#print List.modifyLast /-
/-- Apply `f` to the last element of `l`, if it exists. -/
@[simp]
def modifyLast (f : α → α) : List α → List α
  | [] => []
  | [x] => [f x]
  | x :: xs => x :: modify_last xs
#align list.modify_last List.modifyLast
-/

#print List.insertNth /-
/-- `insert_nth n a l` inserts `a` into the list `l` after the first `n` elements of `l`
 `insert_nth 2 1 [1, 2, 3, 4] = [1, 2, 1, 3, 4]`-/
def insertNth (n : ℕ) (a : α) : List α → List α :=
  modifyNthTail (List.cons a) n
#align list.insert_nth List.insertNth
-/

section Take'

variable [Inhabited α]

#print List.takeI /-
/-- Take `n` elements from a list `l`. If `l` has less than `n` elements, append `n - length l`
elements `default`. -/
def takeI : ∀ n, List α → List α
  | 0, l => []
  | n + 1, l => l.head :: take' n l.tail
#align list.take' List.takeI
-/

end Take'

/- warning: list.take_while -> List.takeWhile is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], (List.{u1} α) -> (List.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, (α -> Bool) -> (List.{u1} α) -> (List.{u1} α)
Case conversion may be inaccurate. Consider using '#align list.take_while List.takeWhileₓ'. -/
/-- Get the longest initial segment of the list whose members all satisfy `p`.

     take_while (λ x, x < 3) [0, 2, 5, 1] = [0, 2] -/
def takeWhile (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | a :: l => if p a then a :: take_while l else []
#align list.take_while List.takeWhile

#print List.scanl /-
/-- Fold a function `f` over the list from the left, returning the list
  of partial results.

     scanl (+) 0 [1, 2, 3] = [0, 1, 3, 6] -/
def scanl (f : α → β → α) : α → List β → List α
  | a, [] => [a]
  | a, b :: l => a :: scanl (f a b) l
#align list.scanl List.scanl
-/

/-- Auxiliary definition used to define `scanr`. If `scanr_aux f b l = (b', l')`
then `scanr f b l = b' :: l'` -/
def scanrAux (f : α → β → β) (b : β) : List α → β × List β
  | [] => (b, [])
  | a :: l =>
    let (b', l') := scanr_aux l
    (f a b', b' :: l')
#align list.scanr_aux List.scanrAux

#print List.scanr /-
/-- Fold a function `f` over the list from the right, returning the list
  of partial results.

     scanr (+) 0 [1, 2, 3] = [6, 5, 3, 0] -/
def scanr (f : α → β → β) (b : β) (l : List α) : List β :=
  let (b', l') := scanrAux f b l
  b' :: l'
#align list.scanr List.scanr
-/

#print List.prod /-
/-- Product of a list.

     prod [a, b, c] = ((1 * a) * b) * c -/
def prod [Mul α] [One α] : List α → α :=
  foldl (· * ·) 1
#align list.prod List.prod
-/

#print List.sum /-
-- Later this will be tagged with `to_additive`, but this can't be done yet because of import
-- dependencies.
/-- Sum of a list.

     sum [a, b, c] = ((0 + a) + b) + c -/
def sum [Add α] [Zero α] : List α → α :=
  foldl (· + ·) 0
#align list.sum List.sum
-/

#print List.alternatingSum /-
/-- The alternating sum of a list. -/
def alternatingSum {G : Type _} [Zero G] [Add G] [Neg G] : List G → G
  | [] => 0
  | g :: [] => g
  | g :: h :: t => g + -h + alternating_sum t
#align list.alternating_sum List.alternatingSum
-/

#print List.alternatingProd /-
/-- The alternating product of a list. -/
def alternatingProd {G : Type _} [One G] [Mul G] [Inv G] : List G → G
  | [] => 1
  | g :: [] => g
  | g :: h :: t => g * h⁻¹ * alternating_prod t
#align list.alternating_prod List.alternatingProd
-/

#print List.partitionMap /-
/-- Given a function `f : α → β ⊕ γ`, `partition_map f l` maps the list by `f`
  whilst partitioning the result it into a pair of lists, `list β × list γ`,
  partitioning the `sum.inl _` into the left list, and the `sum.inr _` into the right list.
  `partition_map (id : ℕ ⊕ ℕ → ℕ ⊕ ℕ) [inl 0, inr 1, inl 2] = ([0,2], [1])`    -/
def partitionMap (f : α → Sum β γ) : List α → List β × List γ
  | [] => ([], [])
  | x :: xs =>
    match f x with
    | Sum.inr r => Prod.map id (cons r) <| partition_map xs
    | Sum.inl l => Prod.map (cons l) id <| partition_map xs
#align list.partition_map List.partitionMap
-/

/- warning: list.find -> List.find? is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], (List.{u1} α) -> (Option.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, (α -> Bool) -> (List.{u1} α) -> (Option.{u1} α)
Case conversion may be inaccurate. Consider using '#align list.find List.find?ₓ'. -/
/-- `find p l` is the first element of `l` satisfying `p`, or `none` if no such
  element exists. -/
def find? (p : α → Prop) [DecidablePred p] : List α → Option α
  | [] => none
  | a :: l => if p a then some a else find l
#align list.find List.find?

#print List.findM /-
/-- `mfind tac l` returns the first element of `l` on which `tac` succeeds, and
fails otherwise. -/
def findM {α} {m : Type u → Type v} [Monad m] [Alternative m] (tac : α → m PUnit) : List α → m α :=
  List.firstM fun a => tac a $> a
#align list.mfind List.findM
-/

#print List.findM?' /-
/-- `mbfind' p l` returns the first element `a` of `l` for which `p a` returns
true. `mbfind'` short-circuits, so `p` is not necessarily run on every `a` in
`l`. This is a monadic version of `list.find`. -/
def findM?' {m : Type u → Type v} [Monad m] {α : Type u} (p : α → m (ULift Bool)) :
    List α → m (Option α)
  | [] => pure none
  | x :: xs => do
    let ⟨px⟩ ← p x
    if px then pure (some x) else mbfind' xs
#align list.mbfind' List.findM?'
-/

section

variable {m : Type → Type v} [Monad m]

#print List.findM? /-
/-- A variant of `mbfind'` with more restrictive universe levels. -/
def findM? {α} (p : α → m Bool) (xs : List α) : m (Option α) :=
  xs.mbfind' (Functor.map ULift.up ∘ p)
#align list.mbfind List.findM?
-/

/- warning: list.many -> List.anyM is a dubious translation:
lean 3 declaration is
  forall {m : Type -> Type.{u2}} [_inst_1 : Monad.{0, u2} m] {α : Type.{u1}}, (α -> (m Bool)) -> (List.{u1} α) -> (m Bool)
but is expected to have type
  forall {m : Type -> Type.{u1}} [_inst_1 : Monad.{0, u1} m] {α : Type.{u2}}, (α -> (m Bool)) -> (List.{u2} α) -> (m Bool)
Case conversion may be inaccurate. Consider using '#align list.many List.anyMₓ'. -/
-- Implementing this via `mbfind` would give us less universe polymorphism.
/-- `many p as` returns true iff `p` returns true for any element of `l`.
`many` short-circuits, so if `p` returns true for any element of `l`, later
elements are not checked. This is a monadic version of `list.any`. -/
def anyM {α : Type u} (p : α → m Bool) : List α → m Bool
  | [] => pure False
  | x :: xs => do
    let px ← p x
    if px then pure tt else many xs
#align list.many List.anyM

/- warning: list.mall -> List.allM is a dubious translation:
lean 3 declaration is
  forall {m : Type -> Type.{u2}} [_inst_1 : Monad.{0, u2} m] {α : Type.{u1}}, (α -> (m Bool)) -> (List.{u1} α) -> (m Bool)
but is expected to have type
  forall {m : Type -> Type.{u1}} [_inst_1 : Monad.{0, u1} m] {α : Type.{u2}}, (α -> (m Bool)) -> (List.{u2} α) -> (m Bool)
Case conversion may be inaccurate. Consider using '#align list.mall List.allMₓ'. -/
/-- `mall p as` returns true iff `p` returns true for all elements of `l`.
`mall` short-circuits, so if `p` returns false for any element of `l`, later
elements are not checked. This is a monadic version of `list.all`. -/
def allM {α : Type u} (p : α → m Bool) (as : List α) : m Bool :=
  not <$> anyM (fun a => not <$> p a) as
#align list.mall List.allM

#print List.orM /-
/-- `mbor xs` runs the actions in `xs`, returning true if any of them returns
true. `mbor` short-circuits, so if an action returns true, later actions are
not run. This is a monadic version of `list.bor`. -/
def orM : List (m Bool) → m Bool :=
  anyM id
#align list.mbor List.orM
-/

#print List.andM /-
/-- `mband xs` runs the actions in `xs`, returning true if all of them return
true. `mband` short-circuits, so if an action returns false, later actions are
not run. This is a monadic version of `list.band`. -/
def andM : List (m Bool) → m Bool :=
  allM id
#align list.mband List.andM
-/

end

/-- Auxiliary definition for `foldl_with_index`. -/
def foldlWithIndexAux (f : ℕ → α → β → α) : ℕ → α → List β → α
  | _, a, [] => a
  | i, a, b :: l => foldl_with_index_aux (i + 1) (f i a b) l
#align list.foldl_with_index_aux List.foldlWithIndexAux

/- warning: list.foldl_with_index -> List.foldlIdx is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β -> α) -> α -> (List.{u2} β) -> α
but is expected to have type
  forall {α : Sort.{u1}} {β : Type.{u2}}, (Nat -> α -> β -> α) -> α -> (List.{u2} β) -> (optParam.{1} Nat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> α
Case conversion may be inaccurate. Consider using '#align list.foldl_with_index List.foldlIdxₓ'. -/
/-- Fold a list from left to right as with `foldl`, but the combining function
also receives each element's index. -/
def foldlIdx (f : ℕ → α → β → α) (a : α) (l : List β) : α :=
  foldlWithIndexAux f 0 a l
#align list.foldl_with_index List.foldlIdx

/-- Auxiliary definition for `foldr_with_index`. -/
def foldrWithIndexAux (f : ℕ → α → β → β) : ℕ → β → List α → β
  | _, b, [] => b
  | i, b, a :: l => f i a (foldr_with_index_aux (i + 1) b l)
#align list.foldr_with_index_aux List.foldrWithIndexAux

/- warning: list.foldr_with_index -> List.foldrIdx is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> β -> β) -> β -> (List.{u1} α) -> β
but is expected to have type
  forall {α : Type.{u1}} {β : Sort.{u2}}, (Nat -> α -> β -> β) -> β -> (List.{u1} α) -> (optParam.{1} Nat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> β
Case conversion may be inaccurate. Consider using '#align list.foldr_with_index List.foldrIdxₓ'. -/
/-- Fold a list from right to left as with `foldr`, but the combining function
also receives each element's index. -/
def foldrIdx (f : ℕ → α → β → β) (b : β) (l : List α) : β :=
  foldrWithIndexAux f 0 b l
#align list.foldr_with_index List.foldrIdx

/- warning: list.find_indexes -> List.findIdxs is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], (List.{u1} α) -> (List.{0} Nat)
but is expected to have type
  forall {α : Type.{u1}}, (α -> Bool) -> (List.{u1} α) -> (List.{0} Nat)
Case conversion may be inaccurate. Consider using '#align list.find_indexes List.findIdxsₓ'. -/
/-- `find_indexes p l` is the list of indexes of elements of `l` that satisfy `p`. -/
def findIdxs (p : α → Prop) [DecidablePred p] (l : List α) : List Nat :=
  foldrIdx (fun i a is => if p a then i :: is else is) [] l
#align list.find_indexes List.findIdxs

/- warning: list.indexes_values -> List.indexesValues is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], (List.{u1} α) -> (List.{u1} (Prod.{0, u1} Nat α))
but is expected to have type
  forall {α : Type.{u1}}, (α -> Bool) -> (List.{u1} α) -> (List.{u1} (Prod.{0, u1} Nat α))
Case conversion may be inaccurate. Consider using '#align list.indexes_values List.indexesValuesₓ'. -/
/-- Returns the elements of `l` that satisfy `p` together with their indexes in
`l`. The returned list is ordered by index. -/
def indexesValues (p : α → Prop) [DecidablePred p] (l : List α) : List (ℕ × α) :=
  foldrIdx (fun i a l => if p a then (i, a) :: l else l) [] l
#align list.indexes_values List.indexesValues

/- warning: list.indexes_of -> List.indexesOf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], α -> (List.{u1} α) -> (List.{0} Nat)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BEq.{u1} α], α -> (List.{u1} α) -> (List.{0} Nat)
Case conversion may be inaccurate. Consider using '#align list.indexes_of List.indexesOfₓ'. -/
/-- `indexes_of a l` is the list of all indexes of `a` in `l`. For example:
```
indexes_of a [a, b, a, a] = [0, 2, 3]
```
-/
def indexesOf [DecidableEq α] (a : α) : List α → List Nat :=
  findIdxs (Eq a)
#align list.indexes_of List.indexesOf

section MfoldWithIndex

variable {m : Type v → Type w} [Monad m]

#print List.foldlIdxM /-
/-- Monadic variant of `foldl_with_index`. -/
def foldlIdxM {α β} (f : ℕ → β → α → m β) (b : β) (as : List α) : m β :=
  as.foldlWithIndex
    (fun i ma b => do
      let a ← ma
      f i a b)
    (pure b)
#align list.mfoldl_with_index List.foldlIdxM
-/

#print List.foldrIdxM /-
/-- Monadic variant of `foldr_with_index`. -/
def foldrIdxM {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) : m β :=
  as.foldrWithIndex
    (fun i a mb => do
      let b ← mb
      f i a b)
    (pure b)
#align list.mfoldr_with_index List.foldrIdxM
-/

end MfoldWithIndex

section MmapWithIndex

variable {m : Type v → Type w} [Applicative m]

/- warning: list.mmap_with_index_aux -> List.mmapWithIndexAux is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}}, (Nat -> α -> (m β)) -> Nat -> (List.{u3} α) -> (m (List.{u1} β))
but is expected to have type
  forall {m : Type.{u2} -> Type.{u3}} [_inst_1 : Applicative.{u2, u3} m] {α : Type.{u1}} {β : Type.{u2}}, (Nat -> α -> (m β)) -> Nat -> (List.{u1} α) -> (m (List.{u2} β))
Case conversion may be inaccurate. Consider using '#align list.mmap_with_index_aux List.mmapWithIndexAuxₓ'. -/
/-- Auxiliary definition for `mmap_with_index`. -/
def mmapWithIndexAux {α β} (f : ℕ → α → m β) : ℕ → List α → m (List β)
  | _, [] => pure []
  | i, a :: as => List.cons <$> f i a <*> mmap_with_index_aux (i + 1) as
#align list.mmap_with_index_aux List.mmapWithIndexAux

/- warning: list.mmap_with_index -> List.mapIdxM is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} m] {α : Type.{u3}} {β : Type.{u1}}, (Nat -> α -> (m β)) -> (List.{u3} α) -> (m (List.{u1} β))
but is expected to have type
  forall {m : Type.{u3}} {_inst_1 : Type.{u1}} {α : Type.{u1} -> Type.{u2}} [β : Monad.{u1, u2} α], (List.{u3} m) -> (Nat -> m -> (α _inst_1)) -> (α (List.{u1} _inst_1))
Case conversion may be inaccurate. Consider using '#align list.mmap_with_index List.mapIdxMₓ'. -/
/-- Applicative variant of `map_with_index`. -/
def mapIdxM {α β} (f : ℕ → α → m β) (as : List α) : m (List β) :=
  mmapWithIndexAux f 0 as
#align list.mmap_with_index List.mapIdxM

/- warning: list.mmap_with_index'_aux -> List.mapIdxMAux' is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} m] {α : Type.{u3}}, (Nat -> α -> (m PUnit.{succ u1})) -> Nat -> (List.{u3} α) -> (m PUnit.{succ u1})
but is expected to have type
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u3}}, (Nat -> α -> (m PUnit.{succ u1})) -> Nat -> (List.{u3} α) -> (m PUnit.{succ u1})
Case conversion may be inaccurate. Consider using '#align list.mmap_with_index'_aux List.mapIdxMAux'ₓ'. -/
/-- Auxiliary definition for `mmap_with_index'`. -/
def mapIdxMAux' {α} (f : ℕ → α → m PUnit) : ℕ → List α → m PUnit
  | _, [] => pure ⟨⟩
  | i, a :: as => f i a *> mmap_with_index'_aux (i + 1) as
#align list.mmap_with_index'_aux List.mapIdxMAux'

/- warning: list.mmap_with_index' -> List.mapIdxM' is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Applicative.{u1, u2} m] {α : Type.{u3}}, (Nat -> α -> (m PUnit.{succ u1})) -> (List.{u3} α) -> (m PUnit.{succ u1})
but is expected to have type
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u3}}, (Nat -> α -> (m PUnit.{succ u1})) -> (List.{u3} α) -> (m PUnit.{succ u1})
Case conversion may be inaccurate. Consider using '#align list.mmap_with_index' List.mapIdxM'ₓ'. -/
/-- A variant of `mmap_with_index` specialised to applicative actions which
return `unit`. -/
def mapIdxM' {α} (f : ℕ → α → m PUnit) (as : List α) : m PUnit :=
  mapIdxMAux' f 0 as
#align list.mmap_with_index' List.mapIdxM'

end MmapWithIndex

#print List.lookmap /-
/-- `lookmap` is a combination of `lookup` and `filter_map`.
  `lookmap f l` will apply `f : α → option α` to each element of the list,
  replacing `a → b` at the first value `a` in the list such that `f a = some b`. -/
def lookmap (f : α → Option α) : List α → List α
  | [] => []
  | a :: l =>
    match f a with
    | some b => b :: l
    | none => a :: lookmap l
#align list.lookmap List.lookmap
-/

/- warning: list.countp -> List.countp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], (List.{u1} α) -> Nat
but is expected to have type
  forall {α : Type.{u1}}, (α -> Bool) -> (List.{u1} α) -> Nat
Case conversion may be inaccurate. Consider using '#align list.countp List.countpₓ'. -/
/-- `countp p l` is the number of elements of `l` that satisfy `p`. -/
def countp (p : α → Prop) [DecidablePred p] : List α → Nat
  | [] => 0
  | x :: xs => if p x then succ (countp xs) else countp xs
#align list.countp List.countp

/- warning: list.count -> List.count is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α], α -> (List.{u1} α) -> Nat
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : BEq.{u1} α], α -> (List.{u1} α) -> Nat
Case conversion may be inaccurate. Consider using '#align list.count List.countₓ'. -/
/-- `count a l` is the number of occurrences of `a` in `l`. -/
def count [DecidableEq α] (a : α) : List α → Nat :=
  countp (Eq a)
#align list.count List.count

#print List.isPrefix /-
/-- `is_prefix l₁ l₂`, or `l₁ <+: l₂`, means that `l₁` is a prefix of `l₂`,
  that is, `l₂` has the form `l₁ ++ t` for some `t`. -/
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂
#align list.is_prefix List.isPrefix
-/

#print List.isSuffix /-
/-- `is_suffix l₁ l₂`, or `l₁ <:+ l₂`, means that `l₁` is a suffix of `l₂`,
  that is, `l₂` has the form `t ++ l₁` for some `t`. -/
def isSuffix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, t ++ l₁ = l₂
#align list.is_suffix List.isSuffix
-/

#print List.isInfix /-
/-- `is_infix l₁ l₂`, or `l₁ <:+: l₂`, means that `l₁` is a contiguous
  substring of `l₂`, that is, `l₂` has the form `s ++ l₁ ++ t` for some `s, t`. -/
def isInfix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ s t, s ++ l₁ ++ t = l₂
#align list.is_infix List.isInfix
-/

-- mathport name: «expr <+: »
infixl:50 " <+: " => isPrefix

-- mathport name: «expr <:+ »
infixl:50 " <:+ " => isSuffix

-- mathport name: «expr <:+: »
infixl:50 " <:+: " => isInfix

#print List.inits /-
/-- `inits l` is the list of initial segments of `l`.

     inits [1, 2, 3] = [[], [1], [1, 2], [1, 2, 3]] -/
@[simp]
def inits : List α → List (List α)
  | [] => [[]]
  | a :: l => [] :: map (fun t => a :: t) (inits l)
#align list.inits List.inits
-/

#print List.tails /-
/-- `tails l` is the list of terminal segments of `l`.

     tails [1, 2, 3] = [[1, 2, 3], [2, 3], [3], []] -/
@[simp]
def tails : List α → List (List α)
  | [] => [[]]
  | a :: l => (a :: l) :: tails l
#align list.tails List.tails
-/

def sublists'Aux : List α → (List α → List β) → List (List β) → List (List β)
  | [], f, r => f [] :: r
  | a :: l, f, r => sublists'_aux l f (sublists'_aux l (f ∘ cons a) r)
#align list.sublists'_aux List.sublists'Aux

#print List.sublists' /-
/-- `sublists' l` is the list of all (non-contiguous) sublists of `l`.
  It differs from `sublists` only in the order of appearance of the sublists;
  `sublists'` uses the first element of the list as the MSB,
  `sublists` uses the first element of the list as the LSB.

     sublists' [1, 2, 3] = [[], [3], [2], [2, 3], [1], [1, 3], [1, 2], [1, 2, 3]] -/
def sublists' (l : List α) : List (List α) :=
  sublists'Aux l id []
#align list.sublists' List.sublists'
-/

def sublistsAux : List α → (List α → List β → List β) → List β
  | [], f => []
  | a :: l, f => f [a] (sublists_aux l fun ys r => f ys (f (a :: ys) r))
#align list.sublists_aux List.sublistsAux

#print List.sublists /-
/-- `sublists l` is the list of all (non-contiguous) sublists of `l`; cf. `sublists'`
  for a different ordering.

     sublists [1, 2, 3] = [[], [1], [2], [1, 2], [3], [1, 3], [2, 3], [1, 2, 3]] -/
def sublists (l : List α) : List (List α) :=
  [] :: sublistsAux l cons
#align list.sublists List.sublists
-/

#print List.sublistsAux₁ /-
def sublistsAux₁ : List α → (List α → List β) → List β
  | [], f => []
  | a :: l, f => f [a] ++ sublists_aux₁ l fun ys => f ys ++ f (a :: ys)
#align list.sublists_aux₁ List.sublistsAux₁
-/

section Forall₂

variable {r : α → β → Prop} {p : γ → δ → Prop}

#print List.Forall₂ /-
/-- `forall₂ R l₁ l₂` means that `l₁` and `l₂` have the same length,
  and whenever `a` is the nth element of `l₁`, and `b` is the nth element of `l₂`,
  then `R a b` is satisfied. -/
inductive Forall₂ (R : α → β → Prop) : List α → List β → Prop
  | nil : forall₂ [] []
  | cons {a b l₁ l₂} : R a b → forall₂ l₁ l₂ → forall₂ (a :: l₁) (b :: l₂)
#align list.forall₂ List.Forall₂
-/

attribute [simp] forall₂.nil

end Forall₂

#print List.All₂ /-
/-- `l.all₂ p` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunction, i.e.
`list.all₂ p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
@[simp]
def All₂ (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ all₂ l
#align list.all₂ List.All₂
-/

/-- Auxiliary definition used to define `transpose`.
  `transpose_aux l L` takes each element of `l` and appends it to the start of
  each element of `L`.

  `transpose_aux [a, b, c] [l₁, l₂, l₃] = [a::l₁, b::l₂, c::l₃]` -/
def transposeAux : List α → List (List α) → List (List α)
  | [], ls => ls
  | a :: i, [] => [a] :: transpose_aux i []
  | a :: i, l :: ls => (a :: l) :: transpose_aux i ls
#align list.transpose_aux List.transposeAux

#print List.transpose /-
/-- transpose of a list of lists, treated as a matrix.

     transpose [[1, 2], [3, 4], [5, 6]] = [[1, 3, 5], [2, 4, 6]] -/
def transpose : List (List α) → List (List α)
  | [] => []
  | l :: ls => transposeAux l (transpose ls)
#align list.transpose List.transpose
-/

#print List.sections /-
/-- List of all sections through a list of lists. A section
  of `[L₁, L₂, ..., Lₙ]` is a list whose first element comes from
  `L₁`, whose second element comes from `L₂`, and so on. -/
def sections : List (List α) → List (List α)
  | [] => [[]]
  | l :: L => (bind (sections L)) fun s => map (fun a => a :: s) l
#align list.sections List.sections
-/

section Permutations

#print List.permutationsAux2 /-
/-- An auxiliary function for defining `permutations`. `permutations_aux2 t ts r ys f` is equal to
`(ys ++ ts, (insert_left ys t ts).map f ++ r)`, where `insert_left ys t ts` (not explicitly
defined) is the list of lists of the form `insert_nth n t (ys ++ ts)` for `0 ≤ n < length ys`.

    permutations_aux2 10 [4, 5, 6] [] [1, 2, 3] id =
      ([1, 2, 3, 4, 5, 6],
       [[10, 1, 2, 3, 4, 5, 6],
        [1, 10, 2, 3, 4, 5, 6],
        [1, 2, 10, 3, 4, 5, 6]]) -/
def permutationsAux2 (t : α) (ts : List α) (r : List β) : List α → (List α → β) → List α × List β
  | [], f => (ts, r)
  | y :: ys, f =>
    let (us, zs) := permutations_aux2 ys fun x : List α => f (y :: x)
    (y :: us, f (t :: y :: us) :: zs)
#align list.permutations_aux2 List.permutationsAux2
-/

private def meas : (Σ'_ : List α, List α) → ℕ × ℕ
  | ⟨l, i⟩ => (length l + length i, length l)
#align list.meas list.meas

-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => InvImage (Prod.Lex (· < ·) (· < ·)) meas

#print List.permutationsAux.rec /-
/-- A recursor for pairs of lists. To have `C l₁ l₂` for all `l₁`, `l₂`, it suffices to have it for
`l₂ = []` and to be able to pour the elements of `l₁` into `l₂`. -/
@[elab_as_elim]
def permutationsAux.rec {C : List α → List α → Sort v} (H0 : ∀ is, C [] is)
    (H1 : ∀ t ts is, C ts (t :: is) → C is [] → C (t :: ts) is) : ∀ l₁ l₂, C l₁ l₂
  | [], is => H0 is
  | t :: ts, is =>
    have h1 : ⟨ts, t :: is⟩ ≺ ⟨t :: ts, is⟩ :=
      show
        Prod.Lex _ _ (succ (length ts + length is), length ts)
          (succ (length ts) + length is, length (t :: ts))
        by rw [Nat.succ_add] <;> exact Prod.Lex.right _ (lt_succ_self _)
    have h2 : ⟨is, []⟩ ≺ ⟨t :: ts, is⟩ := Prod.Lex.left _ _ (Nat.lt_add_of_pos_left (succ_pos _))
    H1 t ts is (permutations_aux.rec ts (t :: is)) (permutations_aux.rec is [])termination_by'
  ⟨(· ≺ ·), @InvImage.wf _ _ _ meas (Prod.lex_wf lt_wf lt_wf)⟩
#align list.permutations_aux.rec List.permutationsAux.rec
-/

#print List.permutationsAux /-
/-- An auxiliary function for defining `permutations`. `permutations_aux ts is` is the set of all
permutations of `is ++ ts` that do not fix `ts`. -/
def permutationsAux : List α → List α → List (List α) :=
  @permutationsAux.rec (fun _ _ => List (List α)) (fun is => []) fun t ts is IH1 IH2 =>
    foldr (fun y r => (permutationsAux2 t ts r y id).2) IH1 (is :: IH2)
#align list.permutations_aux List.permutationsAux
-/

#print List.permutations /-
/-- List of all permutations of `l`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [3, 2, 1],
        [2, 3, 1], [3, 1, 2], [1, 3, 2]] -/
def permutations (l : List α) : List (List α) :=
  l :: permutationsAux l []
#align list.permutations List.permutations
-/

#print List.permutations'Aux /-
/-- `permutations'_aux t ts` inserts `t` into every position in `ts`, including the last.
This function is intended for use in specifications, so it is simpler than `permutations_aux2`,
which plays roughly the same role in `permutations`.

Note that `(permutations_aux2 t [] [] ts id).2` is similar to this function, but skips the last
position:

    permutations'_aux 10 [1, 2, 3] =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3], [1, 2, 3, 10]]
    (permutations_aux2 10 [] [] [1, 2, 3] id).2 =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3]] -/
@[simp]
def permutations'Aux (t : α) : List α → List (List α)
  | [] => [[t]]
  | y :: ys => (t :: y :: ys) :: (permutations'_aux ys).map (cons y)
#align list.permutations'_aux List.permutations'Aux
-/

#print List.permutations' /-
/-- List of all permutations of `l`. This version of `permutations` is less efficient but has
simpler definitional equations. The permutations are in a different order,
but are equal up to permutation, as shown by `list.permutations_perm_permutations'`.

     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 3, 2], [3, 1, 2], [3, 2, 1]] -/
@[simp]
def permutations' : List α → List (List α)
  | [] => [[]]
  | t :: ts => (permutations' ts).bind <| permutations'Aux t
#align list.permutations' List.permutations'
-/

end Permutations

/-- `erasep p l` removes the first element of `l` satisfying the predicate `p`. -/
def eraseP (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | a :: l => if p a then l else a :: erasep l
#align list.erasep List.erasePₓ

#print List.extractp /-
/-- `extractp p l` returns a pair of an element `a` of `l` satisfying the predicate
  `p`, and `l`, with `a` removed. If there is no such element `a` it returns `(none, l)`. -/
def extractp (p : α → Prop) [DecidablePred p] : List α → Option α × List α
  | [] => (none, [])
  | a :: l =>
    if p a then (some a, l)
    else
      let (a', l') := extractp l
      (a', a :: l')
#align list.extractp List.extractp
-/

#print List.revzip /-
/-- `revzip l` returns a list of pairs of the elements of `l` paired
  with the elements of `l` in reverse order.

`revzip [1,2,3,4,5] = [(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)]`
 -/
def revzip (l : List α) : List (α × α) :=
  zip l l.reverse
#align list.revzip List.revzip
-/

#print List.product /-
/-- `product l₁ l₂` is the list of pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂`.

     product [1, 2] [5, 6] = [(1, 5), (1, 6), (2, 5), (2, 6)] -/
def product (l₁ : List α) (l₂ : List β) : List (α × β) :=
  l₁.bind fun a => l₂.map <| Prod.mk a
#align list.product List.product
-/

-- mathport name: list.product
infixr:82
  " ×ˢ " =>-- This notation binds more strongly than (pre)images, unions and intersections.
  List.product

#print List.sigma /-
/-- `sigma l₁ l₂` is the list of dependent pairs `(a, b)` where `a ∈ l₁` and `b ∈ l₂ a`.

     sigma [1, 2] (λ_, [(5 : ℕ), 6]) = [(1, 5), (1, 6), (2, 5), (2, 6)] -/
protected def sigma {σ : α → Type _} (l₁ : List α) (l₂ : ∀ a, List (σ a)) : List (Σa, σ a) :=
  l₁.bind fun a => (l₂ a).map <| Sigma.mk a
#align list.sigma List.sigma
-/

/-- Auxliary definition used to define `of_fn`.

  `of_fn_aux f m h l` returns the first `m` elements of `of_fn f`
  appended to `l` -/
def ofFnAux {n} (f : Fin n → α) : ∀ m, m ≤ n → List α → List α
  | 0, h, l => l
  | succ m, h, l => of_fn_aux m (le_of_lt h) (f ⟨m, h⟩ :: l)
#align list.of_fn_aux List.ofFnAux

#print List.ofFn /-
/-- `of_fn f` with `f : fin n → α` returns the list whose ith element is `f i`
  `of_fun f = [f 0, f 1, ... , f(n - 1)]` -/
def ofFn {n} (f : Fin n → α) : List α :=
  ofFnAux f n (le_refl _) []
#align list.of_fn List.ofFn
-/

#print List.ofFnNthVal /-
/-- `of_fn_nth_val f i` returns `some (f i)` if `i < n` and `none` otherwise. -/
def ofFnNthVal {n} (f : Fin n → α) (i : ℕ) : Option α :=
  if h : i < n then some (f ⟨i, h⟩) else none
#align list.of_fn_nth_val List.ofFnNthVal
-/

#print List.Disjoint /-
/-- `disjoint l₁ l₂` means that `l₁` and `l₂` have no elements in common. -/
def Disjoint (l₁ l₂ : List α) : Prop :=
  ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False
#align list.disjoint List.Disjoint
-/

section Pairwise

variable (R : α → α → Prop)

#print List.Pairwise /-
/-- `pairwise R l` means that all the elements with earlier indexes are
  `R`-related to all the elements with later indexes.

     pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3

  For example if `R = (≠)` then it asserts `l` has no duplicates,
  and if `R = (<)` then it asserts that `l` is (strictly) sorted. -/
inductive Pairwise : List α → Prop
  | nil : Pairwise []
  | cons : ∀ {a : α} {l : List α}, (∀ a' ∈ l, R a a') → Pairwise l → Pairwise (a :: l)
#align list.pairwise List.Pairwise
-/

variable {R}

#print List.pairwise_cons /-
@[simp]
theorem pairwise_cons {a : α} {l : List α} :
    Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ Pairwise R l :=
  ⟨fun p => by cases' p with a l n p <;> exact ⟨n, p⟩, fun ⟨n, p⟩ => p.cons n⟩
#align list.pairwise_cons List.pairwise_cons
-/

attribute [simp] pairwise.nil

#print List.instDecidablePairwise /-
instance instDecidablePairwise [DecidableRel R] (l : List α) : Decidable (Pairwise R l) := by
  induction' l with hd tl ih <;> [exact is_true pairwise.nil,
    exact decidable_of_iff' _ pairwise_cons]
#align list.decidable_pairwise List.instDecidablePairwise
-/

end Pairwise

#print List.pwFilter /-
/-- `pw_filter R l` is a maximal sublist of `l` which is `pairwise R`.
  `pw_filter (≠)` is the erase duplicates function (cf. `dedup`), and `pw_filter (<)` finds
  a maximal increasing subsequence in `l`. For example,

     pw_filter (<) [0, 1, 5, 2, 6, 3, 4] = [0, 1, 2, 3, 4] -/
def pwFilter (R : α → α → Prop) [DecidableRel R] : List α → List α
  | [] => []
  | x :: xs =>
    let IH := pw_filter xs
    if ∀ y ∈ IH, R x y then x :: IH else IH
#align list.pw_filter List.pwFilter
-/

section Chain

variable (R : α → α → Prop)

#print List.Chain /-
/-- `chain R a l` means that `R` holds between adjacent elements of `a::l`.

     chain R a [b, c, d] ↔ R a b ∧ R b c ∧ R c d -/
inductive Chain : α → List α → Prop
  | nil {a : α} : chain a []
  | cons : ∀ {a b : α} {l : List α}, R a b → chain b l → chain a (b :: l)
#align list.chain List.Chain
-/

#print List.Chain' /-
/-- `chain' R l` means that `R` holds between adjacent elements of `l`.

     chain' R [a, b, c, d] ↔ R a b ∧ R b c ∧ R c d -/
def Chain' : List α → Prop
  | [] => True
  | a :: l => Chain R a l
#align list.chain' List.Chain'
-/

variable {R}

#print List.chain_cons /-
@[simp]
theorem chain_cons {a b : α} {l : List α} : Chain R a (b :: l) ↔ R a b ∧ Chain R b l :=
  ⟨fun p => by cases' p with _ a b l n p <;> exact ⟨n, p⟩, fun ⟨n, p⟩ => p.cons n⟩
#align list.chain_cons List.chain_cons
-/

attribute [simp] chain.nil

#print List.decidableChain /-
instance decidableChain [DecidableRel R] (a : α) (l : List α) : Decidable (Chain R a l) := by
  induction l generalizing a <;> simp only [chain.nil, chain_cons] <;> skip <;> infer_instance
#align list.decidable_chain List.decidableChain
-/

#print List.decidableChain' /-
instance decidableChain' [DecidableRel R] (l : List α) : Decidable (Chain' R l) := by
  cases l <;> dsimp only [chain'] <;> infer_instance
#align list.decidable_chain' List.decidableChain'
-/

end Chain

#print List.Nodup /-
/-- `nodup l` means that `l` has no duplicates, that is, any element appears at most
  once in the list. It is defined as `pairwise (≠)`. -/
def Nodup : List α → Prop :=
  Pairwise (· ≠ ·)
#align list.nodup List.Nodup
-/

#print List.nodupDecidable /-
instance nodupDecidable [DecidableEq α] : ∀ l : List α, Decidable (Nodup l) :=
  List.instDecidablePairwise
#align list.nodup_decidable List.nodupDecidable
-/

#print List.dedup /-
/-- `dedup l` removes duplicates from `l` (taking only the last occurrence).
  Defined as `pw_filter (≠)`.

     dedup [1, 0, 2, 2, 1] = [0, 2, 1] -/
def dedup [DecidableEq α] : List α → List α :=
  pwFilter (· ≠ ·)
#align list.dedup List.dedup
-/

#print List.destutter' /-
/-- Greedily create a sublist of `a :: l` such that, for every two adjacent elements `a, b`,
`R a b` holds. Mostly used with ≠; for example, `destutter' (≠) 1 [2, 2, 1, 1] = [1, 2, 1]`,
`destutter' (≠) 1, [2, 3, 3] = [1, 2, 3]`, `destutter' (<) 1 [2, 5, 2, 3, 4, 9] = [1, 2, 5, 9]`. -/
def destutter' (R : α → α → Prop) [DecidableRel R] : α → List α → List α
  | a, [] => [a]
  | a, h :: l => if R a h then a :: destutter' h l else destutter' a l
#align list.destutter' List.destutter'
-/

#print List.destutter /-
/-- Greedily create a sublist of `l` such that, for every two adjacent elements `a, b ∈ l`,
`R a b` holds. Mostly used with ≠; for example, `destutter (≠) [1, 2, 2, 1, 1] = [1, 2, 1]`,
`destutter (≠) [1, 2, 3, 3] = [1, 2, 3]`, `destutter (<) [1, 2, 5, 2, 3, 4, 9] = [1, 2, 5, 9]`. -/
def destutter (R : α → α → Prop) [DecidableRel R] : List α → List α
  | h :: l => destutter' R h l
  | [] => []
#align list.destutter List.destutter
-/

#print List.range' /-
/-- `range' s n` is the list of numbers `[s, s+1, ..., s+n-1]`.
  It is intended mainly for proving properties of `range` and `iota`. -/
@[simp]
def range' : ℕ → ℕ → List ℕ
  | s, 0 => []
  | s, n + 1 => s :: range' (s + 1) n
#align list.range' List.range'
-/

#print List.reduceOption /-
/-- Drop `none`s from a list, and replace each remaining `some a` with `a`. -/
def reduceOption {α} : List (Option α) → List α :=
  List.filterMap id
#align list.reduce_option List.reduceOption
-/

#print List.ilast' /-
/-- `ilast' x xs` returns the last element of `xs` if `xs` is non-empty;
it returns `x` otherwise -/
@[simp]
def ilast' {α} : α → List α → α
  | a, [] => a
  | a, b :: l => ilast' b l
#align list.ilast' List.ilast'
-/

#print List.getLast? /-
/-- `last' xs` returns the last element of `xs` if `xs` is non-empty;
it returns `none` otherwise -/
@[simp]
def getLast? {α} : List α → Option α
  | [] => none
  | [a] => some a
  | b :: l => last' l
#align list.last' List.getLast?
-/

#print List.rotate /-
/-- `rotate l n` rotates the elements of `l` to the left by `n`

     rotate [0, 1, 2, 3, 4, 5] 2 = [2, 3, 4, 5, 0, 1] -/
def rotate (l : List α) (n : ℕ) : List α :=
  let (l₁, l₂) := List.splitAt (n % l.length) l
  l₂ ++ l₁
#align list.rotate List.rotate
-/

#print List.rotate' /-
/-- rotate' is the same as `rotate`, but slower. Used for proofs about `rotate`-/
def rotate' : List α → ℕ → List α
  | [], n => []
  | l, 0 => l
  | a :: l, n + 1 => rotate' (l ++ [a]) n
#align list.rotate' List.rotate'
-/

section Choose

variable (p : α → Prop) [DecidablePred p] (l : List α)

#print List.chooseX /-
/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns both `a` and proofs
of `a ∈ l` and `p a`. -/
def chooseX : ∀ l : List α, ∀ hp : ∃ a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a }
  | [], hp => False.elim (Exists.elim hp fun a h => not_mem_nil a h.left)
  | l :: ls, hp =>
    if pl : p l then ⟨l, ⟨Or.inl rfl, pl⟩⟩
    else
      let ⟨a, ⟨a_mem_ls, pa⟩⟩ :=
        choose_x ls (hp.imp fun b ⟨o, h₂⟩ => ⟨o.resolve_left fun e => pl <| e ▸ h₂, h₂⟩)
      ⟨a, ⟨Or.inr a_mem_ls, pa⟩⟩
#align list.choose_x List.chooseX
-/

#print List.choose /-
/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns `a : α`, and properties
are given by `choose_mem` and `choose_property`. -/
def choose (hp : ∃ a, a ∈ l ∧ p a) : α :=
  chooseX p l hp
#align list.choose List.choose
-/

end Choose

/- warning: list.mmap_filter -> List.filterMapM is a dubious translation:
lean 3 declaration is
  forall {m : Type -> Type.{u1}} [_inst_1 : Monad.{0, u1} m] {α : Type.{u2}} {β : Type}, (α -> (m (Option.{0} β))) -> (List.{u2} α) -> (m (List.{0} β))
but is expected to have type
  forall {m : Type.{u1} -> Type.{u2}} [_inst_1 : Monad.{u1, u2} m] {α : Type.{u1}} {β : Type.{u1}}, (α -> (m (Option.{u1} β))) -> (List.{u1} α) -> (m (List.{u1} β))
Case conversion may be inaccurate. Consider using '#align list.mmap_filter List.filterMapMₓ'. -/
/-- Filters and maps elements of a list -/
def filterMapM {m : Type → Type v} [Monad m] {α β} (f : α → m (Option β)) : List α → m (List β)
  | [] => return []
  | h :: t => do
    let b ← f h
    let t' ← t.mmapFilter
    return <|
        match b with
        | none => t'
        | some x => x :: t'
#align list.mmap_filter List.filterMapM

/- warning: list.mmap_upper_triangle -> List.mapDiagM is a dubious translation:
lean 3 declaration is
  forall {m : Type.{u} -> Type.{u_1}} [_inst_1 : Monad.{u, u_1} m] {α : Type.{u}} {β : Type.{u}}, (α -> α -> (m β)) -> (List.{u} α) -> (m (List.{u} β))
but is expected to have type
  forall {m : Type.{u_1} -> Type.{u_2}} {_inst_1 : Type.{u_3}} {α : Type.{u_1}} [β : Monad.{u_1, u_2} m], (_inst_1 -> _inst_1 -> (m α)) -> (List.{u_3} _inst_1) -> (m (List.{u_1} α))
Case conversion may be inaccurate. Consider using '#align list.mmap_upper_triangle List.mapDiagMₓ'. -/
/-- `mmap_upper_triangle f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mmap_upper_triangle f l` will produce the list
`[f 1 1, f 1 2, f 1 3, f 2 2, f 2 3, f 3 3]`.
-/
def mapDiagM {m} [Monad m] {α β : Type u} (f : α → α → m β) : List α → m (List β)
  | [] => return []
  | h :: t => do
    let v ← f h h
    let l ← t.mmap (f h)
    let t ← t.mmapUpperTriangle
    return <| v :: l ++ t
#align list.mmap_upper_triangle List.mapDiagM

#print List.mapDiagM' /-
/-- `mmap'_diag f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mmap'_diag f l` will evaluate, in this order,
`f 1 1`, `f 1 2`, `f 1 3`, `f 2 2`, `f 2 3`, `f 3 3`.
-/
def mapDiagM' {m} [Monad m] {α} (f : α → α → m Unit) : List α → m Unit
  | [] => return ()
  | h :: t => (f h h >> t.mmap' (f h)) >> t.mmap'Diag
#align list.mmap'_diag List.mapDiagM'
-/

#print List.traverse /-
protected def traverse {F : Type u → Type v} [Applicative F] {α β : Type _} (f : α → F β) :
    List α → F (List β)
  | [] => pure []
  | x :: xs => List.cons <$> f x <*> traverse xs
#align list.traverse List.traverse
-/

#print List.getRest /-
/-- `get_rest l l₁` returns `some l₂` if `l = l₁ ++ l₂`.
  If `l₁` is not a prefix of `l`, returns `none` -/
def getRest [DecidableEq α] : List α → List α → Option (List α)
  | l, [] => some l
  | [], _ => none
  | x :: l, y :: l₁ => if x = y then get_rest l l₁ else none
#align list.get_rest List.getRest
-/

#print List.dropSlice /-
/-- `list.slice n m xs` removes a slice of length `m` at index `n` in list `xs`.
-/
def dropSlice {α} : ℕ → ℕ → List α → List α
  | 0, n, xs => xs.drop n
  | succ n, m, [] => []
  | succ n, m, x :: xs => x :: slice n m xs
#align list.slice List.dropSlice
-/

#print List.map₂Left' /-
/-- Left-biased version of `list.map₂`. `map₂_left' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is
applied to `none` for the remaining `aᵢ`. Returns the results of the `f`
applications and the remaining `bs`.

```
map₂_left' prod.mk [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])

map₂_left' prod.mk [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
```
-/
@[simp]
def map₂Left' (f : α → Option β → γ) : List α → List β → List γ × List β
  | [], bs => ([], bs)
  | a :: as, [] => ((a :: as).map fun a => f a none, [])
  | a :: as, b :: bs =>
    let rec := map₂_left' as bs
    (f a (some b) :: rec.fst, rec.snd)
#align list.map₂_left' List.map₂Left'
-/

#print List.map₂Right' /-
/-- Right-biased version of `list.map₂`. `map₂_right' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is
applied to `none` for the remaining `bᵢ`. Returns the results of the `f`
applications and the remaining `as`.

```
map₂_right' prod.mk [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])

map₂_right' prod.mk [1, 2] ['a'] = ([(some 1, 'a')], [2])
```
-/
def map₂Right' (f : Option α → β → γ) (as : List α) (bs : List β) : List γ × List α :=
  map₂Left' (flip f) bs as
#align list.map₂_right' List.map₂Right'
-/

#print List.zipLeft' /-
/-- Left-biased version of `list.zip`. `zip_left' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`. Also returns the remaining `bs`.

```
zip_left' [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])

zip_left' [1] ['a', 'b'] = ([(1, some 'a')], ['b'])

zip_left' = map₂_left' prod.mk

```
-/
def zipLeft' : List α → List β → List (α × Option β) × List β :=
  map₂Left' Prod.mk
#align list.zip_left' List.zipLeft'
-/

#print List.zipRight' /-
/-- Right-biased version of `list.zip`. `zip_right' as bs` returns the list of
pairs `(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`. Also returns the remaining `as`.

```
zip_right' [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])

zip_right' [1, 2] ['a'] = ([(some 1, 'a')], [2])

zip_right' = map₂_right' prod.mk
```
-/
def zipRight' : List α → List β → List (Option α × β) × List α :=
  map₂Right' Prod.mk
#align list.zip_right' List.zipRight'
-/

#print List.map₂Left /-
/-- Left-biased version of `list.map₂`. `map₂_left f as bs` applies `f` to each pair
`aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `bs` is shorter than `as`, `f` is applied to `none`
for the remaining `aᵢ`.

```
map₂_left prod.mk [1, 2] ['a'] = [(1, some 'a'), (2, none)]

map₂_left prod.mk [1] ['a', 'b'] = [(1, some 'a')]

map₂_left f as bs = (map₂_left' f as bs).fst
```
-/
@[simp]
def map₂Left (f : α → Option β → γ) : List α → List β → List γ
  | [], _ => []
  | a :: as, [] => (a :: as).map fun a => f a none
  | a :: as, b :: bs => f a (some b) :: map₂_left as bs
#align list.map₂_left List.map₂Left
-/

#print List.map₂Right /-
/-- Right-biased version of `list.map₂`. `map₂_right f as bs` applies `f` to each
pair `aᵢ ∈ as` and `bᵢ ‌∈ bs`. If `as` is shorter than `bs`, `f` is applied to
`none` for the remaining `bᵢ`.

```
map₂_right prod.mk [1, 2] ['a'] = [(some 1, 'a')]

map₂_right prod.mk [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

map₂_right f as bs = (map₂_right' f as bs).fst
```
-/
def map₂Right (f : Option α → β → γ) (as : List α) (bs : List β) : List γ :=
  map₂Left (flip f) bs as
#align list.map₂_right List.map₂Right
-/

#print List.zipLeft /-
/-- Left-biased version of `list.zip`. `zip_left as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, the
remaining `aᵢ` are paired with `none`.

```
zip_left [1, 2] ['a'] = [(1, some 'a'), (2, none)]

zip_left [1] ['a', 'b'] = [(1, some 'a')]

zip_left = map₂_left prod.mk
```
-/
def zipLeft : List α → List β → List (α × Option β) :=
  map₂Left Prod.mk
#align list.zip_left List.zipLeft
-/

#print List.zipRight /-
/-- Right-biased version of `list.zip`. `zip_right as bs` returns the list of pairs
`(aᵢ, bᵢ)` for `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, the
remaining `bᵢ` are paired with `none`.

```
zip_right [1, 2] ['a'] = [(some 1, 'a')]

zip_right [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

zip_right = map₂_right prod.mk
```
-/
def zipRight : List α → List β → List (Option α × β) :=
  map₂Right Prod.mk
#align list.zip_right List.zipRight
-/

#print List.allSome /-
/-- If all elements of `xs` are `some xᵢ`, `all_some xs` returns the `xᵢ`. Otherwise
it returns `none`.

```
all_some [some 1, some 2] = some [1, 2]
all_some [some 1, none  ] = none
```
-/
def allSome : List (Option α) → Option (List α)
  | [] => some []
  | some a :: as => cons a <$> all_some as
  | none :: as => none
#align list.all_some List.allSome
-/

#print List.fillNones /-
/-- `fill_nones xs ys` replaces the `none`s in `xs` with elements of `ys`. If there
are not enough `ys` to replace all the `none`s, the remaining `none`s are
dropped from `xs`.

```
fill_nones [none, some 1, none, none] [2, 3] = [2, 1, 3]
```
-/
def fillNones {α} : List (Option α) → List α → List α
  | [], _ => []
  | some a :: as, as' => a :: fill_nones as as'
  | none :: as, [] => as.reduceOption
  | none :: as, a :: as' => a :: fill_nones as as'
#align list.fill_nones List.fillNones
-/

#print List.takeList /-
/-- `take_list as ns` extracts successive sublists from `as`. For `ns = n₁ ... nₘ`,
it first takes the `n₁` initial elements from `as`, then the next `n₂` ones,
etc. It returns the sublists of `as` -- one for each `nᵢ` -- and the remaining
elements of `as`. If `as` does not have at least as many elements as the sum of
the `nᵢ`, the corresponding sublists will have less than `nᵢ` elements.

```
take_list ['a', 'b', 'c', 'd', 'e'] [2, 1, 1] = ([['a', 'b'], ['c'], ['d']], ['e'])
take_list ['a', 'b'] [3, 1] = ([['a', 'b'], []], [])
```
-/
def takeList {α} : List α → List ℕ → List (List α) × List α
  | xs, [] => ([], xs)
  | xs, n :: ns =>
    let ⟨xs₁, xs₂⟩ := xs.splitAt n
    let ⟨xss, rest⟩ := take_list xs₂ ns
    (xs₁ :: xss, rest)
#align list.take_list List.takeList
-/

/- warning: list.to_rbmap -> List.toRBMap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}}, (List.{u_1} α) -> (Rbmap.{0, u_1} Nat α (LT.lt.{0} Nat Nat.hasLt))
but is expected to have type
  forall {α : Type.{u_1}} {ᾰ : Type.{u_2}}, (List.{max u_2 u_1} (Prod.{u_1, u_2} α ᾰ)) -> (forall (cmp : α -> α -> Ordering), Std.RBMap.{u_1, u_2} α ᾰ cmp)
Case conversion may be inaccurate. Consider using '#align list.to_rbmap List.toRBMapₓ'. -/
/-- `to_rbmap as` is the map that associates each index `i` of `as` with the
corresponding element of `as`.

```
to_rbmap ['a', 'b', 'c'] = rbmap_of [(0, 'a'), (1, 'b'), (2, 'c')]
```
-/
def toRBMap {α : Type _} : List α → Rbmap ℕ α :=
  foldlIdx (fun i mapp a => mapp.insert i a) (mkRbmap ℕ α)
#align list.to_rbmap List.toRBMap

#print List.toChunksAux /-
/-- Auxliary definition used to define `to_chunks`.

  `to_chunks_aux n xs i` returns `(xs.take i, (xs.drop i).to_chunks (n+1))`,
  that is, the first `i` elements of `xs`, and the remaining elements chunked into
  sublists of length `n+1`. -/
def toChunksAux {α} (n : ℕ) : List α → ℕ → List α × List (List α)
  | [], i => ([], [])
  | x :: xs, 0 =>
    let (l, L) := to_chunks_aux xs n
    ([], (x :: l) :: L)
  | x :: xs, i + 1 =>
    let (l, L) := to_chunks_aux xs i
    (x :: l, L)
#align list.to_chunks_aux List.toChunksAux
-/

#print List.toChunks /-
/-- `xs.to_chunks n` splits the list into sublists of size at most `n`,
such that `(xs.to_chunks n).join = xs`.

```
[1, 2, 3, 4, 5, 6, 7, 8].to_chunks 10 = [[1, 2, 3, 4, 5, 6, 7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].to_chunks 3 = [[1, 2, 3], [4, 5, 6], [7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].to_chunks 2 = [[1, 2], [3, 4], [5, 6], [7, 8]]
[1, 2, 3, 4, 5, 6, 7, 8].to_chunks 0 = [[1, 2, 3, 4, 5, 6, 7, 8]]
```
-/
def toChunks {α} : ℕ → List α → List (List α)
  | _, [] => []
  | 0, xs => [xs]
  | n + 1, x :: xs =>
    let (l, L) := toChunksAux n xs n
    (x :: l) :: L
#align list.to_chunks List.toChunks
-/

#print List.mapAsyncChunked /-
/-- Asynchronous version of `list.map`.
-/
unsafe def mapAsyncChunked {α β} (f : α → β) (xs : List α) (chunk_size := 1024) : List β :=
  ((xs.toChunks chunk_size).map fun xs => task.delay fun _ => List.map f xs).bind task.get
#align list.map_async_chunked List.mapAsyncChunked
-/

/-!
We add some n-ary versions of `list.zip_with` for functions with more than two arguments.
These can also be written in terms of `list.zip` or `list.zip_with`.
For example, `zip_with3 f xs ys zs` could also be written as
`zip_with id (zip_with f xs ys) zs`
or as
`(zip xs $ zip ys zs).map $ λ ⟨x, y, z⟩, f x y z`.
-/


#print List.zipWith3 /-
/-- Ternary version of `list.zip_with`. -/
def zipWith3 (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | x :: xs, y :: ys, z :: zs => f x y z :: zip_with3 xs ys zs
  | _, _, _ => []
#align list.zip_with3 List.zipWith3
-/

#print List.zipWith4 /-
/-- Quaternary version of `list.zip_with`. -/
def zipWith4 (f : α → β → γ → δ → ε) : List α → List β → List γ → List δ → List ε
  | x :: xs, y :: ys, z :: zs, u :: us => f x y z u :: zip_with4 xs ys zs us
  | _, _, _, _ => []
#align list.zip_with4 List.zipWith4
-/

#print List.zipWith5 /-
/-- Quinary version of `list.zip_with`. -/
def zipWith5 (f : α → β → γ → δ → ε → ζ) : List α → List β → List γ → List δ → List ε → List ζ
  | x :: xs, y :: ys, z :: zs, u :: us, v :: vs => f x y z u v :: zip_with5 xs ys zs us vs
  | _, _, _, _, _ => []
#align list.zip_with5 List.zipWith5
-/

#print List.replaceIf /-
/-- Given a starting list `old`, a list of booleans and a replacement list `new`,
read the items in `old` in succession and either replace them with the next element of `new` or
not, according as to whether the corresponding boolean is `tt` or `ff`. -/
def replaceIf : List α → List Bool → List α → List α
  | l, _, [] => l
  | [], _, _ => []
  | l, [], _ => l
  | n :: ns, tf :: bs, e@(c :: cs) => if tf then c :: ns.replaceIf bs cs else n :: ns.replaceIf bs e
#align list.replace_if List.replaceIf
-/

#print List.mapWithPrefixSuffixAux /-
/-- An auxiliary function for `list.map_with_prefix_suffix`. -/
def mapWithPrefixSuffixAux {α β} (f : List α → α → List α → β) : List α → List α → List β
  | prev, [] => []
  | prev, h :: t => f prev h t :: map_with_prefix_suffix_aux (prev.concat h) t
#align list.map_with_prefix_suffix_aux List.mapWithPrefixSuffixAux
-/

#print List.mapWithPrefixSuffix /-
/-- `list.map_with_prefix_suffix f l` maps `f` across a list `l`.
For each `a ∈ l` with `l = pref ++ [a] ++ suff`, `a` is mapped to `f pref a suff`.

Example: if `f : list ℕ → ℕ → list ℕ → β`,
`list.map_with_prefix_suffix f [1, 2, 3]` will produce the list
`[f [] 1 [2, 3], f [1] 2 [3], f [1, 2] 3 []]`.
-/
def mapWithPrefixSuffix {α β} (f : List α → α → List α → β) (l : List α) : List β :=
  mapWithPrefixSuffixAux f [] l
#align list.map_with_prefix_suffix List.mapWithPrefixSuffix
-/

#print List.mapWithComplement /-
/-- `list.map_with_complement f l` is a variant of `list.map_with_prefix_suffix`
that maps `f` across a list `l`.
For each `a ∈ l` with `l = pref ++ [a] ++ suff`, `a` is mapped to `f a (pref ++ suff)`,
i.e., the list input to `f` is `l` with `a` removed.

Example: if `f : ℕ → list ℕ → β`, `list.map_with_complement f [1, 2, 3]` will produce the list
`[f 1 [2, 3], f 2 [1, 3], f 3 [1, 2]]`.
-/
def mapWithComplement {α β} (f : α → List α → β) : List α → List β :=
  map_with_prefix_suffix fun pref a suff => f a (pref ++ suff)
#align list.map_with_complement List.mapWithComplement
-/

end List


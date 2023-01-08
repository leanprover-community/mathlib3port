/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module data.lazy_list
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

/-!
# Lazy lists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The type `lazy_list α` is a lazy list with elements of type `α`.
In the VM, these are potentially infinite lists
where all elements after the first are computed on-demand.
(This is only useful for execution in the VM,
logically we can prove that `lazy_list α` is isomorphic to `list α`.)
-/


universe u v w

#print LazyList /-
/-- Lazy list.
All elements (except the first) are computed lazily.
-/
inductive LazyList (α : Type u) : Type u
  | nil : LazyList
  | cons (hd : α) (tl : Thunk LazyList) : LazyList
#align lazy_list LazyList
-/

namespace LazyList

variable {α : Type u} {β : Type v} {δ : Type w}

instance : Inhabited (LazyList α) :=
  ⟨nil⟩

#print LazyList.singleton /-
/-- The singleton lazy list.  -/
def singleton : α → LazyList α
  | a => cons a nil
#align lazy_list.singleton LazyList.singleton
-/

#print LazyList.ofList /-
/-- Constructs a lazy list from a list. -/
def ofList : List α → LazyList α
  | [] => nil
  | h :: t => cons h (of_list t)
#align lazy_list.of_list LazyList.ofList
-/

#print LazyList.toList /-
/-- Converts a lazy list to a list.
If the lazy list is infinite,
then this function does not terminate.
-/
def toList : LazyList α → List α
  | nil => []
  | cons h t => h :: to_list (t ())
#align lazy_list.to_list LazyList.toList
-/

#print LazyList.headI /-
/-- Returns the first element of the lazy list,
or `default` if the lazy list is empty.
-/
def headI [Inhabited α] : LazyList α → α
  | nil => default
  | cons h t => h
#align lazy_list.head LazyList.headI
-/

#print LazyList.tail /-
/-- Removes the first element of the lazy list.
-/
def tail : LazyList α → LazyList α
  | nil => nil
  | cons h t => t ()
#align lazy_list.tail LazyList.tail
-/

/- warning: lazy_list.append -> LazyList.append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, (LazyList.{u1} α) -> (Thunkₓ.{u1} (LazyList.{u1} α)) -> (LazyList.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, (LazyList.{u1} α) -> (Thunk.{u1} (LazyList.{u1} α)) -> (LazyList.{u1} α)
Case conversion may be inaccurate. Consider using '#align lazy_list.append LazyList.appendₓ'. -/
/-- Appends two lazy lists.  -/
def append : LazyList α → Thunk (LazyList α) → LazyList α
  | nil, l => l ()
  | cons h t, l => cons h (@append (t ()) l)
#align lazy_list.append LazyList.append

#print LazyList.map /-
/-- Maps a function over a lazy list. -/
def map (f : α → β) : LazyList α → LazyList β
  | nil => nil
  | cons h t => cons (f h) (map (t ()))
#align lazy_list.map LazyList.map
-/

#print LazyList.map₂ /-
/-- Maps a binary function over two lazy list.
Like `lazy_list.zip`, the result is only as long as the smaller input.
-/
def map₂ (f : α → β → δ) : LazyList α → LazyList β → LazyList δ
  | nil, _ => nil
  | _, nil => nil
  | cons h₁ t₁, cons h₂ t₂ => cons (f h₁ h₂) (map₂ (t₁ ()) (t₂ ()))
#align lazy_list.map₂ LazyList.map₂
-/

#print LazyList.zip /-
/-- Zips two lazy lists. -/
def zip : LazyList α → LazyList β → LazyList (α × β) :=
  map₂ Prod.mk
#align lazy_list.zip LazyList.zip
-/

#print LazyList.join /-
/-- The monadic join operation for lazy lists. -/
def join : LazyList (LazyList α) → LazyList α
  | nil => nil
  | cons h t => append h (join (t ()))
#align lazy_list.join LazyList.join
-/

#print LazyList.for /-
/-- Maps a function over a lazy list.
Same as `lazy_list.map`, but with swapped arguments.
-/
def for (l : LazyList α) (f : α → β) : LazyList β :=
  map f l
#align lazy_list.for LazyList.for
-/

#print LazyList.approx /-
/-- The list containing the first `n` elements of a lazy list.  -/
def approx : Nat → LazyList α → List α
  | 0, l => []
  | _, nil => []
  | a + 1, cons h t => h :: approx a (t ())
#align lazy_list.approx LazyList.approx
-/

#print LazyList.filter /-
/-- The lazy list of all elements satisfying the predicate.
If the lazy list is infinite and none of the elements satisfy the predicate,
then this function will not terminate.
-/
def filter (p : α → Prop) [DecidablePred p] : LazyList α → LazyList α
  | nil => nil
  | cons h t => if p h then cons h (filter (t ())) else filter (t ())
#align lazy_list.filter LazyList.filter
-/

#print LazyList.nth /-
/-- The nth element of a lazy list as an option (like `list.nth`). -/
def nth : LazyList α → Nat → Option α
  | nil, n => none
  | cons a l, 0 => some a
  | cons a l, n + 1 => nth (l ()) n
#align lazy_list.nth LazyList.nth
-/

#print LazyList.iterates /-
/-- The infinite lazy list `[x, f x, f (f x), ...]` of iterates of a function.
This definition is meta because it creates an infinite list.
-/
unsafe def iterates (f : α → α) : α → LazyList α
  | x => cons x (iterates (f x))
#align lazy_list.iterates LazyList.iterates
-/

#print LazyList.iota /-
/-- The infinite lazy list `[i, i+1, i+2, ...]` -/
unsafe def iota (i : Nat) : LazyList Nat :=
  iterates Nat.succ i
#align lazy_list.iota LazyList.iota
-/

end LazyList


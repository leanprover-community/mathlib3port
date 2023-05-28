/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.dlist.basic
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Leanbin.Data.Dlist

/-!
# Difference list

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides a few results about `dlist`, which is defined in core Lean.

A difference list is a function that, given a list, returns the original content of the
difference list prepended to the given list. It is useful to represent elements of a given type
as `a₁ + ... + aₙ` where `+ : α → α → α` is any operation, without actually computing.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/


/-- Concatenates a list of difference lists to form a single difference list. Similar to
`list.join`. -/
def Std.DList.join {α : Type _} : List (Dlist α) → Dlist α
  | [] => Dlist.empty
  | x :: xs => x ++ Std.DList.join xs
#align dlist.join Std.DList.join

@[simp]
theorem Std.DList_singleton {α : Type _} {a : α} : Dlist.singleton a = Std.DList.lazy_ofList [a] :=
  rfl
#align dlist_singleton Std.DList_singleton

@[simp]
theorem Std.DList_lazy {α : Type _} {l : List α} : Std.DList.lazy_ofList l = Dlist.ofList l :=
  rfl
#align dlist_lazy Std.DList_lazy


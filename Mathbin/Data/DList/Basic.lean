/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Data.DList.Defs

#align_import data.dlist.basic from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

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


#print Batteries.DList.join /-
/-- Concatenates a list of difference lists to form a single difference list. Similar to
`list.join`. -/
def Batteries.DList.join {α : Type _} : List (Batteries.DList α) → Batteries.DList α
  | [] => Batteries.DList.empty
  | x :: xs => x ++ Batteries.DList.join xs
#align dlist.join Batteries.DList.join
-/

#print Batteries.DList_singleton /-
@[simp]
theorem Batteries.DList_singleton {α : Type _} {a : α} :
    Batteries.DList.singleton a = Batteries.DList.lazy_ofList [a] :=
  rfl
#align dlist_singleton Batteries.DList_singleton
-/

#print Batteries.DList_lazy /-
@[simp]
theorem Batteries.DList_lazy {α : Type _} {l : List α} :
    Batteries.DList.lazy_ofList l = Batteries.DList.ofList l :=
  rfl
#align dlist_lazy Batteries.DList_lazy
-/


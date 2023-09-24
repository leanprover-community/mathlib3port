/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Data.Dlist

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


#print Std.DList.join /-
/-- Concatenates a list of difference lists to form a single difference list. Similar to
`list.join`. -/
def Std.DList.join {α : Type _} : List (Std.DList α) → Std.DList α
  | [] => Std.DList.empty
  | x :: xs => x ++ Std.DList.join xs
#align dlist.join Std.DList.join
-/

#print Std.DList_singleton /-
@[simp]
theorem Std.DList_singleton {α : Type _} {a : α} :
    Std.DList.singleton a = Std.DList.lazy_ofList [a] :=
  rfl
#align dlist_singleton Std.DList_singleton
-/

#print Std.DList_lazy /-
@[simp]
theorem Std.DList_lazy {α : Type _} {l : List α} : Std.DList.lazy_ofList l = Std.DList.ofList l :=
  rfl
#align dlist_lazy Std.DList_lazy
-/


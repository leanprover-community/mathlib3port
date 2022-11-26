/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Leanbin.Data.Dlist

/-!
# Difference list

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/616
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
def Dlist.join {α : Type _} : List (Dlist α) → Dlist α
  | [] => Dlist.empty
  | x :: xs => x ++ Dlist.join xs
#align dlist.join Dlist.join

@[simp]
theorem dlist_singleton {α : Type _} {a : α} : Dlist.singleton a = Dlist.lazyOfList [a] :=
  rfl
#align dlist_singleton dlist_singleton

@[simp]
theorem dlist_lazy {α : Type _} {l : List α} : Dlist.lazyOfList l = Dlist.ofList l :=
  rfl
#align dlist_lazy dlist_lazy


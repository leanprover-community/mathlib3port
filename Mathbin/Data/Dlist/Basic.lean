/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.dlist.basic
! leanprover-community/mathlib commit e001509c11c4d0f549d91d89da95b4a0b43c714f
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


/- warning: dlist.join -> Std.DList.join is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, (List.{u1} (Dlist.{u1} α)) -> (Dlist.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, (List.{u1} (Std.DList.{u1} α)) -> (Std.DList.{u1} α)
Case conversion may be inaccurate. Consider using '#align dlist.join Std.DList.joinₓ'. -/
/-- Concatenates a list of difference lists to form a single difference list. Similar to
`list.join`. -/
def Std.DList.join {α : Type _} : List (Dlist α) → Dlist α
  | [] => Dlist.empty
  | x :: xs => x ++ Std.DList.join xs
#align dlist.join Std.DList.join

/- warning: dlist_singleton -> Std.DList_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α}, Eq.{succ u1} (Dlist.{u1} α) (Dlist.singleton.{u1} α a) (Std.DList.lazy_ofList.{u1} α (fun (_ : Unit) => List.cons.{u1} α a (List.nil.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {a : α}, Eq.{succ u1} (Std.DList.{u1} α) (Std.DList.singleton.{u1} α a) (Std.DList.lazy_ofList.{u1} α (Thunk.mk.{u1} (List.{u1} α) (fun (x._@.Init.Core._hyg.266 : Unit) => List.cons.{u1} α a (List.nil.{u1} α))))
Case conversion may be inaccurate. Consider using '#align dlist_singleton Std.DList_singletonₓ'. -/
@[simp]
theorem Std.DList_singleton {α : Type _} {a : α} : Dlist.singleton a = Std.DList.lazy_ofList [a] :=
  rfl
#align dlist_singleton Std.DList_singleton

/- warning: dlist_lazy -> Std.DList_lazy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {l : List.{u1} α}, Eq.{succ u1} (Dlist.{u1} α) (Std.DList.lazy_ofList.{u1} α (fun (_ : Unit) => l)) (Dlist.ofList.{u1} α l)
but is expected to have type
  forall {α : Type.{u1}} {l : List.{u1} α}, Eq.{succ u1} (Std.DList.{u1} α) (Std.DList.lazy_ofList.{u1} α (Thunk.mk.{u1} (List.{u1} α) (fun (x._@.Init.Core._hyg.266 : Unit) => l))) (Std.DList.ofList.{u1} α l)
Case conversion may be inaccurate. Consider using '#align dlist_lazy Std.DList_lazyₓ'. -/
@[simp]
theorem Std.DList_lazy {α : Type _} {l : List α} : Std.DList.lazy_ofList l = Dlist.ofList l :=
  rfl
#align dlist_lazy Std.DList_lazy


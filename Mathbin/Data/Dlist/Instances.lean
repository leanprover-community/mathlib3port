/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.dlist.instances
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Traversable.Equiv
import Mathbin.Control.Traversable.Instances

/-!
# Traversable instance for dlists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the equivalence between `list α` and `dlist α` and the traversable instance
for `dlist`.
-/


open Function Equiv

namespace Dlist

variable (α : Type _)

/- warning: dlist.list_equiv_dlist -> Std.DList.listEquivDList is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}), Equiv.{succ u1, succ u1} (List.{u1} α) (Dlist.{u1} α)
but is expected to have type
  forall (α : Type.{u1}), Equiv.{succ u1, succ u1} (List.{u1} α) (Std.DList.{u1} α)
Case conversion may be inaccurate. Consider using '#align dlist.list_equiv_dlist Std.DList.listEquivDListₓ'. -/
/-- The natural equivalence between lists and difference lists, using
`dlist.of_list` and `dlist.to_list`. -/
def Std.DList.listEquivDList : List α ≃ Dlist α := by
  refine'
      { toFun := Dlist.ofList
        invFun := Dlist.toList.. } <;>
    simp [Function.RightInverse, left_inverse, to_list_of_list, of_list_to_list]
#align dlist.list_equiv_dlist Std.DList.listEquivDList

instance : Traversable Dlist :=
  Equiv.traversable Std.DList.listEquivDList

instance : IsLawfulTraversable Dlist :=
  Equiv.isLawfulTraversable Std.DList.listEquivDList

instance {α} : Inhabited (Dlist α) :=
  ⟨Dlist.empty⟩

end Dlist


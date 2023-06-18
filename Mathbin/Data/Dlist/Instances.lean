/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.dlist.instances
! leanprover-community/mathlib commit e46da4e335b8671848ac711ccb34b42538c0d800
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

namespace Std.DList

variable (α : Type _)

#print Std.DList.listEquivDList /-
/-- The natural equivalence between lists and difference lists, using
`dlist.of_list` and `dlist.to_list`. -/
def Std.DList.listEquivDList : List α ≃ Std.DList α := by
  refine'
      { toFun := Std.DList.ofList
        invFun := Std.DList.toList .. } <;>
    simp [Function.RightInverse, left_inverse, to_list_of_list, of_list_to_list]
#align dlist.list_equiv_dlist Std.DList.listEquivDList
-/

instance : Traversable Std.DList :=
  Equiv.traversable Std.DList.listEquivDList

instance : IsLawfulTraversable Std.DList :=
  Equiv.isLawfulTraversable Std.DList.listEquivDList

instance {α} : Inhabited (Std.DList α) :=
  ⟨Std.DList.empty⟩

end Std.DList


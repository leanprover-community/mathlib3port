/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Control.Traversable.Equiv
import Control.Traversable.Instances

#align_import data.dlist.instances from "leanprover-community/mathlib"@"e46da4e335b8671848ac711ccb34b42538c0d800"

/-!
# Traversable instance for dlists

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the equivalence between `list α` and `dlist α` and the traversable instance
for `dlist`.
-/


open Function Equiv

namespace Batteries.DList

variable (α : Type _)

#print Batteries.DList.listEquivDList /-
/-- The natural equivalence between lists and difference lists, using
`dlist.of_list` and `dlist.to_list`. -/
def Batteries.DList.listEquivDList : List α ≃ Batteries.DList α := by
  refine'
      { toFun := Batteries.DList.ofList
        invFun := Batteries.DList.toList .. } <;>
    simp [Function.RightInverse, left_inverse, to_list_of_list, of_list_to_list]
#align dlist.list_equiv_dlist Batteries.DList.listEquivDList
-/

instance : Traversable Batteries.DList :=
  Equiv.traversable Batteries.DList.listEquivDList

instance : LawfulTraversable Batteries.DList :=
  Equiv.isLawfulTraversable Batteries.DList.listEquivDList

instance {α} : Inhabited (Batteries.DList α) :=
  ⟨Batteries.DList.empty⟩

end Batteries.DList


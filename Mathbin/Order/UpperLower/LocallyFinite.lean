/-
Copyright (c) 2023 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Order.LocallyFinite
import Order.UpperLower.Basic

#align_import order.upper_lower.locally_finite from "leanprover-community/mathlib"@"31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0"

/-!
# Upper and lower sets in a locally finite order

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we characterise the interaction of `upper_set`/`lower_set` and `locally_finite_order`.
-/


namespace Set

variable {α : Type _} [Preorder α] {s : Set α}

#print Set.Finite.upperClosure /-
protected theorem Finite.upperClosure [LocallyFiniteOrderTop α] (hs : s.Finite) :
    (upperClosure s : Set α).Finite := by rw [coe_upperClosure];
  exact hs.bUnion fun _ _ => finite_Ici _
#align set.finite.upper_closure Set.Finite.upperClosure
-/

#print Set.Finite.lowerClosure /-
protected theorem Finite.lowerClosure [LocallyFiniteOrderBot α] (hs : s.Finite) :
    (lowerClosure s : Set α).Finite := by rw [coe_lowerClosure];
  exact hs.bUnion fun _ _ => finite_Iic _
#align set.finite.lower_closure Set.Finite.lowerClosure
-/

end Set


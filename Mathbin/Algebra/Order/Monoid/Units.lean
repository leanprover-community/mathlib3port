/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Order.Hom.Basic
import Mathbin.Order.MinMax
import Mathbin.Algebra.Group.Units

#align_import algebra.order.monoid.units from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Units in ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

namespace Units

@[to_additive]
instance [Monoid α] [Preorder α] : Preorder αˣ :=
  Preorder.lift (coe : αˣ → α)

#print Units.val_le_val /-
@[simp, norm_cast, to_additive]
theorem val_le_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) ≤ b ↔ a ≤ b :=
  Iff.rfl
#align units.coe_le_coe Units.val_le_val
#align add_units.coe_le_coe AddUnits.val_le_val
-/

#print Units.val_lt_val /-
@[simp, norm_cast, to_additive]
theorem val_lt_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α) < b ↔ a < b :=
  Iff.rfl
#align units.coe_lt_coe Units.val_lt_val
#align add_units.coe_lt_coe AddUnits.val_lt_val
-/

@[to_additive]
instance [Monoid α] [PartialOrder α] : PartialOrder αˣ :=
  PartialOrder.lift coe Units.ext

@[to_additive]
instance [Monoid α] [LinearOrder α] : LinearOrder αˣ :=
  LinearOrder.lift' coe Units.ext

#print Units.orderEmbeddingVal /-
/-- `coe : αˣ → α` as an order embedding. -/
@[to_additive "`coe : add_units α → α` as an order embedding.",
  simps (config := { fullyApplied := false })]
def orderEmbeddingVal [Monoid α] [LinearOrder α] : αˣ ↪o α :=
  ⟨⟨coe, ext⟩, fun _ _ => Iff.rfl⟩
#align units.order_embedding_coe Units.orderEmbeddingVal
#align add_units.order_embedding_coe AddUnits.orderEmbeddingVal
-/

#print Units.max_val /-
@[simp, norm_cast, to_additive]
theorem max_val [Monoid α] [LinearOrder α] {a b : αˣ} : (↑(max a b) : α) = max a b :=
  Monotone.map_max orderEmbeddingVal.Monotone
#align units.max_coe Units.max_val
#align add_units.max_coe AddUnits.max_val
-/

#print Units.min_val /-
@[simp, norm_cast, to_additive]
theorem min_val [Monoid α] [LinearOrder α] {a b : αˣ} : (↑(min a b) : α) = min a b :=
  Monotone.map_min orderEmbeddingVal.Monotone
#align units.min_coe Units.min_val
#align add_units.min_coe AddUnits.min_val
-/

end Units


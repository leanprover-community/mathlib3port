/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Algebra.Order.UpperLower
import Topology.Algebra.Group.Basic
import Topology.Order.Basic

#align_import topology.algebra.order.upper_lower from "leanprover-community/mathlib"@"b1abe23ae96fef89ad30d9f4362c307f72a55010"

/-!
# Topological facts about upper/lower/order-connected sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

## Implementation notes

The same lemmas are true in the additive/multiplicative worlds. To avoid code duplication, we
provide `has_upper_lower_closure`, an ad hoc axiomatisation of the properties we need.
-/


open Function Set

open scoped Pointwise

#print HasUpperLowerClosure /-
/-- Ad hoc class stating that the closure of an upper set is an upper set. This is used to state
lemmas that do not mention algebraic operations for both the additive and multiplicative versions
simultaneously. If you find a satisfying replacement for this typeclass, please remove it! -/
class HasUpperLowerClosure (α : Type _) [TopologicalSpace α] [Preorder α] : Prop where
  isUpperSet_closure : ∀ s : Set α, IsUpperSet s → IsUpperSet (closure s)
  isLowerSet_closure : ∀ s : Set α, IsLowerSet s → IsLowerSet (closure s)
  isOpen_upperClosure : ∀ s : Set α, IsOpen s → IsOpen (upperClosure s : Set α)
  isOpen_lowerClosure : ∀ s : Set α, IsOpen s → IsOpen (lowerClosure s : Set α)
#align has_upper_lower_closure HasUpperLowerClosure
-/

variable {α : Type _} [TopologicalSpace α]

#print OrderedCommGroup.to_hasUpperLowerClosure /-
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCommGroup.to_hasUpperLowerClosure [OrderedCommGroup α]
    [ContinuousConstSMul α α] : HasUpperLowerClosure α
    where
  isUpperSet_closure s h x y hxy hx :=
    closure_mono (h.smul_subset <| one_le_div'.2 hxy) <| by rw [closure_smul];
      exact ⟨x, hx, div_mul_cancel _ _⟩
  isLowerSet_closure s h x y hxy hx :=
    closure_mono (h.smul_subset <| div_le_one'.2 hxy) <| by rw [closure_smul];
      exact ⟨x, hx, div_mul_cancel _ _⟩
  isOpen_upperClosure s hs := by rw [← mul_one s, ← mul_upperClosure]; exact hs.mul_right
  isOpen_lowerClosure s hs := by rw [← mul_one s, ← mul_lowerClosure]; exact hs.mul_right
#align ordered_comm_group.to_has_upper_lower_closure OrderedCommGroup.to_hasUpperLowerClosure
#align ordered_add_comm_group.to_has_upper_lower_closure OrderedAddCommGroup.to_hasUpperLowerClosure
-/

variable [Preorder α]

section OrderClosedTopology

variable [OrderClosedTopology α] {s : Set α}

#print upperBounds_closure /-
@[simp]
theorem upperBounds_closure (s : Set α) : upperBounds (closure s : Set α) = upperBounds s :=
  ext fun a => by simp_rw [mem_upperBounds_iff_subset_Iic, is_closed_Iic.closure_subset_iff]
#align upper_bounds_closure upperBounds_closure
-/

#print lowerBounds_closure /-
@[simp]
theorem lowerBounds_closure (s : Set α) : lowerBounds (closure s : Set α) = lowerBounds s :=
  ext fun a => by simp_rw [mem_lowerBounds_iff_subset_Ici, is_closed_Ici.closure_subset_iff]
#align lower_bounds_closure lowerBounds_closure
-/

#print bddAbove_closure /-
@[simp]
theorem bddAbove_closure : BddAbove (closure s) ↔ BddAbove s := by
  simp_rw [BddAbove, upperBounds_closure]
#align bdd_above_closure bddAbove_closure
-/

#print bddBelow_closure /-
@[simp]
theorem bddBelow_closure : BddBelow (closure s) ↔ BddBelow s := by
  simp_rw [BddBelow, lowerBounds_closure]
#align bdd_below_closure bddBelow_closure
-/

alias ⟨BddAbove.of_closure, BddAbove.closure⟩ := bddAbove_closure
#align bdd_above.of_closure BddAbove.of_closure
#align bdd_above.closure BddAbove.closure

alias ⟨BddBelow.of_closure, BddBelow.closure⟩ := bddBelow_closure
#align bdd_below.of_closure BddBelow.of_closure
#align bdd_below.closure BddBelow.closure

attribute [protected] BddAbove.closure BddBelow.closure

end OrderClosedTopology

variable [HasUpperLowerClosure α] {s : Set α}

#print IsUpperSet.closure /-
protected theorem IsUpperSet.closure : IsUpperSet s → IsUpperSet (closure s) :=
  HasUpperLowerClosure.isUpperSet_closure _
#align is_upper_set.closure IsUpperSet.closure
-/

#print IsLowerSet.closure /-
protected theorem IsLowerSet.closure : IsLowerSet s → IsLowerSet (closure s) :=
  HasUpperLowerClosure.isLowerSet_closure _
#align is_lower_set.closure IsLowerSet.closure
-/

#print IsOpen.upperClosure /-
protected theorem IsOpen.upperClosure : IsOpen s → IsOpen (upperClosure s : Set α) :=
  HasUpperLowerClosure.isOpen_upperClosure _
#align is_open.upper_closure IsOpen.upperClosure
-/

#print IsOpen.lowerClosure /-
protected theorem IsOpen.lowerClosure : IsOpen s → IsOpen (lowerClosure s : Set α) :=
  HasUpperLowerClosure.isOpen_lowerClosure _
#align is_open.lower_closure IsOpen.lowerClosure
-/

instance : HasUpperLowerClosure αᵒᵈ
    where
  isUpperSet_closure := @IsLowerSet.closure α _ _ _
  isLowerSet_closure := @IsUpperSet.closure α _ _ _
  isOpen_upperClosure := @IsOpen.lowerClosure α _ _ _
  isOpen_lowerClosure := @IsOpen.upperClosure α _ _ _

#print IsUpperSet.interior /-
/-
Note: `s.ord_connected` does not imply `(closure s).ord_connected`, as we can see by taking
`s := Ioo 0 1 × Ioo 1 2 ∪ Ioo 2 3 × Ioo 0 1` because then
`closure s = Icc 0 1 × Icc 1 2 ∪ Icc 2 3 × Icc 0 1` is not order-connected as
`(1, 1) ∈ closure s`, `(2, 1) ∈ closure s` but `Icc (1, 1) (2, 1) ⊈ closure s`.

`s` looks like
```
xxooooo
xxooooo
oooooxx
oooooxx
```
-/
protected theorem IsUpperSet.interior (h : IsUpperSet s) : IsUpperSet (interior s) := by
  rw [← isLowerSet_compl, ← closure_compl]; exact h.compl.closure
#align is_upper_set.interior IsUpperSet.interior
-/

#print IsLowerSet.interior /-
protected theorem IsLowerSet.interior (h : IsLowerSet s) : IsLowerSet (interior s) :=
  h.toDual.interior
#align is_lower_set.interior IsLowerSet.interior
-/

#print Set.OrdConnected.interior /-
protected theorem Set.OrdConnected.interior (h : s.OrdConnected) : (interior s).OrdConnected :=
  by
  rw [← h.upper_closure_inter_lower_closure, interior_inter]
  exact
    (upperClosure s).upper.interior.OrdConnected.inter (lowerClosure s).lower.interior.OrdConnected
#align set.ord_connected.interior Set.OrdConnected.interior
-/


/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module topology.algebra.order.upper_lower
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.UpperLower
import Mathbin.Topology.Algebra.Group.Basic

/-!
# Topological facts about upper/lower/order-connected sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

## Notes

The lemmas don't mention additive/multiplicative operations. As a result, we decide to prime the
multiplicative lemma names to indicate that there is probably a common generalisation to each pair
of additive/multiplicative lemma.
-/


open Function Set

open Pointwise

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

/- warning: ordered_comm_group.to_has_upper_lower_closure -> OrderedCommGroup.to_hasUpperLowerClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedCommGroup.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_2)))))))], HasUpperLowerClosure.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_2))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] [_inst_2 : OrderedCommGroup.{u1} α] [_inst_3 : ContinuousConstSMul.{u1, u1} α α _inst_1 (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_2)))) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_2))))))], HasUpperLowerClosure.{u1} α _inst_1 (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_2))
Case conversion may be inaccurate. Consider using '#align ordered_comm_group.to_has_upper_lower_closure OrderedCommGroup.to_hasUpperLowerClosureₓ'. -/
-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCommGroup.to_hasUpperLowerClosure [OrderedCommGroup α]
    [ContinuousConstSMul α α] : HasUpperLowerClosure α
    where
  isUpperSet_closure s h x y hxy hx :=
    closure_mono (h.smul_subset <| one_le_div'.2 hxy) <|
      by
      rw [closure_smul]
      exact ⟨x, hx, div_mul_cancel' _ _⟩
  isLowerSet_closure s h x y hxy hx :=
    closure_mono (h.smul_subset <| div_le_one'.2 hxy) <|
      by
      rw [closure_smul]
      exact ⟨x, hx, div_mul_cancel' _ _⟩
  isOpen_upperClosure s hs := by
    rw [← mul_one s, ← mul_upperClosure]
    exact hs.mul_right
  isOpen_lowerClosure s hs := by
    rw [← mul_one s, ← mul_lowerClosure]
    exact hs.mul_right
#align ordered_comm_group.to_has_upper_lower_closure OrderedCommGroup.to_hasUpperLowerClosure
#align ordered_add_comm_group.to_has_upper_lower_closure OrderedAddCommGroup.to_hasUpperLowerClosure

variable [Preorder α] [HasUpperLowerClosure α] {s : Set α}

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
protected theorem IsUpperSet.interior (h : IsUpperSet s) : IsUpperSet (interior s) :=
  by
  rw [← isLowerSet_compl, ← closure_compl]
  exact h.compl.closure
#align is_upper_set.interior IsUpperSet.interior
-/

#print IsLowerSet.interior /-
protected theorem IsLowerSet.interior (h : IsLowerSet s) : IsLowerSet (interior s) :=
  h.ofDual.interior
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


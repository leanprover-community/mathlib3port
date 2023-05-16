/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.upper_lower
! leanprover-community/mathlib commit ad0089aca372256fe53dde13ca0dfea569bf5ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Group.Defs
import Mathbin.Data.Set.Pointwise.Smul
import Mathbin.Order.UpperLower.Basic

/-!
# Algebraic operations on upper/lower sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Upper/lower sets are preserved under pointwise algebraic operations in ordered groups.
-/


open Function Set

open Pointwise

section OrderedCommMonoid

variable {α : Type _} [OrderedCommMonoid α] {s : Set α} {x : α}

/- warning: is_upper_set.smul_subset -> IsUpperSet.smul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Set.{u1} α} {x : α}, (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))))) x) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))) x s) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Set.{u1} α} {x : α}, (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))) x) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)) (Monoid.toMulAction.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))) x s) s)
Case conversion may be inaccurate. Consider using '#align is_upper_set.smul_subset IsUpperSet.smul_subsetₓ'. -/
@[to_additive]
theorem IsUpperSet.smul_subset (hs : IsUpperSet s) (hx : 1 ≤ x) : x • s ⊆ s :=
  smul_set_subset_iff.2 fun y => hs <| le_mul_of_one_le_left' hx
#align is_upper_set.smul_subset IsUpperSet.smul_subset
#align is_upper_set.vadd_subset IsUpperSet.vadd_subset

/- warning: is_lower_set.smul_subset -> IsLowerSet.smul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Set.{u1} α} {x : α}, (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) s) -> (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) x (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))) x s) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {s : Set.{u1} α} {x : α}, (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) s) -> (LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommMonoid.toPartialOrder.{u1} α _inst_1))) x (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)) (Monoid.toMulAction.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))) x s) s)
Case conversion may be inaccurate. Consider using '#align is_lower_set.smul_subset IsLowerSet.smul_subsetₓ'. -/
@[to_additive]
theorem IsLowerSet.smul_subset (hs : IsLowerSet s) (hx : x ≤ 1) : x • s ⊆ s :=
  smul_set_subset_iff.2 fun y => hs <| mul_le_of_le_one_left' hx
#align is_lower_set.smul_subset IsLowerSet.smul_subset
#align is_lower_set.vadd_subset IsLowerSet.vadd_subset

end OrderedCommMonoid

section OrderedCommGroup

variable {α : Type _} [OrderedCommGroup α] {s t : Set α} {a : α}

/- warning: is_upper_set.smul -> IsUpperSet.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {a : α}, (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {a : α}, (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a s))
Case conversion may be inaccurate. Consider using '#align is_upper_set.smul IsUpperSet.smulₓ'. -/
@[to_additive]
theorem IsUpperSet.smul (hs : IsUpperSet s) : IsUpperSet (a • s) :=
  by
  rintro _ y hxy ⟨x, hx, rfl⟩
  exact mem_smul_set_iff_inv_smul_mem.2 (hs (le_inv_mul_iff_mul_le.2 hxy) hx)
#align is_upper_set.smul IsUpperSet.smul
#align is_upper_set.vadd IsUpperSet.vadd

/- warning: is_lower_set.smul -> IsLowerSet.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {a : α}, (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {a : α}, (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a s))
Case conversion may be inaccurate. Consider using '#align is_lower_set.smul IsLowerSet.smulₓ'. -/
@[to_additive]
theorem IsLowerSet.smul (hs : IsLowerSet s) : IsLowerSet (a • s) :=
  hs.ofDual.smul
#align is_lower_set.smul IsLowerSet.smul
#align is_lower_set.vadd IsLowerSet.vadd

/- warning: set.ord_connected.smul -> Set.OrdConnected.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {a : α}, (Set.OrdConnected.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s) -> (Set.OrdConnected.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {a : α}, (Set.OrdConnected.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s) -> (Set.OrdConnected.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a s))
Case conversion may be inaccurate. Consider using '#align set.ord_connected.smul Set.OrdConnected.smulₓ'. -/
@[to_additive]
theorem Set.OrdConnected.smul (hs : s.OrdConnected) : (a • s).OrdConnected :=
  by
  rw [← hs.upper_closure_inter_lower_closure, smul_set_inter]
  exact (upperClosure _).upper.smul.OrdConnected.inter (lowerClosure _).lower.smul.OrdConnected
#align set.ord_connected.smul Set.OrdConnected.smul
#align set.ord_connected.vadd Set.OrdConnected.vadd

/- warning: is_upper_set.mul_left -> IsUpperSet.mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) t) -> (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) t) -> (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t))
Case conversion may be inaccurate. Consider using '#align is_upper_set.mul_left IsUpperSet.mul_leftₓ'. -/
@[to_additive]
theorem IsUpperSet.mul_left (ht : IsUpperSet t) : IsUpperSet (s * t) :=
  by
  rw [← smul_eq_mul, ← bUnion_smul_set]
  exact isUpperSet_iUnion₂ fun x hx => ht.smul
#align is_upper_set.mul_left IsUpperSet.mul_left
#align is_upper_set.add_left IsUpperSet.add_left

/- warning: is_upper_set.mul_right -> IsUpperSet.mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t))
Case conversion may be inaccurate. Consider using '#align is_upper_set.mul_right IsUpperSet.mul_rightₓ'. -/
@[to_additive]
theorem IsUpperSet.mul_right (hs : IsUpperSet s) : IsUpperSet (s * t) :=
  by
  rw [mul_comm]
  exact hs.mul_left
#align is_upper_set.mul_right IsUpperSet.mul_right
#align is_upper_set.add_right IsUpperSet.add_right

/- warning: is_lower_set.mul_left -> IsLowerSet.mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) t) -> (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) t) -> (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t))
Case conversion may be inaccurate. Consider using '#align is_lower_set.mul_left IsLowerSet.mul_leftₓ'. -/
@[to_additive]
theorem IsLowerSet.mul_left (ht : IsLowerSet t) : IsLowerSet (s * t) :=
  ht.ofDual.mul_left
#align is_lower_set.mul_left IsLowerSet.mul_left
#align is_lower_set.add_left IsLowerSet.add_left

/- warning: is_lower_set.mul_right -> IsLowerSet.mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t))
Case conversion may be inaccurate. Consider using '#align is_lower_set.mul_right IsLowerSet.mul_rightₓ'. -/
@[to_additive]
theorem IsLowerSet.mul_right (hs : IsLowerSet s) : IsLowerSet (s * t) :=
  hs.ofDual.mul_right
#align is_lower_set.mul_right IsLowerSet.mul_right
#align is_lower_set.add_right IsLowerSet.add_right

/- warning: is_upper_set.inv -> IsUpperSet.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α}, (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α}, (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))) s))
Case conversion may be inaccurate. Consider using '#align is_upper_set.inv IsUpperSet.invₓ'. -/
@[to_additive]
theorem IsUpperSet.inv (hs : IsUpperSet s) : IsLowerSet s⁻¹ := fun x y h => hs <| inv_le_inv' h
#align is_upper_set.inv IsUpperSet.inv
#align is_upper_set.neg IsUpperSet.neg

/- warning: is_lower_set.inv -> IsLowerSet.inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α}, (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α}, (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (Inv.inv.{u1} (Set.{u1} α) (Set.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))) s))
Case conversion may be inaccurate. Consider using '#align is_lower_set.inv IsLowerSet.invₓ'. -/
@[to_additive]
theorem IsLowerSet.inv (hs : IsLowerSet s) : IsUpperSet s⁻¹ := fun x y h => hs <| inv_le_inv' h
#align is_lower_set.inv IsLowerSet.inv
#align is_lower_set.neg IsLowerSet.neg

/- warning: is_upper_set.div_left -> IsUpperSet.div_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) t) -> (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) t) -> (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) s t))
Case conversion may be inaccurate. Consider using '#align is_upper_set.div_left IsUpperSet.div_leftₓ'. -/
@[to_additive]
theorem IsUpperSet.div_left (ht : IsUpperSet t) : IsLowerSet (s / t) :=
  by
  rw [div_eq_mul_inv]
  exact ht.inv.mul_left
#align is_upper_set.div_left IsUpperSet.div_left
#align is_upper_set.sub_left IsUpperSet.sub_left

/- warning: is_upper_set.div_right -> IsUpperSet.div_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) s t))
Case conversion may be inaccurate. Consider using '#align is_upper_set.div_right IsUpperSet.div_rightₓ'. -/
@[to_additive]
theorem IsUpperSet.div_right (hs : IsUpperSet s) : IsUpperSet (s / t) :=
  by
  rw [div_eq_mul_inv]
  exact hs.mul_right
#align is_upper_set.div_right IsUpperSet.div_right
#align is_upper_set.sub_right IsUpperSet.sub_right

/- warning: is_lower_set.div_left -> IsLowerSet.div_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) t) -> (IsUpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) t) -> (IsUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) s t))
Case conversion may be inaccurate. Consider using '#align is_lower_set.div_left IsLowerSet.div_leftₓ'. -/
@[to_additive]
theorem IsLowerSet.div_left (ht : IsLowerSet t) : IsUpperSet (s / t) :=
  ht.ofDual.div_left
#align is_lower_set.div_left IsLowerSet.div_left
#align is_lower_set.sub_left IsLowerSet.sub_left

/- warning: is_lower_set.div_right -> IsLowerSet.div_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsLowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) s) -> (IsLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) s t))
Case conversion may be inaccurate. Consider using '#align is_lower_set.div_right IsLowerSet.div_rightₓ'. -/
@[to_additive]
theorem IsLowerSet.div_right (hs : IsLowerSet s) : IsLowerSet (s / t) :=
  hs.ofDual.div_right
#align is_lower_set.div_right IsLowerSet.div_right
#align is_lower_set.sub_right IsLowerSet.sub_right

namespace UpperSet

@[to_additive]
instance : One (UpperSet α) :=
  ⟨Ici 1⟩

@[to_additive]
instance : Mul (UpperSet α) :=
  ⟨fun s t => ⟨image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]
instance : Div (UpperSet α) :=
  ⟨fun s t => ⟨image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]
instance : SMul α (UpperSet α) :=
  ⟨fun a s => ⟨(· • ·) a '' s, s.2.smul⟩⟩

/- warning: upper_set.coe_one -> UpperSet.coe_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (OfNat.ofNat.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (OfNat.mk.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (One.one.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.hasOne.{u1} α _inst_1))))) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (OfNat.ofNat.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (One.toOfNat1.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.instOneUpperSetToLEToPreorderToPartialOrder.{u1} α _inst_1)))) (Set.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align upper_set.coe_one UpperSet.coe_oneₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_one : ((1 : UpperSet α) : Set α) = Set.Ici 1 :=
  rfl
#align upper_set.coe_one UpperSet.coe_one
#align upper_set.coe_zero UpperSet.coe_zero

@[simp, norm_cast, to_additive]
theorem coe_smul (a : α) (s : UpperSet α) : (↑(a • s) : Set α) = a • s :=
  rfl
#align upper_set.coe_smul UpperSet.coe_smul
#align upper_set.coe_vadd UpperSet.coe_vadd

/- warning: upper_set.coe_mul -> UpperSet.coe_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (t : UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHMul.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.hasMul.{u1} α _inst_1)) s t)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (t : UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHMul.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.instMulUpperSetToLEToPreorderToPartialOrder.{u1} α _inst_1)) s t)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) s) (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) t))
Case conversion may be inaccurate. Consider using '#align upper_set.coe_mul UpperSet.coe_mulₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_mul (s t : UpperSet α) : (↑(s * t) : Set α) = s * t :=
  rfl
#align upper_set.coe_mul UpperSet.coe_mul
#align upper_set.coe_add UpperSet.coe_add

/- warning: upper_set.coe_div -> UpperSet.coe_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (t : UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHDiv.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.hasDiv.{u1} α _inst_1)) s t)) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (t : UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHDiv.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.instDivUpperSetToLEToPreorderToPartialOrder.{u1} α _inst_1)) s t)) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) s) (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) t))
Case conversion may be inaccurate. Consider using '#align upper_set.coe_div UpperSet.coe_divₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_div (s t : UpperSet α) : (↑(s / t) : Set α) = s / t :=
  rfl
#align upper_set.coe_div UpperSet.coe_div
#align upper_set.coe_sub UpperSet.coe_sub

/- warning: upper_set.Ici_one -> UpperSet.Ici_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α], Eq.{succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))))) (OfNat.ofNat.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (OfNat.mk.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (One.one.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.hasOne.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α], Eq.{succ u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.Ici.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))) (OfNat.ofNat.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (One.toOfNat1.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.instOneUpperSetToLEToPreorderToPartialOrder.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align upper_set.Ici_one UpperSet.Ici_oneₓ'. -/
@[simp, to_additive]
theorem Ici_one : Ici (1 : α) = 1 :=
  rfl
#align upper_set.Ici_one UpperSet.Ici_one
#align upper_set.Ici_zero UpperSet.Ici_zero

@[to_additive]
instance : MulAction α (UpperSet α) :=
  SetLike.coe_injective.MulAction _ coe_smul

@[to_additive]
instance : CommSemigroup (UpperSet α) :=
  { (SetLike.coe_injective.CommSemigroup _ coe_mul : CommSemigroup (UpperSet α)) with
    mul := (· * ·) }

@[to_additive]
private theorem one_mul (s : UpperSet α) : 1 * s = s :=
  SetLike.coe_injective <|
    (subset_mul_right _ left_mem_Ici).antisymm' <|
      by
      rw [← smul_eq_mul, ← bUnion_smul_set]
      exact Union₂_subset fun _ => s.upper.smul_subset
#align upper_set.one_mul upper_set.one_mul

@[to_additive]
instance : CommMonoid (UpperSet α) :=
  { UpperSet.commSemigroup with
    one := 1
    one_mul := one_mul
    mul_one := fun s => by
      rw [mul_comm]
      exact one_mul _ }

end UpperSet

namespace LowerSet

@[to_additive]
instance : One (LowerSet α) :=
  ⟨Iic 1⟩

@[to_additive]
instance : Mul (LowerSet α) :=
  ⟨fun s t => ⟨image2 (· * ·) s t, s.2.mul_right⟩⟩

@[to_additive]
instance : Div (LowerSet α) :=
  ⟨fun s t => ⟨image2 (· / ·) s t, s.2.div_right⟩⟩

@[to_additive]
instance : SMul α (LowerSet α) :=
  ⟨fun a s => ⟨(· • ·) a '' s, s.2.smul⟩⟩

@[simp, norm_cast, to_additive]
theorem coe_smul (a : α) (s : LowerSet α) : (↑(a • s) : Set α) = a • s :=
  rfl
#align lower_set.coe_smul LowerSet.coe_smul
#align lower_set.coe_vadd LowerSet.coe_vadd

/- warning: lower_set.coe_mul -> LowerSet.coe_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (t : LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHMul.{u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.hasMul.{u1} α _inst_1)) s t)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (t : LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.instSetLikeLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (HMul.hMul.{u1, u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHMul.{u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.instMulLowerSetToLEToPreorderToPartialOrder.{u1} α _inst_1)) s t)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) (SetLike.coe.{u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.instSetLikeLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) s) (SetLike.coe.{u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.instSetLikeLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) t))
Case conversion may be inaccurate. Consider using '#align lower_set.coe_mul LowerSet.coe_mulₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_mul (s t : LowerSet α) : (↑(s * t) : Set α) = s * t :=
  rfl
#align lower_set.coe_mul LowerSet.coe_mul
#align lower_set.coe_add LowerSet.coe_add

/- warning: lower_set.coe_div -> LowerSet.coe_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (t : LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (HDiv.hDiv.{u1, u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHDiv.{u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.hasDiv.{u1} α _inst_1)) s t)) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (t : LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.instSetLikeLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (HDiv.hDiv.{u1, u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHDiv.{u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.instDivLowerSetToLEToPreorderToPartialOrder.{u1} α _inst_1)) s t)) (HDiv.hDiv.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHDiv.{u1} (Set.{u1} α) (Set.div.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))) (SetLike.coe.{u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.instSetLikeLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) s) (SetLike.coe.{u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.instSetLikeLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) t))
Case conversion may be inaccurate. Consider using '#align lower_set.coe_div LowerSet.coe_divₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_div (s t : LowerSet α) : (↑(s / t) : Set α) = s / t :=
  rfl
#align lower_set.coe_div LowerSet.coe_div
#align lower_set.coe_sub LowerSet.coe_sub

/- warning: lower_set.Iic_one -> LowerSet.Iic_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α], Eq.{succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))))) (OfNat.ofNat.{u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (OfNat.mk.{u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (One.one.{u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.hasOne.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α], Eq.{succ u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.Iic.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))) (OfNat.ofNat.{u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (One.toOfNat1.{u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.instOneLowerSetToLEToPreorderToPartialOrder.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align lower_set.Iic_one LowerSet.Iic_oneₓ'. -/
@[simp, to_additive]
theorem Iic_one : Iic (1 : α) = 1 :=
  rfl
#align lower_set.Iic_one LowerSet.Iic_one
#align lower_set.Iic_zero LowerSet.Iic_zero

@[to_additive]
instance : MulAction α (LowerSet α) :=
  SetLike.coe_injective.MulAction _ coe_smul

@[to_additive]
instance : CommSemigroup (LowerSet α) :=
  { (SetLike.coe_injective.CommSemigroup _ coe_mul : CommSemigroup (LowerSet α)) with
    mul := (· * ·) }

@[to_additive]
private theorem one_mul (s : LowerSet α) : 1 * s = s :=
  SetLike.coe_injective <|
    (subset_mul_right _ right_mem_Iic).antisymm' <|
      by
      rw [← smul_eq_mul, ← bUnion_smul_set]
      exact Union₂_subset fun _ => s.lower.smul_subset
#align lower_set.one_mul lower_set.one_mul

@[to_additive]
instance : CommMonoid (LowerSet α) :=
  { LowerSet.commSemigroup with
    one := 1
    one_mul := one_mul
    mul_one := fun s => by
      rw [mul_comm]
      exact one_mul _ }

end LowerSet

variable (a s t)

/- warning: upper_closure_one -> upperClosure_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α], Eq.{succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (OfNat.mk.{u1} (Set.{u1} α) 1 (One.one.{u1} (Set.{u1} α) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))))) (OfNat.ofNat.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (OfNat.mk.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (One.one.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.hasOne.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α], Eq.{succ u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (One.toOfNat1.{u1} (Set.{u1} α) (Set.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))))) (OfNat.ofNat.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (One.toOfNat1.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.instOneUpperSetToLEToPreorderToPartialOrder.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align upper_closure_one upperClosure_oneₓ'. -/
@[simp, to_additive]
theorem upperClosure_one : upperClosure (1 : Set α) = 1 :=
  upperClosure_singleton _
#align upper_closure_one upperClosure_one
#align upper_closure_zero upperClosure_zero

/- warning: lower_closure_one -> lowerClosure_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α], Eq.{succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (OfNat.mk.{u1} (Set.{u1} α) 1 (One.one.{u1} (Set.{u1} α) (Set.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1))))))))))) (OfNat.ofNat.{u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (OfNat.mk.{u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (One.one.{u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.hasOne.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α], Eq.{succ u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (OfNat.ofNat.{u1} (Set.{u1} α) 1 (One.toOfNat1.{u1} (Set.{u1} α) (Set.one.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))))) (OfNat.ofNat.{u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) 1 (One.toOfNat1.{u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.instOneLowerSetToLEToPreorderToPartialOrder.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align lower_closure_one lowerClosure_oneₓ'. -/
@[simp, to_additive]
theorem lowerClosure_one : lowerClosure (1 : Set α) = 1 :=
  lowerClosure_singleton _
#align lower_closure_one lowerClosure_one
#align lower_closure_zero lowerClosure_zero

/- warning: upper_closure_smul -> upperClosure_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (a : α), Eq.{succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a s)) (SMul.smul.{u1, u1} α (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.hasSmul.{u1} α _inst_1) a (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (a : α), Eq.{succ u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a s)) (HSMul.hSMul.{u1, u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHSMul.{u1, u1} α (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.instSMulUpperSetToLEToPreorderToPartialOrder.{u1} α _inst_1)) a (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align upper_closure_smul upperClosure_smulₓ'. -/
@[simp, to_additive]
theorem upperClosure_smul : upperClosure (a • s) = a • upperClosure s :=
  upperClosure_image <| OrderIso.mulLeft a
#align upper_closure_smul upperClosure_smul
#align upper_closure_vadd upperClosure_vadd

/- warning: lower_closure_smul -> lowerClosure_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (a : α), Eq.{succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a s)) (SMul.smul.{u1, u1} α (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.hasSmul.{u1} α _inst_1) a (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (a : α), Eq.{succ u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) a s)) (HSMul.hSMul.{u1, u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHSMul.{u1, u1} α (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.instSMulLowerSetToLEToPreorderToPartialOrder.{u1} α _inst_1)) a (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align lower_closure_smul lowerClosure_smulₓ'. -/
@[simp, to_additive]
theorem lowerClosure_smul : lowerClosure (a • s) = a • lowerClosure s :=
  lowerClosure_image <| OrderIso.mulLeft a
#align lower_closure_smul lowerClosure_smul
#align lower_closure_vadd lowerClosure_vadd

/- warning: mul_upper_closure -> mul_upperClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) t))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) t))) (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)))
Case conversion may be inaccurate. Consider using '#align mul_upper_closure mul_upperClosureₓ'. -/
@[to_additive]
theorem mul_upperClosure : s * upperClosure t = upperClosure (s * t) := by
  simp_rw [← smul_eq_mul, ← bUnion_smul_set, upperClosure_iUnion, upperClosure_smul,
    UpperSet.coe_iInf₂, UpperSet.coe_smul]
#align mul_upper_closure mul_upperClosure
#align add_upper_closure add_upperClosure

/- warning: mul_lower_closure -> mul_lowerClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) t))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s (SetLike.coe.{u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.instSetLikeLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) t))) (SetLike.coe.{u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.instSetLikeLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)))
Case conversion may be inaccurate. Consider using '#align mul_lower_closure mul_lowerClosureₓ'. -/
@[to_additive]
theorem mul_lowerClosure : s * lowerClosure t = lowerClosure (s * t) := by
  simp_rw [← smul_eq_mul, ← bUnion_smul_set, lowerClosure_iUnion, lowerClosure_smul,
    LowerSet.coe_iSup₂, LowerSet.coe_smul]
#align mul_lower_closure mul_lowerClosure
#align add_lower_closure add_lowerClosure

/- warning: upper_closure_mul -> upperClosure_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s)) t) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s)) t) (SetLike.coe.{u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (UpperSet.instSetLikeUpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)))
Case conversion may be inaccurate. Consider using '#align upper_closure_mul upperClosure_mulₓ'. -/
@[to_additive]
theorem upperClosure_mul : ↑(upperClosure s) * t = upperClosure (s * t) :=
  by
  simp_rw [mul_comm _ t]
  exact mul_upperClosure _ _
#align upper_closure_mul upperClosure_mul
#align upper_closure_add upperClosure_add

/- warning: lower_closure_mul -> lowerClosure_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s)) t) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.setLike.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1))))))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) (SetLike.coe.{u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.instSetLikeLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s)) t) (SetLike.coe.{u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) α (LowerSet.instSetLikeLowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)))
Case conversion may be inaccurate. Consider using '#align lower_closure_mul lowerClosure_mulₓ'. -/
@[to_additive]
theorem lowerClosure_mul : ↑(lowerClosure s) * t = lowerClosure (s * t) :=
  by
  simp_rw [mul_comm _ t]
  exact mul_lowerClosure _ _
#align lower_closure_mul lowerClosure_mul
#align lower_closure_add lowerClosure_add

/- warning: upper_closure_mul_distrib -> upperClosure_mul_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)) (HMul.hMul.{u1, u1, u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHMul.{u1} (UpperSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.hasMul.{u1} α _inst_1)) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)) (HMul.hMul.{u1, u1, u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHMul.{u1} (UpperSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (UpperSet.instMulUpperSetToLEToPreorderToPartialOrder.{u1} α _inst_1)) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s) (upperClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) t))
Case conversion may be inaccurate. Consider using '#align upper_closure_mul_distrib upperClosure_mul_distribₓ'. -/
@[simp, to_additive]
theorem upperClosure_mul_distrib : upperClosure (s * t) = upperClosure s * upperClosure t :=
  SetLike.coe_injective <| by
    rw [UpperSet.coe_mul, mul_upperClosure, upperClosure_mul, UpperSet.upperClosure]
#align upper_closure_mul_distrib upperClosure_mul_distrib
#align upper_closure_add_distrib upperClosure_add_distrib

/- warning: lower_closure_mul_distrib -> lowerClosure_mul_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)) (HMul.hMul.{u1, u1, u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHMul.{u1} (LowerSet.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.hasMul.{u1} α _inst_1)) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommGroup.{u1} α] (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α (OrderedCommGroup.toCommGroup.{u1} α _inst_1)))))))) s t)) (HMul.hMul.{u1, u1, u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (instHMul.{u1} (LowerSet.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)))) (LowerSet.instMulLowerSetToLEToPreorderToPartialOrder.{u1} α _inst_1)) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) s) (lowerClosure.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCommGroup.toPartialOrder.{u1} α _inst_1)) t))
Case conversion may be inaccurate. Consider using '#align lower_closure_mul_distrib lowerClosure_mul_distribₓ'. -/
@[simp, to_additive]
theorem lowerClosure_mul_distrib : lowerClosure (s * t) = lowerClosure s * lowerClosure t :=
  SetLike.coe_injective <| by
    rw [LowerSet.coe_mul, mul_lowerClosure, lowerClosure_mul, LowerSet.lowerClosure]
#align lower_closure_mul_distrib lowerClosure_mul_distrib
#align lower_closure_add_distrib lowerClosure_add_distrib

end OrderedCommGroup


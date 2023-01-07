/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module algebra.order.field.canonical.basic
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Field.Canonical.Defs

/-!
# Lemmas about canonically ordered semifields.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α : Type _}

section CanonicallyLinearOrderedSemifield

variable [CanonicallyLinearOrderedSemifield α] [Sub α] [OrderedSub α]

/- warning: tsub_div -> tsub_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedSemifield.{u1} α] [_inst_2 : Sub.{u1} α] [_inst_3 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedCancelAddCommMonoid.toPartialOrder.{u1} α (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{u1} α _inst_1)))))))) (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{u1} α _inst_1))))))))) _inst_2] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α (DivisionSemiring.toGroupWithZero.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{u1} α _inst_1))))))) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_2) a b) c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α (DivisionSemiring.toGroupWithZero.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{u1} α _inst_1))))))) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α (DivisionSemiring.toGroupWithZero.{u1} α (Semifield.toDivisionSemiring.{u1} α (LinearOrderedSemifield.toSemifield.{u1} α (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{u1} α _inst_1))))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyLinearOrderedSemifield.{u1} α] [_inst_2 : Sub.{u1} α] [_inst_3 : OrderedSub.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (StrictOrderedSemiring.toPartialOrder.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{u1} α _inst_1))))))) (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α (StrictOrderedSemiring.toSemiring.{u1} α (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} α (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} α (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} α (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{u1} α _inst_1))))))))) _inst_2] (a : α) (b : α) (c : α), Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (CanonicallyLinearOrderedSemifield.toDiv.{u1} α _inst_1)) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_2) a b) c) (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α _inst_2) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (CanonicallyLinearOrderedSemifield.toDiv.{u1} α _inst_1)) a c) (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (CanonicallyLinearOrderedSemifield.toDiv.{u1} α _inst_1)) b c))
Case conversion may be inaccurate. Consider using '#align tsub_div tsub_divₓ'. -/
theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
#align tsub_div tsub_div

end CanonicallyLinearOrderedSemifield


/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module algebra.order.field.canonical.defs
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Field.Defs
import Mathbin.Algebra.Order.Ring.Canonical
import Mathbin.Algebra.Order.WithZero

/-!
# Canonically ordered semifields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α : Type _}

#print CanonicallyLinearOrderedSemifield /-
/-- A canonically linear ordered field is a linear ordered field in which `a ≤ b` iff there exists
`c` with `b = a + c`. -/
@[protect_proj]
class CanonicallyLinearOrderedSemifield (α : Type _) extends CanonicallyOrderedCommSemiring α,
  LinearOrderedSemifield α
#align canonically_linear_ordered_semifield CanonicallyLinearOrderedSemifield
-/

#print CanonicallyLinearOrderedSemifield.toLinearOrderedCommGroupWithZero /-
-- See note [lower instance priority]
instance (priority := 100) CanonicallyLinearOrderedSemifield.toLinearOrderedCommGroupWithZero
    [CanonicallyLinearOrderedSemifield α] : LinearOrderedCommGroupWithZero α :=
  { ‹CanonicallyLinearOrderedSemifield α› with
    mul_le_mul_left := fun a b h c => mul_le_mul_of_nonneg_left h <| zero_le _ }
#align canonically_linear_ordered_semifield.to_linear_ordered_comm_group_with_zero CanonicallyLinearOrderedSemifield.toLinearOrderedCommGroupWithZero
-/

#print CanonicallyLinearOrderedSemifield.toCanonicallyLinearOrderedAddMonoid /-
-- See note [lower instance priority]
instance (priority := 100) CanonicallyLinearOrderedSemifield.toCanonicallyLinearOrderedAddMonoid
    [CanonicallyLinearOrderedSemifield α] : CanonicallyLinearOrderedAddMonoid α :=
  { ‹CanonicallyLinearOrderedSemifield α› with }
#align canonically_linear_ordered_semifield.to_canonically_linear_ordered_add_monoid CanonicallyLinearOrderedSemifield.toCanonicallyLinearOrderedAddMonoid
-/


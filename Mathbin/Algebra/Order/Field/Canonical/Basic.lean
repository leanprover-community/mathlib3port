/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathbin.Algebra.Order.Field.Canonical.Defs

#align_import algebra.order.field.canonical.basic from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Lemmas about canonically ordered semifields.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α : Type _}

section CanonicallyLinearOrderedSemifield

variable [CanonicallyLinearOrderedSemifield α] [Sub α] [OrderedSub α]

#print tsub_div /-
theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]
#align tsub_div tsub_div
-/

end CanonicallyLinearOrderedSemifield


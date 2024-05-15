/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Algebra.Field.Defs
import Algebra.GroupWithZero.Bitwise
import Algebra.Parity

#align_import algebra.field.power from "leanprover-community/mathlib"@"c3291da49cfa65f0d43b094750541c0731edc932"

/-!
# Results about powers in fields or division rings.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file exists to ensure we can define `field` with minimal imports,
so contains some lemmas about powers of elements which need imports
beyond those needed for the basic definition.
-/


variable {α : Type _}

section DivisionRing

variable [DivisionRing α] {n : ℤ}

#print zpow_bit1_neg /-
@[simp]
theorem zpow_bit1_neg (a : α) (n : ℤ) : (-a) ^ bit1 n = -a ^ bit1 n := by
  rw [zpow_bit1', zpow_bit1', neg_mul_neg, neg_mul_eq_mul_neg]
#align zpow_bit1_neg zpow_bit1_neg
-/

#print Odd.neg_zpow /-
theorem Odd.neg_zpow (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by obtain ⟨k, rfl⟩ := h.exists_bit1;
  exact zpow_bit1_neg _ _
#align odd.neg_zpow Odd.neg_zpow
-/

#print Odd.neg_one_zpow /-
theorem Odd.neg_one_zpow (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow, one_zpow]
#align odd.neg_one_zpow Odd.neg_one_zpow
-/

end DivisionRing


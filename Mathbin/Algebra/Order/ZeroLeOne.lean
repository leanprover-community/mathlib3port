/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Order.Basic
import Algebra.NeZero

#align_import algebra.order.zero_le_one from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Typeclass expressing `0 ≤ 1`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

open Function

#print ZeroLEOneClass /-
/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class ZeroLEOneClass (α : Type _) [Zero α] [One α] [LE α] where
  zero_le_one : (0 : α) ≤ 1
#align zero_le_one_class ZeroLEOneClass
-/

#print zero_le_one /-
/-- `zero_le_one` with the type argument implicit. -/
@[simp]
theorem zero_le_one [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  ZeroLEOneClass.zero_le_one
#align zero_le_one zero_le_one
-/

#print zero_le_one' /-
/-- `zero_le_one` with the type argument explicit. -/
theorem zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one
#align zero_le_one' zero_le_one'
-/

section

variable [Zero α] [One α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

#print zero_lt_one /-
/-- See `zero_lt_one'` for a version with the type explicit. -/
@[simp]
theorem zero_lt_one : (0 : α) < 1 :=
  zero_le_one.lt_of_ne (NeZero.ne' 1)
#align zero_lt_one zero_lt_one
-/

variable (α)

#print zero_lt_one' /-
/-- See `zero_lt_one` for a version with the type implicit. -/
theorem zero_lt_one' : (0 : α) < 1 :=
  zero_lt_one
#align zero_lt_one' zero_lt_one'
-/

end

alias one_pos := zero_lt_one
#align one_pos one_pos


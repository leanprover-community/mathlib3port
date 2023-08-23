/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao
-/
import Mathbin.Algebra.Order.Monoid.Lemmas
import Mathbin.Algebra.Order.ZeroLeOne
import Mathbin.Data.Nat.Cast.Defs

#align_import algebra.order.monoid.nat_cast from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Order of numerials in an `add_monoid_with_one`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

open Function

#print lt_add_one /-
theorem lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [CovariantClass α α (· + ·) (· < ·)] (a : α) : a < a + 1 :=
  lt_add_of_pos_right _ zero_lt_one
#align lt_add_one lt_add_one
-/

#print lt_one_add /-
theorem lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]
    [CovariantClass α α (swap (· + ·)) (· < ·)] (a : α) : a < 1 + a :=
  lt_add_of_pos_left _ zero_lt_one
#align lt_one_add lt_one_add
-/

variable [AddMonoidWithOne α]

#print zero_le_two /-
theorem zero_le_two [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 2 :=
  add_nonneg zero_le_one zero_le_one
#align zero_le_two zero_le_two
-/

#print zero_le_three /-
theorem zero_le_three [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 3 :=
  add_nonneg zero_le_two zero_le_one
#align zero_le_three zero_le_three
-/

#print zero_le_four /-
theorem zero_le_four [Preorder α] [ZeroLEOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] :
    (0 : α) ≤ 4 :=
  add_nonneg zero_le_two zero_le_two
#align zero_le_four zero_le_four
-/

#print one_le_two /-
theorem one_le_two [LE α] [ZeroLEOneClass α] [CovariantClass α α (· + ·) (· ≤ ·)] : (1 : α) ≤ 2 :=
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ ≤ 1 + 1 := add_le_add_left zero_le_one _
#align one_le_two one_le_two
-/

#print one_le_two' /-
theorem one_le_two' [LE α] [ZeroLEOneClass α] [CovariantClass α α (swap (· + ·)) (· ≤ ·)] :
    (1 : α) ≤ 2 :=
  calc
    1 = 0 + 1 := (zero_add 1).symm
    _ ≤ 1 + 1 := add_le_add_right zero_le_one _
#align one_le_two' one_le_two'
-/

section

variable [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

section

variable [CovariantClass α α (· + ·) (· ≤ ·)]

#print zero_lt_two /-
/-- See `zero_lt_two'` for a version with the type explicit. -/
@[simp]
theorem zero_lt_two : (0 : α) < 2 :=
  zero_lt_one.trans_le one_le_two
#align zero_lt_two zero_lt_two
-/

#print zero_lt_three /-
/-- See `zero_lt_three'` for a version with the type explicit. -/
@[simp]
theorem zero_lt_three : (0 : α) < 3 :=
  lt_add_of_lt_of_nonneg zero_lt_two zero_le_one
#align zero_lt_three zero_lt_three
-/

#print zero_lt_four /-
/-- See `zero_lt_four'` for a version with the type explicit. -/
@[simp]
theorem zero_lt_four : (0 : α) < 4 :=
  lt_add_of_lt_of_nonneg zero_lt_two zero_le_two
#align zero_lt_four zero_lt_four
-/

variable (α)

#print zero_lt_two' /-
/-- See `zero_lt_two` for a version with the type implicit. -/
theorem zero_lt_two' : (0 : α) < 2 :=
  zero_lt_two
#align zero_lt_two' zero_lt_two'
-/

#print zero_lt_three' /-
/-- See `zero_lt_three` for a version with the type implicit. -/
theorem zero_lt_three' : (0 : α) < 3 :=
  zero_lt_three
#align zero_lt_three' zero_lt_three'
-/

#print zero_lt_four' /-
/-- See `zero_lt_four` for a version with the type implicit. -/
theorem zero_lt_four' : (0 : α) < 4 :=
  zero_lt_four
#align zero_lt_four' zero_lt_four'
-/

instance ZeroLEOneClass.NeZero.two : NeZero (2 : α) :=
  ⟨zero_lt_two.ne'⟩
#align zero_le_one_class.ne_zero.two ZeroLEOneClass.NeZero.two

instance ZeroLEOneClass.NeZero.three : NeZero (3 : α) :=
  ⟨zero_lt_three.ne'⟩
#align zero_le_one_class.ne_zero.three ZeroLEOneClass.NeZero.three

instance ZeroLEOneClass.NeZero.four : NeZero (4 : α) :=
  ⟨zero_lt_four.ne'⟩
#align zero_le_one_class.ne_zero.four ZeroLEOneClass.NeZero.four

end

#print one_lt_two /-
theorem one_lt_two [CovariantClass α α (· + ·) (· < ·)] : (1 : α) < 2 :=
  lt_add_one _
#align one_lt_two one_lt_two
-/

end

alias two_pos := zero_lt_two
#align two_pos two_pos

alias three_pos := zero_lt_three
#align three_pos three_pos

alias four_pos := zero_lt_four
#align four_pos four_pos


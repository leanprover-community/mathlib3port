/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.zero_le_one
! leanprover-community/mathlib commit 198161d833f2c01498c39c266b0b3dbe2c7a8c07
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Basic
import Mathbin.Algebra.NeZero

/-!
# Typeclass expressing `0 ≤ 1`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/893
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

open Function

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class ZeroLeOneClass (α : Type _) [Zero α] [One α] [LE α] where
  zero_le_one : (0 : α) ≤ 1
#align zero_le_one_class ZeroLeOneClass

/-- `zero_le_one` with the type argument implicit. -/
@[simp]
theorem zero_le_one [Zero α] [One α] [LE α] [ZeroLeOneClass α] : (0 : α) ≤ 1 :=
  ZeroLeOneClass.zero_le_one
#align zero_le_one zero_le_one

/-- `zero_le_one` with the type argument explicit. -/
theorem zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLeOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one
#align zero_le_one' zero_le_one'

section

variable [Zero α] [One α] [PartialOrder α] [ZeroLeOneClass α] [NeZero (1 : α)]

/- warning: zero_lt_one -> zero_lt_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Zero.{u1} α] [_inst_2 : One.{u1} α] [_inst_3 : PartialOrder.{u1} α] [_inst_4 : ZeroLeOneClass.{u1} α _inst_1 _inst_2 (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3))] [_inst_5 : NeZero.{u1} α _inst_1 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_2)))], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_3)) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedSemiring.{u1} α] [_inst_2 : Nontrivial.{u1} α], LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (OrderedSemiring.toPartialOrder.{u1} α _inst_1))) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Semiring.toOne.{u1} α (OrderedSemiring.toSemiring.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align zero_lt_one zero_lt_oneₓ'. -/
/-- See `zero_lt_one'` for a version with the type explicit. -/
@[simp]
theorem zero_lt_one : (0 : α) < 1 :=
  zero_le_one.lt_of_ne (NeZero.ne' 1)
#align zero_lt_one zero_lt_one

variable (α)

/-- See `zero_lt_one` for a version with the type implicit. -/
theorem zero_lt_one' : (0 : α) < 1 :=
  zero_lt_one
#align zero_lt_one' zero_lt_one'

end

alias zero_lt_one ← one_pos


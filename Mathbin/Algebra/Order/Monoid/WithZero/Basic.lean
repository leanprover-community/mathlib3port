/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Algebra.Order.Monoid.WithZero
import Algebra.GroupWithZero.Basic

#align_import algebra.order.monoid.with_zero.basic from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# An instance orphaned from `algebra.order.monoid.with_zero.defs`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We put this here to minimise imports: if you can move it back into
`algebra.order.monoid.with_zero.defs` without increasing imports, please do.
-/


open Function

universe u

variable {α : Type u}

namespace WithZero

#print WithZero.contravariantClass_mul_lt /-
instance contravariantClass_mul_lt {α : Type u} [Mul α] [PartialOrder α]
    [ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass (WithZero α) (WithZero α) (· * ·) (· < ·) :=
  by
  refine' ⟨fun a b c h => _⟩
  have := ((zero_le _).trans_lt h).ne'
  lift a to α using left_ne_zero_of_mul this
  lift c to α using right_ne_zero_of_mul this
  induction b using WithZero.recZeroCoe
  exacts [zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]
#align with_zero.contravariant_class_mul_lt WithZero.contravariantClass_mul_lt
-/

end WithZero


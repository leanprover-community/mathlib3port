/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.with_zero.basic
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Monoid.WithZero.Defs
import Mathbin.Algebra.GroupWithZero.Basic

/-!
# An instance orphaned from `algebra.order.monoid.with_zero.defs`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/851
> Any changes to this file require a corresponding PR to mathlib4.

We put this here to minimise imports: if you can move it back into
`algebra.order.monoid.with_zero.defs` without increasing imports, please do.
-/


open Function

universe u

variable {α : Type u}

namespace WithZero

/- warning: with_zero.contravariant_class_mul_lt -> WithZero.contravariantClass_mul_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1)) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)))], ContravariantClass.{u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (HMul.hMul.{u1, u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (WithZero.{u1} α) (instHMul.{u1} (WithZero.{u1} α) (MulZeroClass.toHasMul.{u1} (WithZero.{u1} α) (WithZero.mulZeroClass.{u1} α _inst_1)))) (LT.lt.{u1} (WithZero.{u1} α) (Preorder.toLT.{u1} (WithZero.{u1} α) (WithZero.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Mul.{u1} α] [_inst_2 : PartialOrder.{u1} α] [_inst_3 : ContravariantClass.{u1, u1} α α (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.24 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.26 : α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α _inst_1) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.24 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.26) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.39 : α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.41 : α) => LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2)) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.39 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.41)], ContravariantClass.{u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.63 : WithZero.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.65 : WithZero.{u1} α) => HMul.hMul.{u1, u1, u1} (WithZero.{u1} α) (WithZero.{u1} α) (WithZero.{u1} α) (instHMul.{u1} (WithZero.{u1} α) (MulZeroClass.toMul.{u1} (WithZero.{u1} α) (WithZero.mulZeroClass.{u1} α _inst_1))) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.63 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.65) (fun (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.78 : WithZero.{u1} α) (x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.80 : WithZero.{u1} α) => LT.lt.{u1} (WithZero.{u1} α) (Preorder.toLT.{u1} (WithZero.{u1} α) (WithZero.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_2))) x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.78 x._@.Mathlib.Algebra.Order.Monoid.WithZero.Basic._hyg.80)
Case conversion may be inaccurate. Consider using '#align with_zero.contravariant_class_mul_lt WithZero.contravariantClass_mul_ltₓ'. -/
instance contravariantClass_mul_lt {α : Type u} [Mul α] [PartialOrder α]
    [ContravariantClass α α (· * ·) (· < ·)] :
    ContravariantClass (WithZero α) (WithZero α) (· * ·) (· < ·) :=
  by
  refine' ⟨fun a b c h => _⟩
  have := ((zero_le _).trans_lt h).ne'
  lift a to α using left_ne_zero_of_mul this
  lift c to α using right_ne_zero_of_mul this
  induction b using WithZero.recZeroCoe
  exacts[zero_lt_coe _, coe_lt_coe.mpr (lt_of_mul_lt_mul_left' <| coe_lt_coe.mp h)]
#align with_zero.contravariant_class_mul_lt WithZero.contravariantClass_mul_lt

end WithZero


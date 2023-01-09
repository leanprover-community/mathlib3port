/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.cancel.basic
! leanprover-community/mathlib commit 40acfb6aa7516ffe6f91136691df012a64683390
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Monoid.Basic
import Mathbin.Algebra.Order.Monoid.Cancel.Defs

/-!
# Basic results on ordered cancellative monoids.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We pull back ordered cancellative monoids along injective maps.
-/


universe u

variable {α : Type u}

open Function

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α]

/- warning: function.injective.ordered_cancel_comm_monoid -> Function.Injective.orderedCancelCommMonoid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Pow.{u2, 0} β Nat] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_2)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1)))))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1))))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1)))))) (f x) n)) -> (OrderedCancelCommMonoid.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCancelCommMonoid.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Pow.{u2, 0} β Nat] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_2))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (RightCancelMonoid.toOne.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1))))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α _inst_1)))))) (f x) n)) -> (OrderedCancelCommMonoid.{u2} β)
Case conversion may be inaccurate. Consider using '#align function.injective.ordered_cancel_comm_monoid Function.Injective.orderedCancelCommMonoidₓ'. -/
/-- Pullback an `ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.orderedCancelAddCommMonoid
      "Pullback an `ordered_cancel_add_comm_monoid` under an injective map."]
def Function.Injective.orderedCancelCommMonoid {β : Type _} [One β] [Mul β] [Pow β ℕ] (f : β → α)
    (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : OrderedCancelCommMonoid β :=
  { hf.OrderedCommMonoid f one mul npow with
    le_of_mul_le_mul_left := fun a b c (bc : f (a * b) ≤ f (a * c)) =>
      (mul_le_mul_iff_left (f a)).mp (by rwa [← mul, ← mul]) }
#align function.injective.ordered_cancel_comm_monoid Function.Injective.orderedCancelCommMonoid

end OrderedCancelCommMonoid

section LinearOrderedCancelCommMonoid

variable [LinearOrderedCancelCommMonoid α]

/- warning: function.injective.linear_ordered_cancel_comm_monoid -> Function.Injective.linearOrderedCancelCommMonoid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCancelCommMonoid.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Pow.{u2, 0} β Nat] [_inst_5 : HasSup.{u2} β] [_inst_6 : HasInf.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_2)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1))))))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1)))))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1))))))) (f x) n)) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HasSup.sup.{u2} β _inst_5 x y)) (LinearOrder.max.{u1} α (LinearOrderedCommMonoid.toLinearOrder.{u1} α (LinearOrderedCancelCommMonoid.toLinearOrderedCommMonoid.{u1} α _inst_1)) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HasInf.inf.{u2} β _inst_6 x y)) (LinearOrder.min.{u1} α (LinearOrderedCommMonoid.toLinearOrder.{u1} α (LinearOrderedCancelCommMonoid.toLinearOrderedCommMonoid.{u1} α _inst_1)) (f x) (f y))) -> (LinearOrderedCancelCommMonoid.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCancelCommMonoid.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Pow.{u2, 0} β Nat] [_inst_5 : HasSup.{u2} β] [_inst_6 : HasInf.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_2))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (RightCancelMonoid.toOne.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1)))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1)))))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (RightCancelMonoid.toMonoid.{u1} α (CancelMonoid.toRightCancelMonoid.{u1} α (CancelCommMonoid.toCancelMonoid.{u1} α (OrderedCancelCommMonoid.toCancelCommMonoid.{u1} α (LinearOrderedCancelCommMonoid.toOrderedCancelCommMonoid.{u1} α _inst_1))))))) (f x) n)) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HasSup.sup.{u2} β _inst_5 x y)) (Max.max.{u1} α (LinearOrderedCancelCommMonoid.toMax.{u1} α _inst_1) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HasInf.inf.{u2} β _inst_6 x y)) (Min.min.{u1} α (LinearOrderedCancelCommMonoid.toMin.{u1} α _inst_1) (f x) (f y))) -> (LinearOrderedCancelCommMonoid.{u2} β)
Case conversion may be inaccurate. Consider using '#align function.injective.linear_ordered_cancel_comm_monoid Function.Injective.linearOrderedCancelCommMonoidₓ'. -/
/-- Pullback a `linear_ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedCancelAddCommMonoid
      "Pullback a `linear_ordered_cancel_add_comm_monoid` under an injective map."]
def Function.Injective.linearOrderedCancelCommMonoid {β : Type _} [One β] [Mul β] [Pow β ℕ]
    [HasSup β] [HasInf β] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCancelCommMonoid β :=
  { hf.LinearOrderedCommMonoid f one mul npow hsup hinf,
    hf.OrderedCancelCommMonoid f one mul npow with }
#align
  function.injective.linear_ordered_cancel_comm_monoid Function.Injective.linearOrderedCancelCommMonoid

end LinearOrderedCancelCommMonoid


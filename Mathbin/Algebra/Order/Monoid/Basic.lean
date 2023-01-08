/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.monoid.basic
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Monoid.Defs
import Mathbin.Algebra.Group.InjSurj
import Mathbin.Order.Hom.Basic

/-!
# Ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file develops some additional material on ordered monoids.
-/


open Function

universe u

variable {α : Type u} {β : Type _}

/- warning: function.injective.ordered_comm_monoid -> Function.Injective.orderedCommMonoid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Pow.{u2, 0} β Nat] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_2)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))) (f x) n)) -> (OrderedCommMonoid.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : OrderedCommMonoid.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Pow.{u2, 0} β Nat] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_2))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))) (f x) n)) -> (OrderedCommMonoid.{u2} β)
Case conversion may be inaccurate. Consider using '#align function.injective.ordered_comm_monoid Function.Injective.orderedCommMonoidₓ'. -/
/-- Pullback an `ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.orderedAddCommMonoid
      "Pullback an `ordered_add_comm_monoid` under an injective map."]
def Function.Injective.orderedCommMonoid [OrderedCommMonoid α] {β : Type _} [One β] [Mul β]
    [Pow β ℕ] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    OrderedCommMonoid β :=
  { PartialOrder.lift f hf, hf.CommMonoid f one mul npow with
    mul_le_mul_left := fun a b ab c =>
      show f (c * a) ≤ f (c * b) by
        rw [mul, mul]
        apply mul_le_mul_left'
        exact ab }
#align function.injective.ordered_comm_monoid Function.Injective.orderedCommMonoid

/- warning: function.injective.linear_ordered_comm_monoid -> Function.Injective.linearOrderedCommMonoid is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommMonoid.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Pow.{u2, 0} β Nat] [_inst_5 : HasSup.{u2} β] [_inst_6 : HasInf.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_2)))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} α _inst_1)))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (LinearOrderedCommMonoid.toOrderedCommMonoid.{u1} α _inst_1))))) (f x) n)) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HasSup.sup.{u2} β _inst_5 x y)) (LinearOrder.max.{u1} α (LinearOrderedCommMonoid.toLinearOrder.{u1} α _inst_1) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HasInf.inf.{u2} β _inst_6 x y)) (LinearOrder.min.{u1} α (LinearOrderedCommMonoid.toLinearOrder.{u1} α _inst_1) (f x) (f y))) -> (LinearOrderedCommMonoid.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LinearOrderedCommMonoid.{u1} α] {β : Type.{u2}} [_inst_2 : One.{u2} β] [_inst_3 : Mul.{u2} β] [_inst_4 : Pow.{u2, 0} β Nat] [_inst_5 : HasSup.{u2} β] [_inst_6 : HasInf.{u2} β] (f : β -> α), (Function.Injective.{succ u2, succ u1} β α f) -> (Eq.{succ u1} α (f (OfNat.ofNat.{u2} β 1 (One.toOfNat1.{u2} β _inst_2))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (LinearOrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HMul.hMul.{u2, u2, u2} β β β (instHMul.{u2} β _inst_3) x y)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (LinearOrderedCommMonoid.toCommMonoid.{u1} α _inst_1))))) (f x) (f y))) -> (forall (x : β) (n : Nat), Eq.{succ u1} α (f (HPow.hPow.{u2, 0, u2} β Nat β (instHPow.{u2, 0} β Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} α Nat α (instHPow.{u1, 0} α Nat (Monoid.Pow.{u1} α (CommMonoid.toMonoid.{u1} α (LinearOrderedCommMonoid.toCommMonoid.{u1} α _inst_1)))) (f x) n)) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HasSup.sup.{u2} β _inst_5 x y)) (Max.max.{u1} α (LinearOrder.toMax.{u1} α (LinearOrderedCommMonoid.toLinearOrder.{u1} α _inst_1)) (f x) (f y))) -> (forall (x : β) (y : β), Eq.{succ u1} α (f (HasInf.inf.{u2} β _inst_6 x y)) (Min.min.{u1} α (LinearOrder.toMin.{u1} α (LinearOrderedCommMonoid.toLinearOrder.{u1} α _inst_1)) (f x) (f y))) -> (LinearOrderedCommMonoid.{u2} β)
Case conversion may be inaccurate. Consider using '#align function.injective.linear_ordered_comm_monoid Function.Injective.linearOrderedCommMonoidₓ'. -/
/-- Pullback a `linear_ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedAddCommMonoid
      "Pullback an `ordered_add_comm_monoid` under an injective map."]
def Function.Injective.linearOrderedCommMonoid [LinearOrderedCommMonoid α] {β : Type _} [One β]
    [Mul β] [Pow β ℕ] [HasSup β] [HasInf β] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommMonoid β :=
  { hf.OrderedCommMonoid f one mul npow, LinearOrder.lift f hf hsup hinf with }
#align function.injective.linear_ordered_comm_monoid Function.Injective.linearOrderedCommMonoid

#print OrderEmbedding.mulLeft /-
-- TODO find a better home for the next two constructions.
/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `order_iso.mul_left` when working in an ordered group. -/
@[to_additive
      "The order embedding sending `b` to `a + b`, for some fixed `a`.\n  See also `order_iso.add_left` when working in an additive ordered group.",
  simps]
def OrderEmbedding.mulLeft {α : Type _} [Mul α] [LinearOrder α] [CovariantClass α α (· * ·) (· < ·)]
    (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) fun a b w => mul_lt_mul_left' w m
#align order_embedding.mul_left OrderEmbedding.mulLeft
-/

#print OrderEmbedding.mulRight /-
/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `order_iso.mul_right` when working in an ordered group. -/
@[to_additive
      "The order embedding sending `b` to `b + a`, for some fixed `a`.\n  See also `order_iso.add_right` when working in an additive ordered group.",
  simps]
def OrderEmbedding.mulRight {α : Type _} [Mul α] [LinearOrder α]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) fun a b w => mul_lt_mul_right' w m
#align order_embedding.mul_right OrderEmbedding.mulRight
-/


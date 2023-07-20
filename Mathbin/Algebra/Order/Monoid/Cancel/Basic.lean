/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Monoid.Basic
import Mathbin.Algebra.Order.Monoid.Cancel.Defs

#align_import algebra.order.monoid.cancel.basic from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

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

#print Function.Injective.orderedCancelCommMonoid /-
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
#align function.injective.ordered_cancel_add_comm_monoid Function.Injective.orderedCancelAddCommMonoid
-/

end OrderedCancelCommMonoid

section LinearOrderedCancelCommMonoid

variable [LinearOrderedCancelCommMonoid α]

#print Function.Injective.linearOrderedCancelCommMonoid /-
/-- Pullback a `linear_ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedCancelAddCommMonoid
      "Pullback a `linear_ordered_cancel_add_comm_monoid` under an injective map."]
def Function.Injective.linearOrderedCancelCommMonoid {β : Type _} [One β] [Mul β] [Pow β ℕ] [Sup β]
    [Inf β] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCancelCommMonoid β :=
  { hf.LinearOrderedCommMonoid f one mul npow hsup hinf,
    hf.OrderedCancelCommMonoid f one mul npow with }
#align function.injective.linear_ordered_cancel_comm_monoid Function.Injective.linearOrderedCancelCommMonoid
#align function.injective.linear_ordered_cancel_add_comm_monoid Function.Injective.linearOrderedCancelAddCommMonoid
-/

end LinearOrderedCancelCommMonoid


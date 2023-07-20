/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Group.Defs
import Mathbin.Algebra.Order.Monoid.Basic
import Mathbin.Algebra.Order.Group.Instances

#align_import algebra.order.group.inj_surj from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Pull back ordered groups along injective maps.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α β : Type _}

#print Function.Injective.orderedCommGroup /-
/-- Pullback an `ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.orderedAddCommGroup
      "Pullback an `ordered_add_comm_group` under an injective map."]
def Function.Injective.orderedCommGroup [OrderedCommGroup α] {β : Type _} [One β] [Mul β] [Inv β]
    [Div β] [Pow β ℕ] [Pow β ℤ] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : OrderedCommGroup β :=
  { PartialOrder.lift f hf, hf.OrderedCommMonoid f one mul npow,
    hf.CommGroup f one mul inv div npow zpow with }
#align function.injective.ordered_comm_group Function.Injective.orderedCommGroup
#align function.injective.ordered_add_comm_group Function.Injective.orderedAddCommGroup
-/

#print Function.Injective.linearOrderedCommGroup /-
/-- Pullback a `linear_ordered_comm_group` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedAddCommGroup
      "Pullback a `linear_ordered_add_comm_group` under an injective map."]
def Function.Injective.linearOrderedCommGroup [LinearOrderedCommGroup α] {β : Type _} [One β]
    [Mul β] [Inv β] [Div β] [Pow β ℕ] [Pow β ℤ] [Sup β] [Inf β] (f : β → α)
    (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommGroup β :=
  { LinearOrder.lift f hf hsup hinf, hf.OrderedCommGroup f one mul inv div npow zpow with }
#align function.injective.linear_ordered_comm_group Function.Injective.linearOrderedCommGroup
#align function.injective.linear_ordered_add_comm_group Function.Injective.linearOrderedAddCommGroup
-/


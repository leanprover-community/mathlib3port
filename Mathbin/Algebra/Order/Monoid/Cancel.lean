/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Monoid.Basic

/-!
# Ordered cancellative monoids
-/


universe u

variable {α : Type u}

open Function

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
@[protect_proj]
class OrderedCancelAddCommMonoid (α : Type u) extends AddCommMonoid α, PartialOrder α where
  add_le_add_left : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b
  le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[protect_proj, to_additive]
class OrderedCancelCommMonoid (α : Type u) extends CommMonoid α, PartialOrder α where
  mul_le_mul_left : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b
  le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] {a b c d : α}

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 200) OrderedCancelCommMonoid.to_contravariant_class_le_left :
    ContravariantClass α α (· * ·) (· ≤ ·) :=
  ⟨OrderedCancelCommMonoid.le_of_mul_le_mul_left⟩

@[to_additive]
theorem OrderedCancelCommMonoid.lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c := fun a b c h =>
  lt_of_le_not_le (OrderedCancelCommMonoid.le_of_mul_le_mul_left a b c h.le) <|
    mt (fun h => OrderedCancelCommMonoid.mul_le_mul_left _ _ h _) (not_le_of_gt h)

@[to_additive]
instance OrderedCancelCommMonoid.to_contravariant_class_left (M : Type _) [OrderedCancelCommMonoid M] :
    ContravariantClass M M (· * ·) (· < ·) where elim a b c := OrderedCancelCommMonoid.lt_of_mul_lt_mul_left _ _ _

/- This instance can be proven with `by apply_instance`.  However, by analogy with the
instance `ordered_cancel_comm_monoid.to_covariant_class_right` above, I imagine that without
this instance, some Type would not have a `contravariant_class M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance OrderedCancelCommMonoid.to_contravariant_class_right (M : Type _) [OrderedCancelCommMonoid M] :
    ContravariantClass M M (swap (· * ·)) (· < ·) :=
  contravariant_swap_mul_lt_of_contravariant_mul_lt M

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toOrderedCommMonoid : OrderedCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) OrderedCancelCommMonoid.toCancelCommMonoid : CancelCommMonoid α :=
  { ‹OrderedCancelCommMonoid α› with
    mul_left_cancel := fun a b c h => (le_of_mul_le_mul_left' h.le).antisymm <| le_of_mul_le_mul_left' h.ge }

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

end OrderedCancelCommMonoid

/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
@[protect_proj]
class LinearOrderedCancelAddCommMonoid (α : Type u) extends OrderedCancelAddCommMonoid α, LinearOrderedAddCommMonoid α

/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[protect_proj, to_additive]
class LinearOrderedCancelCommMonoid (α : Type u) extends OrderedCancelCommMonoid α, LinearOrderedCommMonoid α

section LinearOrderedCancelCommMonoid

variable [LinearOrderedCancelCommMonoid α]

/-- Pullback a `linear_ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible,
  to_additive Function.Injective.linearOrderedCancelAddCommMonoid
      "Pullback a `linear_ordered_cancel_add_comm_monoid` under an injective map."]
def Function.Injective.linearOrderedCancelCommMonoid {β : Type _} [One β] [Mul β] [Pow β ℕ] [HasSup β] [HasInf β]
    (f : β → α) (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) : LinearOrderedCancelCommMonoid β :=
  { hf.LinearOrderedCommMonoid f one mul npow hsup hinf, hf.OrderedCancelCommMonoid f one mul npow with }

end LinearOrderedCancelCommMonoid


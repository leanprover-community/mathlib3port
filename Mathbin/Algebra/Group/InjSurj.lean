/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Logic.Function.Basic

/-!
# Lifting algebraic data classes along injective/surjective maps

This file provides definitions that are meant to deal with
situations such as the following:

Suppose that `G` is a group, and `H` is a type endowed with
`has_one H`, `has_mul H`, and `has_inv H`.
Suppose furthermore, that `f : G → H` is a surjective map
that respects the multiplication, and the unit elements.
Then `H` satisfies the group axioms.

The relevant definition in this case is `function.surjective.group`.
Dually, there is also `function.injective.group`.
And there are versions for (additive) (commutative) semigroups/monoids.
-/


namespace Function

/-!
### Injective
-/


namespace Injective

variable {M₁ : Type _} {M₂ : Type _} [Mul M₁]

/-- A type endowed with `*` is a semigroup,
if it admits an injective map that preserves `*` to a semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `+` is an additive semigroup,\nif it admits an injective map that preserves `+` to an additive semigroup."]
protected def semigroup [Semigroupₓ M₂] (f : M₁ → M₂) (hf : Injective f) (mul : ∀ x y, f (x * y) = f x * f y) :
    Semigroupₓ M₁ :=
  { ‹Mul M₁› with
    mul_assoc := fun x y z =>
      hf <| by
        erw [mul, mul, mul, mul, mul_assoc] }

/-- A type endowed with `*` is a commutative semigroup,
if it admits an injective map that preserves `*` to a commutative semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `+` is an additive commutative semigroup,\nif it admits an injective map that preserves `+` to an additive commutative semigroup."]
protected def commSemigroup [CommSemigroupₓ M₂] (f : M₁ → M₂) (hf : Injective f) (mul : ∀ x y, f (x * y) = f x * f y) :
    CommSemigroupₓ M₁ :=
  { hf.Semigroup f mul with
    mul_comm := fun x y =>
      hf <| by
        erw [mul, mul, mul_comm] }

/-- A type endowed with `*` is a left cancel semigroup,
if it admits an injective map that preserves `*` to a left cancel semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddLeftCancelSemigroup
      "A type endowed with `+` is an additive left cancel semigroup,\nif it admits an injective map that preserves `+` to an additive left cancel semigroup."]
protected def leftCancelSemigroup [LeftCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftCancelSemigroup M₁ :=
  { hf.Semigroup f mul with mul := (· * ·),
    mul_left_cancel := fun x y z H =>
      hf <|
        (mul_right_injₓ (f x)).1 <| by
          erw [← mul, ← mul, H] <;> rfl }

/-- A type endowed with `*` is a right cancel semigroup,
if it admits an injective map that preserves `*` to a right cancel semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddRightCancelSemigroup
      "A type endowed with `+` is an additive right cancel semigroup,\nif it admits an injective map that preserves `+` to an additive right cancel semigroup."]
protected def rightCancelSemigroup [RightCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightCancelSemigroup M₁ :=
  { hf.Semigroup f mul with mul := (· * ·),
    mul_right_cancel := fun x y z H =>
      hf <|
        (mul_left_injₓ (f y)).1 <| by
          erw [← mul, ← mul, H] <;> rfl }

variable [One M₁]

/-- A type endowed with `1` and `*` is a mul_one_class,
if it admits an injective map that preserves `1` and `*` to a mul_one_class.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an add_zero_class,\nif it admits an injective map that preserves `0` and `+` to an add_zero_class."]
protected def mulOneClass [MulOneClassₓ M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClassₓ M₁ :=
  { ‹One M₁›, ‹Mul M₁› with
    one_mul := fun x =>
      hf <| by
        erw [mul, one, one_mulₓ],
    mul_one := fun x =>
      hf <| by
        erw [mul, one, mul_oneₓ] }

/-- A type endowed with `1` and `*` is a monoid,
if it admits an injective map that preserves `1` and `*` to a monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive monoid,\nif it admits an injective map that preserves `0` and `+` to an additive monoid."]
protected def monoid [Monoidₓ M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : Monoidₓ M₁ :=
  { hf.Semigroup f mul, hf.MulOneClass f one mul with }

/-- A type endowed with `1` and `*` is a monoid,
if it admits an injective map that preserves `1` and `*` to a monoid.
This version takes a custom `npow` as a `[has_pow M₁ ℕ]` argument.
See note [reducible non-instances]. -/
@[reducible,
  to_additive add_monoid_smul
      "A type endowed with `0` and `+` is an additive monoid,\nif it admits an injective map that preserves `0` and `+` to an additive monoid.\nThis version takes a custom `nsmul` as a `[has_scalar ℕ M₁]` argument."]
protected def monoidPow [Pow M₁ ℕ] [Monoidₓ M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) : Monoidₓ M₁ :=
  { hf.Monoid f one mul with npow := fun n x => x ^ n,
    npow_zero' := fun x =>
      hf <| by
        erw [npow, one, pow_zeroₓ],
    npow_succ' := fun n x =>
      hf <| by
        erw [npow, pow_succₓ, mul, npow] }

/-- A type endowed with `1` and `*` is a left cancel monoid,
if it admits an injective map that preserves `1` and `*` to a left cancel monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddLeftCancelMonoid
      "A type endowed with `0` and `+` is an additive left cancel monoid,\nif it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def leftCancelMonoid [LeftCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftCancelMonoid M₁ :=
  { hf.LeftCancelSemigroup f mul, hf.Monoid f one mul with }

/-- A type endowed with `1` and `*` is a right cancel monoid,
if it admits an injective map that preserves `1` and `*` to a right cancel monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddRightCancelMonoid
      "A type endowed with `0` and `+` is an additive left cancel monoid,\nif it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def rightCancelMonoid [RightCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightCancelMonoid M₁ :=
  { hf.RightCancelSemigroup f mul, hf.Monoid f one mul with }

/-- A type endowed with `1` and `*` is a cancel monoid,
if it admits an injective map that preserves `1` and `*` to a cancel monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddCancelMonoid
      "A type endowed with `0` and `+` is an additive left cancel monoid,\nif it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def cancelMonoid [CancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : CancelMonoid M₁ :=
  { hf.LeftCancelMonoid f one mul, hf.RightCancelMonoid f one mul with }

/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits an injective map that preserves `1` and `*` to a commutative monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive commutative monoid,\nif it admits an injective map that preserves `0` and `+` to an additive commutative monoid."]
protected def commMonoid [CommMonoidₓ M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommMonoidₓ M₁ :=
  { hf.CommSemigroup f mul, hf.Monoid f one mul with }

/-- A type endowed with `1` and `*` is a cancel commutative monoid,
if it admits an injective map that preserves `1` and `*` to a cancel commutative monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddCancelCommMonoid
      "A type endowed with `0` and `+` is an additive cancel commutative monoid,\nif it admits an injective map that preserves `0` and `+` to an additive cancel commutative monoid."]
protected def cancelCommMonoid [CancelCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : CancelCommMonoid M₁ :=
  { hf.LeftCancelSemigroup f mul, hf.CommMonoid f one mul with }

variable [Inv M₁] [Div M₁]

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits an injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`.
See note [reducible non-instances]. -/
@[reducible,
  to_additive SubNegMonoidₓ
      "A type endowed with `0`, `+`, unary `-`, and binary `-` is a `sub_neg_monoid`\nif it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to\na `sub_neg_monoid`."]
protected def divInvMonoid [DivInvMonoidₓ M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) :
    DivInvMonoidₓ M₁ :=
  { hf.Monoid f one mul, ‹Inv M₁›, ‹Div M₁› with
    div_eq_mul_inv := fun x y =>
      hf <| by
        erw [div, mul, inv, div_eq_mul_inv] }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits an injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`.
This version takes custom `npow` and `zpow` as `[has_pow M₁ ℕ]` and `[has_pow M₁ ℤ]` arguments.
See note [reducible non-instances]. -/
@[reducible,
  to_additive sub_neg_monoid_smul
      "A type endowed with `0`, `+`, unary `-`, and binary `-` is a `sub_neg_monoid`\nif it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to\na `sub_neg_monoid`.\nThis version takes custom `nsmul` and `zsmul` as `[has_scalar ℕ M₁]` and\n`[has_scalar ℤ M₁]` arguments."]
protected def divInvMonoidPow [Pow M₁ ℕ] [Pow M₁ ℤ] [DivInvMonoidₓ M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) (zpow : ∀ x n : ℤ, f (x ^ n) = f x ^ n) : DivInvMonoidₓ M₁ :=
  { hf.monoidPow f one mul npow, hf.DivInvMonoid f one mul inv div with zpow := fun n x => x ^ n,
    zpow_zero' := fun x =>
      hf <| by
        erw [zpow, zpow_zero, one],
    zpow_succ' := fun n x =>
      hf <| by
        erw [zpow, mul, zpow_of_nat, pow_succₓ, zpow, zpow_of_nat],
    zpow_neg' := fun n x =>
      hf <| by
        erw [zpow, zpow_neg_succ_of_nat, inv, zpow, zpow_coe_nat] }

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a group.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive group,\nif it admits an injective map that preserves `0` and `+` to an additive group."]
protected def group [Groupₓ M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) : Groupₓ M₁ :=
  { hf.DivInvMonoid f one mul inv div with
    mul_left_inv := fun x =>
      hf <| by
        erw [mul, inv, mul_left_invₓ, one] }

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a group.
This version takes custom `npow` and `zpow` as `[has_pow M₁ ℕ]` and `[has_pow M₁ ℤ]` arguments.
See note [reducible non-instances]. -/
@[reducible,
  to_additive add_group_smul
      "A type endowed with `0` and `+` is an additive group,\nif it admits an injective map that preserves `0` and `+` to an additive group.\nThis version takes custom `nsmul` and `zsmul` as `[has_scalar ℕ M₁]` and\n`[has_scalar ℤ M₁]` arguments."]
protected def groupPow [Pow M₁ ℕ] [Pow M₁ ℤ] [Groupₓ M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) (zpow : ∀ x n : ℤ, f (x ^ n) = f x ^ n) : Groupₓ M₁ :=
  { hf.divInvMonoidPow f one mul inv div npow zpow, hf.Group f one mul inv div with }

/-- A type endowed with `1`, `*` and `⁻¹` is a commutative group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a commutative group.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive commutative group,\nif it admits an injective map that preserves `0` and `+` to an additive commutative group."]
protected def commGroup [CommGroupₓ M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) :
    CommGroupₓ M₁ :=
  { hf.CommMonoid f one mul, hf.Group f one mul inv div with }

end Injective

/-!
### Surjective
-/


namespace Surjective

variable {M₁ : Type _} {M₂ : Type _} [Mul M₂]

/-- A type endowed with `*` is a semigroup,
if it admits a surjective map that preserves `*` from a semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `+` is an additive semigroup,\nif it admits a surjective map that preserves `+` from an additive semigroup."]
protected def semigroup [Semigroupₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (mul : ∀ x y, f (x * y) = f x * f y) :
    Semigroupₓ M₂ :=
  { ‹Mul M₂› with
    mul_assoc :=
      hf.forall₃.2 fun x y z => by
        simp only [← mul, mul_assoc] }

/-- A type endowed with `*` is a commutative semigroup,
if it admits a surjective map that preserves `*` from a commutative semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `+` is an additive commutative semigroup,\nif it admits a surjective map that preserves `+` from an additive commutative semigroup."]
protected def commSemigroup [CommSemigroupₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (mul : ∀ x y, f (x * y) = f x * f y) :
    CommSemigroupₓ M₂ :=
  { hf.Semigroup f mul with
    mul_comm :=
      hf.Forall₂.2 fun x y => by
        erw [← mul, ← mul, mul_comm] }

variable [One M₂]

/-- A type endowed with `1` and `*` is a mul_one_class,
if it admits a surjective map that preserves `1` and `*` from a mul_one_class.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an add_zero_class,\nif it admits a surjective map that preserves `0` and `+` to an add_zero_class."]
protected def mulOneClass [MulOneClassₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClassₓ M₂ :=
  { ‹One M₂›, ‹Mul M₂› with
    one_mul :=
      hf.forall.2 fun x => by
        erw [← one, ← mul, one_mulₓ],
    mul_one :=
      hf.forall.2 fun x => by
        erw [← one, ← mul, mul_oneₓ] }

/-- A type endowed with `1` and `*` is a monoid,
if it admits a surjective map that preserves `1` and `*` from a monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive monoid,\nif it admits a surjective map that preserves `0` and `+` to an additive monoid."]
protected def monoid [Monoidₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : Monoidₓ M₂ :=
  { hf.Semigroup f mul, hf.MulOneClass f one mul with }

/-- A type endowed with `1` and `*` is a monoid,
if it admits a surjective map that preserves `1` and `*` to a monoid.
This version takes a custom `npow` as a `[has_pow M₂ ℕ]` argument.
See note [reducible non-instances]. -/
@[reducible,
  to_additive add_monoid_smul
      "A type endowed with `0` and `+` is an additive monoid,\nif it admits a surjective map that preserves `0` and `+` to an additive monoid.\nThis version takes a custom `nsmul` as a `[has_scalar ℕ M₂]` argument."]
protected def monoidPow [Pow M₂ ℕ] [Monoidₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) : Monoidₓ M₂ :=
  { hf.Monoid f one mul with npow := fun n x => x ^ n,
    npow_zero' :=
      hf.forall.2 fun x => by
        erw [← npow, pow_zeroₓ, ← one],
    npow_succ' := fun n =>
      hf.forall.2 fun x => by
        erw [← npow, pow_succₓ, ← npow, ← mul] }

/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits a surjective map that preserves `1` and `*` from a commutative monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive commutative monoid,\nif it admits a surjective map that preserves `0` and `+` to an additive commutative monoid."]
protected def commMonoid [CommMonoidₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommMonoidₓ M₂ :=
  { hf.CommSemigroup f mul, hf.Monoid f one mul with }

variable [Inv M₂] [Div M₂]

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a `div_inv_monoid`
See note [reducible non-instances]. -/
@[reducible,
  to_additive SubNegMonoidₓ
      "A type endowed with `0`, `+`, and `-` (unary and binary) is an additive group,\nif it admits a surjective map that preserves `0`, `+`, and `-` from a `sub_neg_monoid`"]
protected def divInvMonoid [DivInvMonoidₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) :
    DivInvMonoidₓ M₂ :=
  { hf.Monoid f one mul, ‹Div M₂›, ‹Inv M₂› with
    div_eq_mul_inv :=
      hf.Forall₂.2 fun x y => by
        erw [← inv, ← mul, ← div, div_eq_mul_inv] }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`.
This version takes custom `npow` and `zpow` as `[has_pow M₂ ℕ]` and `[has_pow M₂ ℤ]` arguments.
See note [reducible non-instances]. -/
@[reducible,
  to_additive sub_neg_monoid_smul
      "A type endowed with `0`, `+`, unary `-`, and binary `-` is a `sub_neg_monoid`\nif it admits a surjective map that preserves `0`, `+`, unary `-`, and binary `-` to\na `sub_neg_monoid`.\nThis version takes custom `nsmul` and `zsmul` as `[has_scalar ℕ M₂]` and\n`[has_scalar ℤ M₂]` arguments."]
protected def divInvMonoidPow [Pow M₂ ℕ] [Pow M₂ ℤ] [DivInvMonoidₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) (zpow : ∀ x n : ℤ, f (x ^ n) = f x ^ n) : DivInvMonoidₓ M₂ :=
  { hf.monoidPow f one mul npow, hf.DivInvMonoid f one mul inv div with zpow := fun n x => x ^ n,
    zpow_zero' :=
      hf.forall.2 fun x => by
        erw [← zpow, zpow_zero, ← one],
    zpow_succ' := fun n =>
      hf.forall.2 fun x => by
        erw [← zpow, ← zpow, zpow_of_nat, zpow_of_nat, pow_succₓ, ← mul],
    zpow_neg' := fun n =>
      hf.forall.2 fun x => by
        erw [← zpow, ← zpow, zpow_neg_succ_of_nat, zpow_coe_nat, inv] }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a group,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a group.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0`, `+`, and unary `-` is an additive group,\nif it admits a surjective map that preserves `0`, `+`, and `-` from an additive group."]
protected def group [Groupₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) : Groupₓ M₂ :=
  { hf.DivInvMonoid f one mul inv div with
    mul_left_inv :=
      hf.forall.2 fun x => by
        erw [← inv, ← mul, mul_left_invₓ, one] <;> rfl }

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits a surjective map that preserves `1`, `*` and `⁻¹` to a group.
This version takes custom `npow` and `zpow` as `[has_pow M₂ ℕ]` and `[has_pow M₂ ℤ]` arguments.
See note [reducible non-instances]. -/
@[reducible,
  to_additive add_group_smul
      "A type endowed with `0` and `+` is an additive group,\nif it admits a surjective map that preserves `0` and `+` to an additive group.\nThis version takes custom `nsmul` and `zsmul` as `[has_scalar ℕ M₂]` and\n`[has_scalar ℤ M₂]` arguments."]
protected def groupPow [Pow M₂ ℕ] [Pow M₂ ℤ] [Groupₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) (zpow : ∀ x n : ℤ, f (x ^ n) = f x ^ n) : Groupₓ M₂ :=
  { hf.divInvMonoidPow f one mul inv div npow zpow, hf.Group f one mul inv div with }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a commutative group,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a commutative group.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive commutative group,\nif it admits a surjective map that preserves `0` and `+` to an additive commutative group."]
protected def commGroup [CommGroupₓ M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) :
    CommGroupₓ M₂ :=
  { hf.CommMonoid f one mul, hf.Group f one mul inv div with }

end Surjective

end Function


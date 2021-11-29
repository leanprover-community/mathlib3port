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

variable{M₁ : Type _}{M₂ : Type _}[Mul M₁]

/-- A type endowed with `*` is a semigroup,
if it admits an injective map that preserves `*` to a semigroup.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `+` is an additive semigroup,\nif it admits an injective map that preserves `+` to an additive semigroup."]
protected def Semigroupₓ [Semigroupₓ M₂] (f : M₁ → M₂) (hf : injective f) (mul : ∀ x y, f (x*y) = f x*f y) :
  Semigroupₓ M₁ :=
  { ‹Mul M₁› with
    mul_assoc :=
      fun x y z =>
        hf$
          by 
            erw [mul, mul, mul, mul, mul_assocₓ] }

/-- A type endowed with `*` is a commutative semigroup,
if it admits an injective map that preserves `*` to a commutative semigroup.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `+` is an additive commutative semigroup,\nif it admits an injective map that preserves `+` to an additive commutative semigroup."]
protected def CommSemigroupₓ [CommSemigroupₓ M₂] (f : M₁ → M₂) (hf : injective f) (mul : ∀ x y, f (x*y) = f x*f y) :
  CommSemigroupₓ M₁ :=
  { hf.semigroup f mul with
    mul_comm :=
      fun x y =>
        hf$
          by 
            erw [mul, mul, mul_commₓ] }

/-- A type endowed with `*` is a left cancel semigroup,
if it admits an injective map that preserves `*` to a left cancel semigroup.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive AddLeftCancelSemigroup
      "A type endowed with `+` is an additive left cancel semigroup,\nif it admits an injective map that preserves `+` to an additive left cancel semigroup."]
protected def LeftCancelSemigroup [LeftCancelSemigroup M₂] (f : M₁ → M₂) (hf : injective f)
  (mul : ∀ x y, f (x*y) = f x*f y) : LeftCancelSemigroup M₁ :=
  { hf.semigroup f mul with mul := ·*·,
    mul_left_cancel :=
      fun x y z H =>
        hf$
          (mul_right_injₓ (f x)).1$
            by 
              erw [←mul, ←mul, H] <;> rfl }

/-- A type endowed with `*` is a right cancel semigroup,
if it admits an injective map that preserves `*` to a right cancel semigroup.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive AddRightCancelSemigroup
      "A type endowed with `+` is an additive right cancel semigroup,\nif it admits an injective map that preserves `+` to an additive right cancel semigroup."]
protected def RightCancelSemigroup [RightCancelSemigroup M₂] (f : M₁ → M₂) (hf : injective f)
  (mul : ∀ x y, f (x*y) = f x*f y) : RightCancelSemigroup M₁ :=
  { hf.semigroup f mul with mul := ·*·,
    mul_right_cancel :=
      fun x y z H =>
        hf$
          (mul_left_injₓ (f y)).1$
            by 
              erw [←mul, ←mul, H] <;> rfl }

variable[HasOne M₁]

/-- A type endowed with `1` and `*` is a mul_one_class,
if it admits an injective map that preserves `1` and `*` to a mul_one_class.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `0` and `+` is an add_zero_class,\nif it admits an injective map that preserves `0` and `+` to an add_zero_class."]
protected def MulOneClass [MulOneClass M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) : MulOneClass M₁ :=
  { ‹HasOne M₁›, ‹Mul M₁› with
    one_mul :=
      fun x =>
        hf$
          by 
            erw [mul, one, one_mulₓ],
    mul_one :=
      fun x =>
        hf$
          by 
            erw [mul, one, mul_oneₓ] }

/-- A type endowed with `1` and `*` is a monoid,
if it admits an injective map that preserves `1` and `*` to a monoid.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `0` and `+` is an additive monoid,\nif it admits an injective map that preserves `0` and `+` to an additive monoid."]
protected def Monoidₓ [Monoidₓ M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1) (mul : ∀ x y, f (x*y) = f x*f y) :
  Monoidₓ M₁ :=
  { hf.semigroup f mul, hf.mul_one_class f one mul with  }

/-- A type endowed with `1` and `*` is a monoid,
if it admits an injective map that preserves `1` and `*` to a monoid.
This version takes a custom `npow` as a `[has_pow M₁ ℕ]` argument.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive add_monoid_smul
      "A type endowed with `0` and `+` is an additive monoid,\nif it admits an injective map that preserves `0` and `+` to an additive monoid.\nThis version takes a custom `nsmul` as a `[has_scalar ℕ M₁]` argument."]
protected def monoid_pow [Pow M₁ ℕ] [Monoidₓ M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) : Monoidₓ M₁ :=
  { hf.monoid f one mul with npow := fun n x => x ^ n,
    npow_zero' :=
      fun x =>
        hf$
          by 
            erw [npow, one, pow_zeroₓ],
    npow_succ' :=
      fun n x =>
        hf$
          by 
            erw [npow, pow_succₓ, mul, npow] }

/-- A type endowed with `1` and `*` is a left cancel monoid,
if it admits an injective map that preserves `1` and `*` to a left cancel monoid.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive AddLeftCancelMonoid
      "A type endowed with `0` and `+` is an additive left cancel monoid,\nif it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def LeftCancelMonoid [LeftCancelMonoid M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) : LeftCancelMonoid M₁ :=
  { hf.left_cancel_semigroup f mul, hf.monoid f one mul with  }

/-- A type endowed with `1` and `*` is a right cancel monoid,
if it admits an injective map that preserves `1` and `*` to a right cancel monoid.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive AddRightCancelMonoid
      "A type endowed with `0` and `+` is an additive left cancel monoid,\nif it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def RightCancelMonoid [RightCancelMonoid M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) : RightCancelMonoid M₁ :=
  { hf.right_cancel_semigroup f mul, hf.monoid f one mul with  }

/-- A type endowed with `1` and `*` is a cancel monoid,
if it admits an injective map that preserves `1` and `*` to a cancel monoid.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive AddCancelMonoid
      "A type endowed with `0` and `+` is an additive left cancel monoid,\nif it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def CancelMonoid [CancelMonoid M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) : CancelMonoid M₁ :=
  { hf.left_cancel_monoid f one mul, hf.right_cancel_monoid f one mul with  }

/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits an injective map that preserves `1` and `*` to a commutative monoid.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `0` and `+` is an additive commutative monoid,\nif it admits an injective map that preserves `0` and `+` to an additive commutative monoid."]
protected def CommMonoidₓ [CommMonoidₓ M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) : CommMonoidₓ M₁ :=
  { hf.comm_semigroup f mul, hf.monoid f one mul with  }

/-- A type endowed with `1` and `*` is a cancel commutative monoid,
if it admits an injective map that preserves `1` and `*` to a cancel commutative monoid.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive AddCancelCommMonoid
      "A type endowed with `0` and `+` is an additive cancel commutative monoid,\nif it admits an injective map that preserves `0` and `+` to an additive cancel commutative monoid."]
protected def CancelCommMonoid [CancelCommMonoid M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) : CancelCommMonoid M₁ :=
  { hf.left_cancel_semigroup f mul, hf.comm_monoid f one mul with  }

variable[HasInv M₁][Div M₁]

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits an injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive SubNegMonoidₓ
      "A type endowed with `0`, `+`, unary `-`, and binary `-` is a `sub_neg_monoid`\nif it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to\na `sub_neg_monoid`."]
protected def DivInvMonoidₓ [DivInvMonoidₓ M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) (inv : ∀ x, f (x⁻¹) = f x⁻¹) (div : ∀ x y, f (x / y) = f x / f y) :
  DivInvMonoidₓ M₁ :=
  { hf.monoid f one mul, ‹HasInv M₁›, ‹Div M₁› with
    div_eq_mul_inv :=
      fun x y =>
        hf$
          by 
            erw [div, mul, inv, div_eq_mul_inv] }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits an injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`.
This version takes custom `npow` and `zpow` as `[has_pow M₁ ℕ]` and `[has_pow M₁ ℤ]` arguments.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive sub_neg_monoid_smul
      "A type endowed with `0`, `+`, unary `-`, and binary `-` is a `sub_neg_monoid`\nif it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to\na `sub_neg_monoid`.\nThis version takes custom `nsmul` and `zsmul` as `[has_scalar ℕ M₁]` and\n`[has_scalar ℤ M₁]` arguments."]
protected def div_inv_monoid_pow [Pow M₁ ℕ] [Pow M₁ ℤ] [DivInvMonoidₓ M₂] (f : M₁ → M₂) (hf : injective f)
  (one : f 1 = 1) (mul : ∀ x y, f (x*y) = f x*f y) (inv : ∀ x, f (x⁻¹) = f x⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n) : DivInvMonoidₓ M₁ :=
  { hf.monoid_pow f one mul npow, hf.div_inv_monoid f one mul inv div with zpow := fun n x => x ^ n,
    zpow_zero' :=
      fun x =>
        hf$
          by 
            erw [zpow, zpow_zero, one],
    zpow_succ' :=
      fun n x =>
        hf$
          by 
            erw [zpow, mul, zpow_of_nat, pow_succₓ, zpow, zpow_of_nat],
    zpow_neg' :=
      fun n x =>
        hf$
          by 
            erw [zpow, zpow_neg_succ_of_nat, inv, zpow, zpow_coe_nat] }

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a group.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `0` and `+` is an additive group,\nif it admits an injective map that preserves `0` and `+` to an additive group."]
protected def Groupₓ [Groupₓ M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1) (mul : ∀ x y, f (x*y) = f x*f y)
  (inv : ∀ x, f (x⁻¹) = f x⁻¹) (div : ∀ x y, f (x / y) = f x / f y) : Groupₓ M₁ :=
  { hf.div_inv_monoid f one mul inv div with
    mul_left_inv :=
      fun x =>
        hf$
          by 
            erw [mul, inv, mul_left_invₓ, one] }

/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a group.
This version takes custom `npow` and `zpow` as `[has_pow M₁ ℕ]` and `[has_pow M₁ ℤ]` arguments.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive add_group_smul
      "A type endowed with `0` and `+` is an additive group,\nif it admits an injective map that preserves `0` and `+` to an additive group.\nThis version takes custom `nsmul` and `zsmul` as `[has_scalar ℕ M₁]` and\n`[has_scalar ℤ M₁]` arguments."]
protected def group_pow [Pow M₁ ℕ] [Pow M₁ ℤ] [Groupₓ M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) (inv : ∀ x, f (x⁻¹) = f x⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
  (npow : ∀ x (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ x (n : ℤ), f (x ^ n) = f x ^ n) : Groupₓ M₁ :=
  { hf.div_inv_monoid_pow f one mul inv div npow zpow, hf.group f one mul inv div with  }

/-- A type endowed with `1`, `*` and `⁻¹` is a commutative group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a commutative group.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `0` and `+` is an additive commutative group,\nif it admits an injective map that preserves `0` and `+` to an additive commutative group."]
protected def CommGroupₓ [CommGroupₓ M₂] (f : M₁ → M₂) (hf : injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) (inv : ∀ x, f (x⁻¹) = f x⁻¹) (div : ∀ x y, f (x / y) = f x / f y) : CommGroupₓ M₁ :=
  { hf.comm_monoid f one mul, hf.group f one mul inv div with  }

end Injective

/-!
### Surjective
-/


namespace Surjective

variable{M₁ : Type _}{M₂ : Type _}[Mul M₂]

/-- A type endowed with `*` is a semigroup,
if it admits a surjective map that preserves `*` from a semigroup.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `+` is an additive semigroup,\nif it admits a surjective map that preserves `+` from an additive semigroup."]
protected def Semigroupₓ [Semigroupₓ M₁] (f : M₁ → M₂) (hf : surjective f) (mul : ∀ x y, f (x*y) = f x*f y) :
  Semigroupₓ M₂ :=
  { ‹Mul M₂› with
    mul_assoc :=
      hf.forall₃.2$
        fun x y z =>
          by 
            simp only [←mul, mul_assocₓ] }

/-- A type endowed with `*` is a commutative semigroup,
if it admits a surjective map that preserves `*` from a commutative semigroup.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `+` is an additive commutative semigroup,\nif it admits a surjective map that preserves `+` from an additive commutative semigroup."]
protected def CommSemigroupₓ [CommSemigroupₓ M₁] (f : M₁ → M₂) (hf : surjective f) (mul : ∀ x y, f (x*y) = f x*f y) :
  CommSemigroupₓ M₂ :=
  { hf.semigroup f mul with
    mul_comm :=
      hf.forall₂.2$
        fun x y =>
          by 
            erw [←mul, ←mul, mul_commₓ] }

variable[HasOne M₂]

/-- A type endowed with `1` and `*` is a mul_one_class,
if it admits a surjective map that preserves `1` and `*` from a mul_one_class.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `0` and `+` is an add_zero_class,\nif it admits a surjective map that preserves `0` and `+` to an add_zero_class."]
protected def MulOneClass [MulOneClass M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) : MulOneClass M₂ :=
  { ‹HasOne M₂›, ‹Mul M₂› with
    one_mul :=
      hf.forall.2$
        fun x =>
          by 
            erw [←one, ←mul, one_mulₓ],
    mul_one :=
      hf.forall.2$
        fun x =>
          by 
            erw [←one, ←mul, mul_oneₓ] }

/-- A type endowed with `1` and `*` is a monoid,
if it admits a surjective map that preserves `1` and `*` from a monoid.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `0` and `+` is an additive monoid,\nif it admits a surjective map that preserves `0` and `+` to an additive monoid."]
protected def Monoidₓ [Monoidₓ M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 1 = 1) (mul : ∀ x y, f (x*y) = f x*f y) :
  Monoidₓ M₂ :=
  { hf.semigroup f mul, hf.mul_one_class f one mul with  }

/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits a surjective map that preserves `1` and `*` from a commutative monoid.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `0` and `+` is an additive commutative monoid,\nif it admits a surjective map that preserves `0` and `+` to an additive commutative monoid."]
protected def CommMonoidₓ [CommMonoidₓ M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) : CommMonoidₓ M₂ :=
  { hf.comm_semigroup f mul, hf.monoid f one mul with  }

variable[HasInv M₂][Div M₂]

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a `div_inv_monoid`
See note [reducible non-instances]. -/
@[reducible,
  toAdditive SubNegMonoidₓ
      "A type endowed with `0`, `+`, and `-` (unary and binary) is an additive group,\nif it admits a surjective map that preserves `0`, `+`, and `-` from a `sub_neg_monoid`"]
protected def DivInvMonoidₓ [DivInvMonoidₓ M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) (inv : ∀ x, f (x⁻¹) = f x⁻¹) (div : ∀ x y, f (x / y) = f x / f y) :
  DivInvMonoidₓ M₂ :=
  { hf.monoid f one mul, ‹Div M₂›, ‹HasInv M₂› with
    div_eq_mul_inv :=
      hf.forall₂.2$
        fun x y =>
          by 
            erw [←inv, ←mul, ←div, div_eq_mul_inv] }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a group,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a group.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `0`, `+`, and unary `-` is an additive group,\nif it admits a surjective map that preserves `0`, `+`, and `-` from an additive group."]
protected def Groupₓ [Groupₓ M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 1 = 1) (mul : ∀ x y, f (x*y) = f x*f y)
  (inv : ∀ x, f (x⁻¹) = f x⁻¹) (div : ∀ x y, f (x / y) = f x / f y) : Groupₓ M₂ :=
  { hf.div_inv_monoid f one mul inv div with
    mul_left_inv :=
      hf.forall.2$
        fun x =>
          by 
            erw [←inv, ←mul, mul_left_invₓ, one] <;> rfl }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a commutative group,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a commutative group.
See note [reducible non-instances]. -/
@[reducible,
  toAdditive
      "A type endowed with `0` and `+` is an additive commutative group,\nif it admits a surjective map that preserves `0` and `+` to an additive commutative group."]
protected def CommGroupₓ [CommGroupₓ M₁] (f : M₁ → M₂) (hf : surjective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x*y) = f x*f y) (inv : ∀ x, f (x⁻¹) = f x⁻¹) (div : ∀ x y, f (x / y) = f x / f y) : CommGroupₓ M₂ :=
  { hf.comm_monoid f one mul, hf.group f one mul inv div with  }

end Surjective

end Function


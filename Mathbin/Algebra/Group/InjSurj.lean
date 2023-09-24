/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Algebra.Group.Defs
import Logic.Function.Basic
import Data.Int.Cast.Basic

#align_import algebra.group.inj_surj from "leanprover-community/mathlib"@"d23418e009d2bc37f9e1047ecaa229790b7356be"

/-!
# Lifting algebraic data classes along injective/surjective maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

#print Function.Injective.semigroup /-
/-- A type endowed with `*` is a semigroup,
if it admits an injective map that preserves `*` to a semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `+` is an additive semigroup,\nif it admits an injective map that preserves `+` to an additive semigroup."]
protected def semigroup [Semigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : Semigroup M₁ :=
  { ‹Mul M₁› with mul_assoc := fun x y z => hf <| by erw [mul, mul, mul, mul, mul_assoc] }
#align function.injective.semigroup Function.Injective.semigroup
#align function.injective.add_semigroup Function.Injective.addSemigroup
-/

#print Function.Injective.commSemigroup /-
/-- A type endowed with `*` is a commutative semigroup,
if it admits an injective map that preserves `*` to a commutative semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `+` is an additive commutative semigroup,\nif it admits an injective map that preserves `+` to an additive commutative semigroup."]
protected def commSemigroup [CommSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommSemigroup M₁ :=
  { hf.Semigroup f mul with mul_comm := fun x y => hf <| by erw [mul, mul, mul_comm] }
#align function.injective.comm_semigroup Function.Injective.commSemigroup
#align function.injective.add_comm_semigroup Function.Injective.addCommSemigroup
-/

#print Function.Injective.leftCancelSemigroup /-
/-- A type endowed with `*` is a left cancel semigroup,
if it admits an injective map that preserves `*` to a left cancel semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddLeftCancelSemigroup
      "A type endowed with `+` is an additive left cancel semigroup,\nif it admits an injective map that preserves `+` to an additive left cancel semigroup."]
protected def leftCancelSemigroup [LeftCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftCancelSemigroup M₁ :=
  { hf.Semigroup f mul with
    mul := (· * ·)
    hMul_left_cancel := fun x y z H =>
      hf <| (mul_right_inj (f x)).1 <| by erw [← mul, ← mul, H] <;> rfl }
#align function.injective.left_cancel_semigroup Function.Injective.leftCancelSemigroup
#align function.injective.add_left_cancel_semigroup Function.Injective.addLeftCancelSemigroup
-/

#print Function.Injective.rightCancelSemigroup /-
/-- A type endowed with `*` is a right cancel semigroup,
if it admits an injective map that preserves `*` to a right cancel semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddRightCancelSemigroup
      "A type endowed with `+` is an additive right cancel semigroup,\nif it admits an injective map that preserves `+` to an additive right cancel semigroup."]
protected def rightCancelSemigroup [RightCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightCancelSemigroup M₁ :=
  { hf.Semigroup f mul with
    mul := (· * ·)
    hMul_right_cancel := fun x y z H =>
      hf <| (mul_left_inj (f y)).1 <| by erw [← mul, ← mul, H] <;> rfl }
#align function.injective.right_cancel_semigroup Function.Injective.rightCancelSemigroup
#align function.injective.add_right_cancel_semigroup Function.Injective.addRightCancelSemigroup
-/

variable [One M₁]

#print Function.Injective.mulOneClass /-
/-- A type endowed with `1` and `*` is a mul_one_class,
if it admits an injective map that preserves `1` and `*` to a mul_one_class.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an add_zero_class,\nif it admits an injective map that preserves `0` and `+` to an add_zero_class."]
protected def mulOneClass [MulOneClass M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClass M₁ :=
  { ‹One M₁›,
    ‹Mul M₁› with
    one_mul := fun x => hf <| by erw [mul, one, one_mul]
    mul_one := fun x => hf <| by erw [mul, one, mul_one] }
#align function.injective.mul_one_class Function.Injective.mulOneClass
#align function.injective.add_zero_class Function.Injective.addZeroClass
-/

variable [Pow M₁ ℕ]

#print Function.Injective.monoid /-
/-- A type endowed with `1` and `*` is a monoid,
if it admits an injective map that preserves `1` and `*` to a monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive monoid,\nif it admits an injective map that preserves `0` and `+` to an additive monoid.\nThis version takes a custom `nsmul` as a `[has_smul ℕ M₁]` argument."]
protected def monoid [Monoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : Monoid M₁ :=
  { hf.Semigroup f mul,
    hf.MulOneClass f one mul with
    npow := fun n x => x ^ n
    npow_zero := fun x => hf <| by erw [npow, one, pow_zero]
    npow_succ := fun n x => hf <| by erw [npow, pow_succ, mul, npow] }
#align function.injective.monoid Function.Injective.monoid
#align function.injective.add_monoid Function.Injective.addMonoid
-/

#print Function.Injective.addMonoidWithOne /-
/-- A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits an injective map that preserves `0`, `1` and `+` to an additive monoid with one.
See note [reducible non-instances]. -/
@[reducible]
protected def addMonoidWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [NatCast M₁]
    [AddMonoidWithOne M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (nat_cast : ∀ n : ℕ, f n = n) : AddMonoidWithOne M₁ :=
  { hf.AddMonoid f zero add nsmul with
    natCast := coe
    natCast_zero := hf (by erw [nat_cast, Nat.cast_zero, zero])
    natCast_succ := fun n => hf (by erw [nat_cast, Nat.cast_succ, add, one, nat_cast])
    one := 1 }
#align function.injective.add_monoid_with_one Function.Injective.addMonoidWithOne
-/

#print Function.Injective.leftCancelMonoid /-
/-- A type endowed with `1` and `*` is a left cancel monoid,
if it admits an injective map that preserves `1` and `*` to a left cancel monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddLeftCancelMonoid
      "A type endowed with `0` and `+` is an additive left cancel monoid,\nif it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def leftCancelMonoid [LeftCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : LeftCancelMonoid M₁ :=
  { hf.LeftCancelSemigroup f mul, hf.Monoid f one mul npow with }
#align function.injective.left_cancel_monoid Function.Injective.leftCancelMonoid
#align function.injective.add_left_cancel_monoid Function.Injective.addLeftCancelMonoid
-/

#print Function.Injective.rightCancelMonoid /-
/-- A type endowed with `1` and `*` is a right cancel monoid,
if it admits an injective map that preserves `1` and `*` to a right cancel monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddRightCancelMonoid
      "A type endowed with `0` and `+` is an additive left cancel monoid,\nif it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def rightCancelMonoid [RightCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : RightCancelMonoid M₁ :=
  { hf.RightCancelSemigroup f mul, hf.Monoid f one mul npow with }
#align function.injective.right_cancel_monoid Function.Injective.rightCancelMonoid
#align function.injective.add_right_cancel_monoid Function.Injective.addRightCancelMonoid
-/

#print Function.Injective.cancelMonoid /-
/-- A type endowed with `1` and `*` is a cancel monoid,
if it admits an injective map that preserves `1` and `*` to a cancel monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddCancelMonoid
      "A type endowed with `0` and `+` is an additive left cancel monoid,\nif it admits an injective map that preserves `0` and `+` to an additive left cancel monoid."]
protected def cancelMonoid [CancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CancelMonoid M₁ :=
  { hf.LeftCancelMonoid f one mul npow, hf.RightCancelMonoid f one mul npow with }
#align function.injective.cancel_monoid Function.Injective.cancelMonoid
#align function.injective.add_cancel_monoid Function.Injective.addCancelMonoid
-/

#print Function.Injective.commMonoid /-
/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits an injective map that preserves `1` and `*` to a commutative monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive commutative monoid,\nif it admits an injective map that preserves `0` and `+` to an additive commutative monoid."]
protected def commMonoid [CommMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoid M₁ :=
  { hf.CommSemigroup f mul, hf.Monoid f one mul npow with }
#align function.injective.comm_monoid Function.Injective.commMonoid
#align function.injective.add_comm_monoid Function.Injective.addCommMonoid
-/

#print Function.Injective.addCommMonoidWithOne /-
/-- A type endowed with `0`, `1` and `+` is an additive commutative monoid with one, if it admits an
injective map that preserves `0`, `1` and `+` to an additive commutative monoid with one.
See note [reducible non-instances]. -/
@[reducible]
protected def addCommMonoidWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [NatCast M₁]
    [AddCommMonoidWithOne M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (nat_cast : ∀ n : ℕ, f n = n) : AddCommMonoidWithOne M₁ :=
  { hf.AddMonoidWithOne f zero one add nsmul nat_cast, hf.AddCommMonoid f zero add nsmul with }
#align function.injective.add_comm_monoid_with_one Function.Injective.addCommMonoidWithOne
-/

#print Function.Injective.cancelCommMonoid /-
/-- A type endowed with `1` and `*` is a cancel commutative monoid,
if it admits an injective map that preserves `1` and `*` to a cancel commutative monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive AddCancelCommMonoid
      "A type endowed with `0` and `+` is an additive cancel commutative monoid,\nif it admits an injective map that preserves `0` and `+` to an additive cancel commutative monoid."]
protected def cancelCommMonoid [CancelCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CancelCommMonoid M₁ :=
  { hf.LeftCancelSemigroup f mul, hf.CommMonoid f one mul npow with }
#align function.injective.cancel_comm_monoid Function.Injective.cancelCommMonoid
#align function.injective.add_cancel_comm_monoid Function.Injective.addCancelCommMonoid
-/

#print Function.Injective.involutiveInv /-
--See note [reducible non-instances]
/-- A type has an involutive inversion if it admits a surjective map that preserves `⁻¹` to a type
which has an involutive inversion. -/
@[reducible,
  to_additive
      "A type has an involutive negation if it admits a surjective map that\npreserves `⁻¹` to a type which has an involutive inversion."]
protected def involutiveInv {M₁ : Type _} [Inv M₁] [InvolutiveInv M₂] (f : M₁ → M₂)
    (hf : Injective f) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) : InvolutiveInv M₁
    where
  inv := Inv.inv
  inv_inv x := hf <| by rw [inv, inv, inv_inv]
#align function.injective.has_involutive_inv Function.Injective.involutiveInv
#align function.injective.has_involutive_neg Function.Injective.involutiveNeg
-/

variable [Inv M₁] [Div M₁] [Pow M₁ ℤ]

#print Function.Injective.divInvMonoid /-
/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits an injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`.
See note [reducible non-instances]. -/
@[reducible,
  to_additive SubNegMonoid
      "A type endowed with `0`, `+`, unary `-`, and binary `-` is a `sub_neg_monoid`\nif it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to\na `sub_neg_monoid`.\nThis version takes custom `nsmul` and `zsmul` as `[has_smul ℕ M₁]` and\n`[has_smul ℤ M₁]` arguments."]
protected def divInvMonoid [DivInvMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvMonoid M₁ :=
  { hf.Monoid f one mul npow, ‹Inv M₁›,
    ‹Div M₁› with
    zpow := fun n x => x ^ n
    zpow_zero' := fun x => hf <| by erw [zpow, zpow_zero, one]
    zpow_succ' := fun n x => hf <| by erw [zpow, mul, zpow_ofNat, pow_succ, zpow, zpow_ofNat]
    zpow_neg' := fun n x => hf <| by erw [zpow, zpow_negSucc, inv, zpow, zpow_ofNat]
    div_eq_hMul_inv := fun x y => hf <| by erw [div, mul, inv, div_eq_mul_inv] }
#align function.injective.div_inv_monoid Function.Injective.divInvMonoid
#align function.injective.sub_neg_monoid Function.Injective.subNegMonoid
-/

#print Function.Injective.divisionMonoid /-
-- See note [reducible non-instances]
/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `division_monoid`
if it admits an injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `division_monoid`. -/
@[reducible,
  to_additive
      "A type endowed with `0`, `+`, unary `-`, and binary `-` is a `subtraction_monoid`\nif it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to\na `subtraction_monoid`.\nThis version takes custom `nsmul` and `zsmul` as `[has_smul ℕ M₁]` and\n`[has_smul ℤ M₁]` arguments."]
protected def divisionMonoid [DivisionMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivisionMonoid M₁ :=
  { hf.DivInvMonoid f one mul inv div npow zpow,
    hf.InvolutiveInv f
      inv with
    mul_inv_rev := fun x y => hf <| by erw [inv, mul, mul_inv_rev, mul, inv, inv]
    inv_eq_of_hMul := fun x y h =>
      hf <| by erw [inv, inv_eq_of_mul_eq_one_right (by erw [← mul, h, one])] }
#align function.injective.division_monoid Function.Injective.divisionMonoid
#align function.injective.subtraction_monoid Function.Injective.subtractionMonoid
-/

#print Function.Injective.divisionCommMonoid /-
-- See note [reducible non-instances]
/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `division_comm_monoid`
if it admits an injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `division_comm_monoid`.
See note [reducible non-instances]. -/
@[reducible,
  to_additive SubtractionCommMonoid
      "A type endowed with `0`, `+`, unary `-`, and binary `-` is a `subtraction_comm_monoid`\nif it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to\na `subtraction_comm_monoid`.\nThis version takes custom `nsmul` and `zsmul` as `[has_smul ℕ M₁]` and\n`[has_smul ℤ M₁]` arguments."]
protected def divisionCommMonoid [DivisionCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivisionCommMonoid M₁ :=
  { hf.DivisionMonoid f one mul inv div npow zpow, hf.CommSemigroup f mul with }
#align function.injective.division_comm_monoid Function.Injective.divisionCommMonoid
#align function.injective.subtraction_comm_monoid Function.Injective.subtractionCommMonoid
-/

#print Function.Injective.group /-
/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a group.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive group,\nif it admits an injective map that preserves `0` and `+` to an additive group."]
protected def group [Group M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : Group M₁ :=
  { hf.DivInvMonoid f one mul inv div npow zpow with
    hMul_left_inv := fun x => hf <| by erw [mul, inv, mul_left_inv, one] }
#align function.injective.group Function.Injective.group
#align function.injective.add_group Function.Injective.addGroup
-/

#print Function.Injective.addGroupWithOne /-
/-- A type endowed with `0`, `1` and `+` is an additive group with one,
if it admits an injective map that preserves `0`, `1` and `+` to an additive group with one.
See note [reducible non-instances]. -/
@[reducible]
protected def addGroupWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [Neg M₁] [Sub M₁]
    [SMul ℤ M₁] [NatCast M₁] [IntCast M₁] [AddGroupWithOne M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : AddGroupWithOne M₁ :=
  { hf.AddGroup f zero add neg sub nsmul zsmul,
    hf.AddMonoidWithOne f zero one add nsmul
      nat_cast with
    intCast := coe
    intCast_ofNat := fun n => hf (by simp only [nat_cast, int_cast, Int.cast_ofNat])
    intCast_negSucc := fun n =>
      hf (by erw [int_cast, neg, nat_cast, Int.cast_neg, Int.cast_ofNat]) }
#align function.injective.add_group_with_one Function.Injective.addGroupWithOne
-/

#print Function.Injective.commGroup /-
/-- A type endowed with `1`, `*` and `⁻¹` is a commutative group,
if it admits an injective map that preserves `1`, `*` and `⁻¹` to a commutative group.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive commutative group,\nif it admits an injective map that preserves `0` and `+` to an additive commutative group."]
protected def commGroup [CommGroup M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroup M₁ :=
  { hf.CommMonoid f one mul npow, hf.Group f one mul inv div npow zpow with }
#align function.injective.comm_group Function.Injective.commGroup
#align function.injective.add_comm_group Function.Injective.addCommGroup
-/

#print Function.Injective.addCommGroupWithOne /-
/-- A type endowed with `0`, `1` and `+` is an additive commutative group with one, if it admits an
injective map that preserves `0`, `1` and `+` to an additive commutative group with one.
See note [reducible non-instances]. -/
@[reducible]
protected def addCommGroupWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [Neg M₁] [Sub M₁]
    [SMul ℤ M₁] [NatCast M₁] [IntCast M₁] [AddCommGroupWithOne M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : AddCommGroupWithOne M₁ :=
  { hf.AddGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast,
    hf.AddCommMonoid f zero add nsmul with }
#align function.injective.add_comm_group_with_one Function.Injective.addCommGroupWithOne
-/

end Injective

/-!
### Surjective
-/


namespace Surjective

variable {M₁ : Type _} {M₂ : Type _} [Mul M₂]

#print Function.Surjective.semigroup /-
/-- A type endowed with `*` is a semigroup,
if it admits a surjective map that preserves `*` from a semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `+` is an additive semigroup,\nif it admits a surjective map that preserves `+` from an additive semigroup."]
protected def semigroup [Semigroup M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : Semigroup M₂ :=
  { ‹Mul M₂› with mul_assoc := hf.forall₃.2 fun x y z => by simp only [← mul, mul_assoc] }
#align function.surjective.semigroup Function.Surjective.semigroup
#align function.surjective.add_semigroup Function.Surjective.addSemigroup
-/

#print Function.Surjective.commSemigroup /-
/-- A type endowed with `*` is a commutative semigroup,
if it admits a surjective map that preserves `*` from a commutative semigroup.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `+` is an additive commutative semigroup,\nif it admits a surjective map that preserves `+` from an additive commutative semigroup."]
protected def commSemigroup [CommSemigroup M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommSemigroup M₂ :=
  { hf.Semigroup f mul with mul_comm := hf.Forall₂.2 fun x y => by erw [← mul, ← mul, mul_comm] }
#align function.surjective.comm_semigroup Function.Surjective.commSemigroup
#align function.surjective.add_comm_semigroup Function.Surjective.addCommSemigroup
-/

variable [One M₂]

#print Function.Surjective.mulOneClass /-
/-- A type endowed with `1` and `*` is a mul_one_class,
if it admits a surjective map that preserves `1` and `*` from a mul_one_class.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an add_zero_class,\nif it admits a surjective map that preserves `0` and `+` to an add_zero_class."]
protected def mulOneClass [MulOneClass M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClass M₂ :=
  { ‹One M₂›,
    ‹Mul M₂› with
    one_mul := hf.forall.2 fun x => by erw [← one, ← mul, one_mul]
    mul_one := hf.forall.2 fun x => by erw [← one, ← mul, mul_one] }
#align function.surjective.mul_one_class Function.Surjective.mulOneClass
#align function.surjective.add_zero_class Function.Surjective.addZeroClass
-/

variable [Pow M₂ ℕ]

#print Function.Surjective.monoid /-
/-- A type endowed with `1` and `*` is a monoid,
if it admits a surjective map that preserves `1` and `*` to a monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive monoid,\nif it admits a surjective map that preserves `0` and `+` to an additive monoid.\nThis version takes a custom `nsmul` as a `[has_smul ℕ M₂]` argument."]
protected def monoid [Monoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : Monoid M₂ :=
  { hf.Semigroup f mul,
    hf.MulOneClass f one mul with
    npow := fun n x => x ^ n
    npow_zero := hf.forall.2 fun x => by erw [← npow, pow_zero, ← one]
    npow_succ := fun n => hf.forall.2 fun x => by erw [← npow, pow_succ, ← npow, ← mul] }
#align function.surjective.monoid Function.Surjective.monoid
#align function.surjective.add_monoid Function.Surjective.addMonoid
-/

#print Function.Surjective.addMonoidWithOne /-
/-- A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits a surjective map that preserves `0`, `1` and `*` from an additive monoid with one.
See note [reducible non-instances]. -/
@[reducible]
protected def addMonoidWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [SMul ℕ M₂] [NatCast M₂]
    [AddMonoidWithOne M₁] (f : M₁ → M₂) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (nat_cast : ∀ n : ℕ, f n = n) : AddMonoidWithOne M₂ :=
  { hf.AddMonoid f zero add nsmul with
    natCast := coe
    natCast_zero := by rw [← nat_cast, Nat.cast_zero, zero]; rfl
    natCast_succ := fun n => by rw [← nat_cast, Nat.cast_succ, add, one, nat_cast]; rfl
    one := 1 }
#align function.surjective.add_monoid_with_one Function.Surjective.addMonoidWithOne
-/

#print Function.Surjective.commMonoid /-
/-- A type endowed with `1` and `*` is a commutative monoid,
if it admits a surjective map that preserves `1` and `*` from a commutative monoid.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive commutative monoid,\nif it admits a surjective map that preserves `0` and `+` to an additive commutative monoid."]
protected def commMonoid [CommMonoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoid M₂ :=
  { hf.CommSemigroup f mul, hf.Monoid f one mul npow with }
#align function.surjective.comm_monoid Function.Surjective.commMonoid
#align function.surjective.add_comm_monoid Function.Surjective.addCommMonoid
-/

#print Function.Surjective.addCommMonoidWithOne /-
/-- A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits a surjective map that preserves `0`, `1` and `*` from an additive monoid with one.
See note [reducible non-instances]. -/
@[reducible]
protected def addCommMonoidWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [SMul ℕ M₂] [NatCast M₂]
    [AddCommMonoidWithOne M₁] (f : M₁ → M₂) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (nat_cast : ∀ n : ℕ, f n = n) : AddCommMonoidWithOne M₂ :=
  { hf.AddMonoidWithOne f zero one add nsmul nat_cast, hf.AddCommMonoid _ zero _ nsmul with }
#align function.surjective.add_comm_monoid_with_one Function.Surjective.addCommMonoidWithOne
-/

#print Function.Surjective.involutiveInv /-
--See note [reducible non-instances]
/-- A type has an involutive inversion if it admits a surjective map that preserves `⁻¹` to a type
which has an involutive inversion. -/
@[reducible,
  to_additive
      "A type has an involutive negation if it admits a surjective map that\npreserves `⁻¹` to a type which has an involutive inversion."]
protected def involutiveInv {M₂ : Type _} [Inv M₂] [InvolutiveInv M₁] (f : M₁ → M₂)
    (hf : Surjective f) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) : InvolutiveInv M₂
    where
  inv := Inv.inv
  inv_inv := hf.forall.2 fun x => by erw [← inv, ← inv, inv_inv]
#align function.surjective.has_involutive_inv Function.Surjective.involutiveInv
#align function.surjective.has_involutive_neg Function.Surjective.involutiveNeg
-/

variable [Inv M₂] [Div M₂] [Pow M₂ ℤ]

#print Function.Surjective.divInvMonoid /-
/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `div_inv_monoid`
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` to a `div_inv_monoid`.
See note [reducible non-instances]. -/
@[reducible,
  to_additive SubNegMonoid
      "A type endowed with `0`, `+`, unary `-`, and binary `-` is a `sub_neg_monoid`\nif it admits a surjective map that preserves `0`, `+`, unary `-`, and binary `-` to\na `sub_neg_monoid`."]
protected def divInvMonoid [DivInvMonoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvMonoid M₂ :=
  { hf.Monoid f one mul npow, ‹Div M₂›,
    ‹Inv M₂› with
    zpow := fun n x => x ^ n
    zpow_zero' := hf.forall.2 fun x => by erw [← zpow, zpow_zero, ← one]
    zpow_succ' := fun n =>
      hf.forall.2 fun x => by erw [← zpow, ← zpow, zpow_ofNat, zpow_ofNat, pow_succ, ← mul]
    zpow_neg' := fun n =>
      hf.forall.2 fun x => by erw [← zpow, ← zpow, zpow_negSucc, zpow_ofNat, inv]
    div_eq_hMul_inv := hf.Forall₂.2 fun x y => by erw [← inv, ← mul, ← div, div_eq_mul_inv] }
#align function.surjective.div_inv_monoid Function.Surjective.divInvMonoid
#align function.surjective.sub_neg_monoid Function.Surjective.subNegMonoid
-/

#print Function.Surjective.group /-
/-- A type endowed with `1`, `*` and `⁻¹` is a group,
if it admits a surjective map that preserves `1`, `*` and `⁻¹` to a group.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive group,\nif it admits a surjective map that preserves `0` and `+` to an additive group."]
protected def group [Group M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : Group M₂ :=
  { hf.DivInvMonoid f one mul inv div npow zpow with
    hMul_left_inv := hf.forall.2 fun x => by erw [← inv, ← mul, mul_left_inv, one] <;> rfl }
#align function.surjective.group Function.Surjective.group
#align function.surjective.add_group Function.Surjective.addGroup
-/

#print Function.Surjective.addGroupWithOne /-
/-- A type endowed with `0`, `1`, `+` is an additive group with one,
if it admits a surjective map that preserves `0`, `1`, and `+` to an additive group with one.
See note [reducible non-instances]. -/
@[reducible]
protected def addGroupWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [Neg M₂] [Sub M₂] [SMul ℕ M₂]
    [SMul ℤ M₂] [NatCast M₂] [IntCast M₂] [AddGroupWithOne M₁] (f : M₁ → M₂) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : AddGroupWithOne M₂ :=
  { hf.AddMonoidWithOne f zero one add nsmul nat_cast,
    hf.AddGroup f zero add neg sub nsmul
      zsmul with
    intCast := coe
    intCast_ofNat := fun n => by rw [← int_cast, Int.cast_ofNat, nat_cast]
    intCast_negSucc := fun n => by rw [← int_cast, Int.cast_neg, Int.cast_ofNat, neg, nat_cast];
      rfl }
#align function.surjective.add_group_with_one Function.Surjective.addGroupWithOne
-/

#print Function.Surjective.commGroup /-
/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a commutative group,
if it admits a surjective map that preserves `1`, `*`, `⁻¹`, and `/` from a commutative group.
See note [reducible non-instances]. -/
@[reducible,
  to_additive
      "A type endowed with `0` and `+` is an additive commutative group,\nif it admits a surjective map that preserves `0` and `+` to an additive commutative group."]
protected def commGroup [CommGroup M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroup M₂ :=
  { hf.CommMonoid f one mul npow, hf.Group f one mul inv div npow zpow with }
#align function.surjective.comm_group Function.Surjective.commGroup
#align function.surjective.add_comm_group Function.Surjective.addCommGroup
-/

#print Function.Surjective.addCommGroupWithOne /-
/-- A type endowed with `0`, `1`, `+` is an additive commutative group with one, if it admits a
surjective map that preserves `0`, `1`, and `+` to an additive commutative group with one.
See note [reducible non-instances]. -/
@[reducible]
protected def addCommGroupWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [Neg M₂] [Sub M₂] [SMul ℕ M₂]
    [SMul ℤ M₂] [NatCast M₂] [IntCast M₂] [AddCommGroupWithOne M₁] (f : M₁ → M₂) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : AddCommGroupWithOne M₂ :=
  { hf.AddGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast,
    hf.AddCommMonoid _ zero add nsmul with }
#align function.surjective.add_comm_group_with_one Function.Surjective.addCommGroupWithOne
-/

end Surjective

end Function


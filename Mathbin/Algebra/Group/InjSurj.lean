/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.group.inj_surj
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Logic.Function.Basic
import Mathbin.Data.Int.Cast.Basic

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

/- warning: function.injective.semigroup -> Function.Injective.semigroup is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : Semigroup.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (Semigroup.toHasMul.{u2} M₂ _inst_2)) (f x) (f y))) -> (Semigroup.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : Semigroup.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (Semigroup.toMul.{u2} M₂ _inst_2)) (f x) (f y))) -> (Semigroup.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.semigroup Function.Injective.semigroupₓ'. -/
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

/- warning: function.injective.comm_semigroup -> Function.Injective.commSemigroup is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : CommSemigroup.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (Semigroup.toHasMul.{u2} M₂ (CommSemigroup.toSemigroup.{u2} M₂ _inst_2))) (f x) (f y))) -> (CommSemigroup.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : CommSemigroup.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (Semigroup.toMul.{u2} M₂ (CommSemigroup.toSemigroup.{u2} M₂ _inst_2))) (f x) (f y))) -> (CommSemigroup.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.comm_semigroup Function.Injective.commSemigroupₓ'. -/
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

/- warning: function.injective.left_cancel_semigroup -> Function.Injective.leftCancelSemigroup is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : LeftCancelSemigroup.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (Semigroup.toHasMul.{u2} M₂ (LeftCancelSemigroup.toSemigroup.{u2} M₂ _inst_2))) (f x) (f y))) -> (LeftCancelSemigroup.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : LeftCancelSemigroup.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (Semigroup.toMul.{u2} M₂ (LeftCancelSemigroup.toSemigroup.{u2} M₂ _inst_2))) (f x) (f y))) -> (LeftCancelSemigroup.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.left_cancel_semigroup Function.Injective.leftCancelSemigroupₓ'. -/
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
    mul_left_cancel := fun x y z H =>
      hf <| (mul_right_inj (f x)).1 <| by erw [← mul, ← mul, H] <;> rfl }
#align function.injective.left_cancel_semigroup Function.Injective.leftCancelSemigroup
#align function.injective.add_left_cancel_semigroup Function.Injective.addLeftCancelSemigroup

/- warning: function.injective.right_cancel_semigroup -> Function.Injective.rightCancelSemigroup is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : RightCancelSemigroup.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (Semigroup.toHasMul.{u2} M₂ (RightCancelSemigroup.toSemigroup.{u2} M₂ _inst_2))) (f x) (f y))) -> (RightCancelSemigroup.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : RightCancelSemigroup.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (Semigroup.toMul.{u2} M₂ (RightCancelSemigroup.toSemigroup.{u2} M₂ _inst_2))) (f x) (f y))) -> (RightCancelSemigroup.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.right_cancel_semigroup Function.Injective.rightCancelSemigroupₓ'. -/
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
    mul_right_cancel := fun x y z H =>
      hf <| (mul_left_inj (f y)).1 <| by erw [← mul, ← mul, H] <;> rfl }
#align function.injective.right_cancel_semigroup Function.Injective.rightCancelSemigroup
#align function.injective.add_right_cancel_semigroup Function.Injective.addRightCancelSemigroup

variable [One M₁]

/- warning: function.injective.mul_one_class -> Function.Injective.mulOneClass is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : MulOneClass.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ _inst_3))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ _inst_3)) (f x) (f y))) -> (MulOneClass.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : MulOneClass.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (MulOneClass.toOne.{u2} M₂ _inst_3)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ _inst_3)) (f x) (f y))) -> (MulOneClass.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.mul_one_class Function.Injective.mulOneClassₓ'. -/
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

variable [Pow M₁ ℕ]

/- warning: function.injective.monoid -> Function.Injective.monoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Monoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ _inst_4)))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ _inst_4))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ _inst_4)) (f x) n)) -> (Monoid.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Monoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (Monoid.toOne.{u2} M₂ _inst_4)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ _inst_4))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ _inst_4)) (f x) n)) -> (Monoid.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.monoid Function.Injective.monoidₓ'. -/
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

/- warning: function.injective.add_monoid_with_one -> Function.Injective.addMonoidWithOne is a dubious translation:
lean 3 declaration is
  forall {M₂ : Type.{u1}} {M₁ : Type.{u2}} [_inst_4 : Zero.{u2} M₁] [_inst_5 : One.{u2} M₁] [_inst_6 : Add.{u2} M₁] [_inst_7 : SMul.{0, u2} Nat M₁] [_inst_8 : NatCast.{u2} M₁] [_inst_9 : AddMonoidWithOne.{u1} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u2, succ u1} M₁ M₂ f) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 0 (OfNat.mk.{u2} M₁ 0 (Zero.zero.{u2} M₁ _inst_4)))) (OfNat.ofNat.{u1} M₂ 0 (OfNat.mk.{u1} M₂ 0 (Zero.zero.{u1} M₂ (AddZeroClass.toHasZero.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ _inst_9))))))) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 1 (OfNat.mk.{u2} M₁ 1 (One.one.{u2} M₁ _inst_5)))) (OfNat.ofNat.{u1} M₂ 1 (OfNat.mk.{u1} M₂ 1 (One.one.{u1} M₂ (AddMonoidWithOne.toOne.{u1} M₂ _inst_9))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HAdd.hAdd.{u2, u2, u2} M₁ M₁ M₁ (instHAdd.{u2} M₁ _inst_6) x y)) (HAdd.hAdd.{u1, u1, u1} M₂ M₂ M₂ (instHAdd.{u1} M₂ (AddZeroClass.toHasAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ _inst_9)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u1} M₂ (f (SMul.smul.{0, u2} Nat M₁ _inst_7 n x)) (SMul.smul.{0, u1} Nat M₂ (AddMonoid.SMul.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ _inst_9)) n (f x))) -> (forall (n : Nat), Eq.{succ u1} M₂ (f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat M₁ (HasLiftT.mk.{1, succ u2} Nat M₁ (CoeTCₓ.coe.{1, succ u2} Nat M₁ (Nat.castCoe.{u2} M₁ _inst_8))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat M₂ (HasLiftT.mk.{1, succ u1} Nat M₂ (CoeTCₓ.coe.{1, succ u1} Nat M₂ (Nat.castCoe.{u1} M₂ (AddMonoidWithOne.toNatCast.{u1} M₂ _inst_9)))) n)) -> (AddMonoidWithOne.{u2} M₁)
but is expected to have type
  forall {M₂ : Type.{u1}} {M₁ : Type.{u2}} [_inst_4 : Zero.{u2} M₁] [_inst_5 : One.{u2} M₁] [_inst_6 : Add.{u2} M₁] [_inst_7 : SMul.{0, u2} Nat M₁] [_inst_8 : NatCast.{u2} M₁] [_inst_9 : AddMonoidWithOne.{u1} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u2, succ u1} M₁ M₂ f) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 0 (Zero.toOfNat0.{u2} M₁ _inst_4))) (OfNat.ofNat.{u1} M₂ 0 (Zero.toOfNat0.{u1} M₂ (AddMonoid.toZero.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ _inst_9))))) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 1 (One.toOfNat1.{u2} M₁ _inst_5))) (OfNat.ofNat.{u1} M₂ 1 (One.toOfNat1.{u1} M₂ (AddMonoidWithOne.toOne.{u1} M₂ _inst_9)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HAdd.hAdd.{u2, u2, u2} M₁ M₁ M₁ (instHAdd.{u2} M₁ _inst_6) x y)) (HAdd.hAdd.{u1, u1, u1} M₂ M₂ M₂ (instHAdd.{u1} M₂ (AddZeroClass.toAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ _inst_9)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u1} M₂ (f (HSMul.hSMul.{0, u2, u2} Nat M₁ M₁ (instHSMul.{0, u2} Nat M₁ _inst_7) n x)) (HSMul.hSMul.{0, u1, u1} Nat M₂ M₂ (instHSMul.{0, u1} Nat M₂ (AddMonoid.SMul.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ _inst_9))) n (f x))) -> (forall (n : Nat), Eq.{succ u1} M₂ (f (Nat.cast.{u2} M₁ _inst_8 n)) (Nat.cast.{u1} M₂ (AddMonoidWithOne.toNatCast.{u1} M₂ _inst_9) n)) -> (AddMonoidWithOne.{u2} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.add_monoid_with_one Function.Injective.addMonoidWithOneₓ'. -/
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

/- warning: function.injective.left_cancel_monoid -> Function.Injective.leftCancelMonoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : LeftCancelMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (LeftCancelMonoid.toMonoid.{u2} M₂ _inst_4))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (LeftCancelMonoid.toMonoid.{u2} M₂ _inst_4)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (LeftCancelMonoid.toMonoid.{u2} M₂ _inst_4))) (f x) n)) -> (LeftCancelMonoid.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : LeftCancelMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (LeftCancelMonoid.toOne.{u2} M₂ _inst_4)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (LeftCancelMonoid.toMonoid.{u2} M₂ _inst_4)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (LeftCancelMonoid.toMonoid.{u2} M₂ _inst_4))) (f x) n)) -> (LeftCancelMonoid.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.left_cancel_monoid Function.Injective.leftCancelMonoidₓ'. -/
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

/- warning: function.injective.right_cancel_monoid -> Function.Injective.rightCancelMonoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : RightCancelMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ _inst_4))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ _inst_4)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ _inst_4))) (f x) n)) -> (RightCancelMonoid.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : RightCancelMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (RightCancelMonoid.toOne.{u2} M₂ _inst_4)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ _inst_4)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ _inst_4))) (f x) n)) -> (RightCancelMonoid.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.right_cancel_monoid Function.Injective.rightCancelMonoidₓ'. -/
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

/- warning: function.injective.cancel_monoid -> Function.Injective.cancelMonoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : CancelMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ _inst_4)))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ _inst_4))))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ _inst_4)))) (f x) n)) -> (CancelMonoid.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : CancelMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (RightCancelMonoid.toOne.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ _inst_4))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ _inst_4))))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ _inst_4)))) (f x) n)) -> (CancelMonoid.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.cancel_monoid Function.Injective.cancelMonoidₓ'. -/
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

/- warning: function.injective.comm_monoid -> Function.Injective.commMonoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : CommMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (CommMonoid.toMonoid.{u2} M₂ _inst_4))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (CommMonoid.toMonoid.{u2} M₂ _inst_4)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (CommMonoid.toMonoid.{u2} M₂ _inst_4))) (f x) n)) -> (CommMonoid.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : CommMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (Monoid.toOne.{u2} M₂ (CommMonoid.toMonoid.{u2} M₂ _inst_4))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (CommMonoid.toMonoid.{u2} M₂ _inst_4)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (CommMonoid.toMonoid.{u2} M₂ _inst_4))) (f x) n)) -> (CommMonoid.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.comm_monoid Function.Injective.commMonoidₓ'. -/
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

/- warning: function.injective.add_comm_monoid_with_one -> Function.Injective.addCommMonoidWithOne is a dubious translation:
lean 3 declaration is
  forall {M₂ : Type.{u1}} {M₁ : Type.{u2}} [_inst_4 : Zero.{u2} M₁] [_inst_5 : One.{u2} M₁] [_inst_6 : Add.{u2} M₁] [_inst_7 : SMul.{0, u2} Nat M₁] [_inst_8 : NatCast.{u2} M₁] [_inst_9 : AddCommMonoidWithOne.{u1} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u2, succ u1} M₁ M₂ f) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 0 (OfNat.mk.{u2} M₁ 0 (Zero.zero.{u2} M₁ _inst_4)))) (OfNat.ofNat.{u1} M₂ 0 (OfNat.mk.{u1} M₂ 0 (Zero.zero.{u1} M₂ (AddZeroClass.toHasZero.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₂ _inst_9)))))))) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 1 (OfNat.mk.{u2} M₁ 1 (One.one.{u2} M₁ _inst_5)))) (OfNat.ofNat.{u1} M₂ 1 (OfNat.mk.{u1} M₂ 1 (One.one.{u1} M₂ (AddMonoidWithOne.toOne.{u1} M₂ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₂ _inst_9)))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HAdd.hAdd.{u2, u2, u2} M₁ M₁ M₁ (instHAdd.{u2} M₁ _inst_6) x y)) (HAdd.hAdd.{u1, u1, u1} M₂ M₂ M₂ (instHAdd.{u1} M₂ (AddZeroClass.toHasAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₂ _inst_9))))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u1} M₂ (f (SMul.smul.{0, u2} Nat M₁ _inst_7 n x)) (SMul.smul.{0, u1} Nat M₂ (AddMonoid.SMul.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₂ _inst_9))) n (f x))) -> (forall (n : Nat), Eq.{succ u1} M₂ (f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat M₁ (HasLiftT.mk.{1, succ u2} Nat M₁ (CoeTCₓ.coe.{1, succ u2} Nat M₁ (Nat.castCoe.{u2} M₁ _inst_8))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat M₂ (HasLiftT.mk.{1, succ u1} Nat M₂ (CoeTCₓ.coe.{1, succ u1} Nat M₂ (Nat.castCoe.{u1} M₂ (AddMonoidWithOne.toNatCast.{u1} M₂ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₂ _inst_9))))) n)) -> (AddCommMonoidWithOne.{u2} M₁)
but is expected to have type
  forall {M₂ : Type.{u1}} {M₁ : Type.{u2}} [_inst_4 : Zero.{u2} M₁] [_inst_5 : One.{u2} M₁] [_inst_6 : Add.{u2} M₁] [_inst_7 : SMul.{0, u2} Nat M₁] [_inst_8 : NatCast.{u2} M₁] [_inst_9 : AddCommMonoidWithOne.{u1} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u2, succ u1} M₁ M₂ f) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 0 (Zero.toOfNat0.{u2} M₁ _inst_4))) (OfNat.ofNat.{u1} M₂ 0 (Zero.toOfNat0.{u1} M₂ (AddMonoid.toZero.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₂ _inst_9)))))) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 1 (One.toOfNat1.{u2} M₁ _inst_5))) (OfNat.ofNat.{u1} M₂ 1 (One.toOfNat1.{u1} M₂ (AddMonoidWithOne.toOne.{u1} M₂ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₂ _inst_9))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HAdd.hAdd.{u2, u2, u2} M₁ M₁ M₁ (instHAdd.{u2} M₁ _inst_6) x y)) (HAdd.hAdd.{u1, u1, u1} M₂ M₂ M₂ (instHAdd.{u1} M₂ (AddZeroClass.toAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₂ _inst_9))))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u1} M₂ (f (HSMul.hSMul.{0, u2, u2} Nat M₁ M₁ (instHSMul.{0, u2} Nat M₁ _inst_7) n x)) (HSMul.hSMul.{0, u1, u1} Nat M₂ M₂ (instHSMul.{0, u1} Nat M₂ (AddMonoid.SMul.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₂ _inst_9)))) n (f x))) -> (forall (n : Nat), Eq.{succ u1} M₂ (f (Nat.cast.{u2} M₁ _inst_8 n)) (Nat.cast.{u1} M₂ (AddMonoidWithOne.toNatCast.{u1} M₂ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₂ _inst_9)) n)) -> (AddCommMonoidWithOne.{u2} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.add_comm_monoid_with_one Function.Injective.addCommMonoidWithOneₓ'. -/
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

/- warning: function.injective.cancel_comm_monoid -> Function.Injective.cancelCommMonoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : CancelCommMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ (CancelCommMonoid.toCancelMonoid.{u2} M₂ _inst_4))))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ (CancelCommMonoid.toCancelMonoid.{u2} M₂ _inst_4)))))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ (CancelCommMonoid.toCancelMonoid.{u2} M₂ _inst_4))))) (f x) n)) -> (CancelCommMonoid.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : CancelCommMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (RightCancelMonoid.toOne.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ (CancelCommMonoid.toCancelMonoid.{u2} M₂ _inst_4)))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ (CancelCommMonoid.toCancelMonoid.{u2} M₂ _inst_4)))))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (RightCancelMonoid.toMonoid.{u2} M₂ (CancelMonoid.toRightCancelMonoid.{u2} M₂ (CancelCommMonoid.toCancelMonoid.{u2} M₂ _inst_4))))) (f x) n)) -> (CancelCommMonoid.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.cancel_comm_monoid Function.Injective.cancelCommMonoidₓ'. -/
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

/- warning: function.injective.has_involutive_inv -> Function.Injective.involutiveInv is a dubious translation:
lean 3 declaration is
  forall {M₂ : Type.{u1}} {M₁ : Type.{u2}} [_inst_4 : Inv.{u2} M₁] [_inst_5 : InvolutiveInv.{u1} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u2, succ u1} M₁ M₂ f) -> (forall (x : M₁), Eq.{succ u1} M₂ (f (Inv.inv.{u2} M₁ _inst_4 x)) (Inv.inv.{u1} M₂ (InvolutiveInv.toHasInv.{u1} M₂ _inst_5) (f x))) -> (InvolutiveInv.{u2} M₁)
but is expected to have type
  forall {M₂ : Type.{u1}} {M₁ : Type.{u2}} [_inst_4 : Inv.{u2} M₁] [_inst_5 : InvolutiveInv.{u1} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u2, succ u1} M₁ M₂ f) -> (forall (x : M₁), Eq.{succ u1} M₂ (f (Inv.inv.{u2} M₁ _inst_4 x)) (Inv.inv.{u1} M₂ (InvolutiveInv.toInv.{u1} M₂ _inst_5) (f x))) -> (InvolutiveInv.{u2} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.has_involutive_inv Function.Injective.involutiveInvₓ'. -/
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

variable [Inv M₁] [Div M₁] [Pow M₁ ℤ]

/- warning: function.injective.div_inv_monoid -> Function.Injective.divInvMonoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Inv.{u1} M₁] [_inst_5 : Div.{u1} M₁] [_inst_6 : Pow.{u1, 0} M₁ Int] [_inst_7 : DivInvMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ _inst_7))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ _inst_7)))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ _inst_4 x)) (Inv.inv.{u2} M₂ (DivInvMonoid.toHasInv.{u2} M₂ _inst_7) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ _inst_5) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ (DivInvMonoid.toHasDiv.{u2} M₂ _inst_7)) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ _inst_7))) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int _inst_6) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int (DivInvMonoid.Pow.{u2} M₂ _inst_7)) (f x) n)) -> (DivInvMonoid.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Inv.{u1} M₁] [_inst_5 : Div.{u1} M₁] [_inst_6 : Pow.{u1, 0} M₁ Int] [_inst_7 : DivInvMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (Monoid.toOne.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ _inst_7))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ _inst_7)))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ _inst_4 x)) (Inv.inv.{u2} M₂ (DivInvMonoid.toInv.{u2} M₂ _inst_7) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ _inst_5) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ (DivInvMonoid.toDiv.{u2} M₂ _inst_7)) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ _inst_7))) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int _inst_6) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int (DivInvMonoid.Pow.{u2} M₂ _inst_7)) (f x) n)) -> (DivInvMonoid.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.div_inv_monoid Function.Injective.divInvMonoidₓ'. -/
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
    div_eq_mul_inv := fun x y => hf <| by erw [div, mul, inv, div_eq_mul_inv] }
#align function.injective.div_inv_monoid Function.Injective.divInvMonoid
#align function.injective.sub_neg_monoid Function.Injective.subNegMonoid

/- warning: function.injective.division_monoid -> Function.Injective.divisionMonoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Inv.{u1} M₁] [_inst_5 : Div.{u1} M₁] [_inst_6 : Pow.{u1, 0} M₁ Int] [_inst_7 : DivisionMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ _inst_7)))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ _inst_7))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ _inst_4 x)) (Inv.inv.{u2} M₂ (DivInvMonoid.toHasInv.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ _inst_7)) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ _inst_5) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ (DivInvMonoid.toHasDiv.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ _inst_7))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ _inst_7)))) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int _inst_6) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int (DivInvMonoid.Pow.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ _inst_7))) (f x) n)) -> (DivisionMonoid.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Inv.{u1} M₁] [_inst_5 : Div.{u1} M₁] [_inst_6 : Pow.{u1, 0} M₁ Int] [_inst_7 : DivisionMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (InvOneClass.toOne.{u2} M₂ (DivInvOneMonoid.toInvOneClass.{u2} M₂ (DivisionMonoid.toDivInvOneMonoid.{u2} M₂ _inst_7)))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ _inst_7))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ _inst_4 x)) (Inv.inv.{u2} M₂ (InvOneClass.toInv.{u2} M₂ (DivInvOneMonoid.toInvOneClass.{u2} M₂ (DivisionMonoid.toDivInvOneMonoid.{u2} M₂ _inst_7))) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ _inst_5) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ (DivInvMonoid.toDiv.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ _inst_7))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ _inst_7)))) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int _inst_6) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int (DivInvMonoid.Pow.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ _inst_7))) (f x) n)) -> (DivisionMonoid.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.division_monoid Function.Injective.divisionMonoidₓ'. -/
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
    inv_eq_of_mul := fun x y h =>
      hf <| by erw [inv, inv_eq_of_mul_eq_one_right (by erw [← mul, h, one])] }
#align function.injective.division_monoid Function.Injective.divisionMonoid
#align function.injective.subtraction_monoid Function.Injective.subtractionMonoid

/- warning: function.injective.division_comm_monoid -> Function.Injective.divisionCommMonoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Inv.{u1} M₁] [_inst_5 : Div.{u1} M₁] [_inst_6 : Pow.{u1, 0} M₁ Int] [_inst_7 : DivisionCommMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7))))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7)))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ _inst_4 x)) (Inv.inv.{u2} M₂ (DivInvMonoid.toHasInv.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7))) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ _inst_5) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ (DivInvMonoid.toHasDiv.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7))))) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int _inst_6) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int (DivInvMonoid.Pow.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7)))) (f x) n)) -> (DivisionCommMonoid.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Inv.{u1} M₁] [_inst_5 : Div.{u1} M₁] [_inst_6 : Pow.{u1, 0} M₁ Int] [_inst_7 : DivisionCommMonoid.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (InvOneClass.toOne.{u2} M₂ (DivInvOneMonoid.toInvOneClass.{u2} M₂ (DivisionMonoid.toDivInvOneMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7)))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ _inst_4 x)) (Inv.inv.{u2} M₂ (InvOneClass.toInv.{u2} M₂ (DivInvOneMonoid.toInvOneClass.{u2} M₂ (DivisionMonoid.toDivInvOneMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7)))) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ _inst_5) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ (DivInvMonoid.toDiv.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7))))) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int _inst_6) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int (DivInvMonoid.Pow.{u2} M₂ (DivisionMonoid.toDivInvMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ _inst_7)))) (f x) n)) -> (DivisionCommMonoid.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.division_comm_monoid Function.Injective.divisionCommMonoidₓ'. -/
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

/- warning: function.injective.group -> Function.Injective.group is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Inv.{u1} M₁] [_inst_5 : Div.{u1} M₁] [_inst_6 : Pow.{u1, 0} M₁ Int] [_inst_7 : Group.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ _inst_7)))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ _inst_7))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ _inst_4 x)) (Inv.inv.{u2} M₂ (DivInvMonoid.toHasInv.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ _inst_7)) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ _inst_5) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ (DivInvMonoid.toHasDiv.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ _inst_7))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ _inst_7)))) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int _inst_6) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int (DivInvMonoid.Pow.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ _inst_7))) (f x) n)) -> (Group.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Inv.{u1} M₁] [_inst_5 : Div.{u1} M₁] [_inst_6 : Pow.{u1, 0} M₁ Int] [_inst_7 : Group.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (InvOneClass.toOne.{u2} M₂ (DivInvOneMonoid.toInvOneClass.{u2} M₂ (DivisionMonoid.toDivInvOneMonoid.{u2} M₂ (Group.toDivisionMonoid.{u2} M₂ _inst_7))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ _inst_7))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ _inst_4 x)) (Inv.inv.{u2} M₂ (InvOneClass.toInv.{u2} M₂ (DivInvOneMonoid.toInvOneClass.{u2} M₂ (DivisionMonoid.toDivInvOneMonoid.{u2} M₂ (Group.toDivisionMonoid.{u2} M₂ _inst_7)))) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ _inst_5) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ (DivInvMonoid.toDiv.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ _inst_7))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ _inst_7)))) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int _inst_6) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int (DivInvMonoid.Pow.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ _inst_7))) (f x) n)) -> (Group.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.group Function.Injective.groupₓ'. -/
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
    mul_left_inv := fun x => hf <| by erw [mul, inv, mul_left_inv, one] }
#align function.injective.group Function.Injective.group
#align function.injective.add_group Function.Injective.addGroup

/- warning: function.injective.add_group_with_one -> Function.Injective.addGroupWithOne is a dubious translation:
lean 3 declaration is
  forall {M₂ : Type.{u1}} {M₁ : Type.{u2}} [_inst_7 : Zero.{u2} M₁] [_inst_8 : One.{u2} M₁] [_inst_9 : Add.{u2} M₁] [_inst_10 : SMul.{0, u2} Nat M₁] [_inst_11 : Neg.{u2} M₁] [_inst_12 : Sub.{u2} M₁] [_inst_13 : SMul.{0, u2} Int M₁] [_inst_14 : NatCast.{u2} M₁] [_inst_15 : IntCast.{u2} M₁] [_inst_16 : AddGroupWithOne.{u1} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u2, succ u1} M₁ M₂ f) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 0 (OfNat.mk.{u2} M₁ 0 (Zero.zero.{u2} M₁ _inst_7)))) (OfNat.ofNat.{u1} M₂ 0 (OfNat.mk.{u1} M₂ 0 (Zero.zero.{u1} M₂ (AddZeroClass.toHasZero.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ _inst_16)))))))) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 1 (OfNat.mk.{u2} M₁ 1 (One.one.{u2} M₁ _inst_8)))) (OfNat.ofNat.{u1} M₂ 1 (OfNat.mk.{u1} M₂ 1 (One.one.{u1} M₂ (AddMonoidWithOne.toOne.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ _inst_16)))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HAdd.hAdd.{u2, u2, u2} M₁ M₁ M₁ (instHAdd.{u2} M₁ _inst_9) x y)) (HAdd.hAdd.{u1, u1, u1} M₂ M₂ M₂ (instHAdd.{u1} M₂ (AddZeroClass.toHasAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ _inst_16))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u1} M₂ (f (Neg.neg.{u2} M₁ _inst_11 x)) (Neg.neg.{u1} M₂ (SubNegMonoid.toHasNeg.{u1} M₂ (AddGroup.toSubNegMonoid.{u1} M₂ (AddGroupWithOne.toAddGroup.{u1} M₂ _inst_16))) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HSub.hSub.{u2, u2, u2} M₁ M₁ M₁ (instHSub.{u2} M₁ _inst_12) x y)) (HSub.hSub.{u1, u1, u1} M₂ M₂ M₂ (instHSub.{u1} M₂ (SubNegMonoid.toHasSub.{u1} M₂ (AddGroup.toSubNegMonoid.{u1} M₂ (AddGroupWithOne.toAddGroup.{u1} M₂ _inst_16)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u1} M₂ (f (SMul.smul.{0, u2} Nat M₁ _inst_10 n x)) (SMul.smul.{0, u1} Nat M₂ (AddMonoid.SMul.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ _inst_16))) n (f x))) -> (forall (x : M₁) (n : Int), Eq.{succ u1} M₂ (f (SMul.smul.{0, u2} Int M₁ _inst_13 n x)) (SMul.smul.{0, u1} Int M₂ (SubNegMonoid.SMulInt.{u1} M₂ (AddGroup.toSubNegMonoid.{u1} M₂ (AddGroupWithOne.toAddGroup.{u1} M₂ _inst_16))) n (f x))) -> (forall (n : Nat), Eq.{succ u1} M₂ (f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat M₁ (HasLiftT.mk.{1, succ u2} Nat M₁ (CoeTCₓ.coe.{1, succ u2} Nat M₁ (Nat.castCoe.{u2} M₁ _inst_14))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat M₂ (HasLiftT.mk.{1, succ u1} Nat M₂ (CoeTCₓ.coe.{1, succ u1} Nat M₂ (Nat.castCoe.{u1} M₂ (AddMonoidWithOne.toNatCast.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ _inst_16))))) n)) -> (forall (n : Int), Eq.{succ u1} M₂ (f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int M₁ (HasLiftT.mk.{1, succ u2} Int M₁ (CoeTCₓ.coe.{1, succ u2} Int M₁ (Int.castCoe.{u2} M₁ _inst_15))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int M₂ (HasLiftT.mk.{1, succ u1} Int M₂ (CoeTCₓ.coe.{1, succ u1} Int M₂ (Int.castCoe.{u1} M₂ (AddGroupWithOne.toHasIntCast.{u1} M₂ _inst_16)))) n)) -> (AddGroupWithOne.{u2} M₁)
but is expected to have type
  forall {M₂ : Type.{u1}} {M₁ : Type.{u2}} [_inst_7 : Zero.{u2} M₁] [_inst_8 : One.{u2} M₁] [_inst_9 : Add.{u2} M₁] [_inst_10 : SMul.{0, u2} Nat M₁] [_inst_11 : Neg.{u2} M₁] [_inst_12 : Sub.{u2} M₁] [_inst_13 : SMul.{0, u2} Int M₁] [_inst_14 : NatCast.{u2} M₁] [_inst_15 : IntCast.{u2} M₁] [_inst_16 : AddGroupWithOne.{u1} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u2, succ u1} M₁ M₂ f) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 0 (Zero.toOfNat0.{u2} M₁ _inst_7))) (OfNat.ofNat.{u1} M₂ 0 (Zero.toOfNat0.{u1} M₂ (NegZeroClass.toZero.{u1} M₂ (SubNegZeroMonoid.toNegZeroClass.{u1} M₂ (SubtractionMonoid.toSubNegZeroMonoid.{u1} M₂ (AddGroup.toSubtractionMonoid.{u1} M₂ (AddGroupWithOne.toAddGroup.{u1} M₂ _inst_16)))))))) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 1 (One.toOfNat1.{u2} M₁ _inst_8))) (OfNat.ofNat.{u1} M₂ 1 (One.toOfNat1.{u1} M₂ (AddMonoidWithOne.toOne.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ _inst_16))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HAdd.hAdd.{u2, u2, u2} M₁ M₁ M₁ (instHAdd.{u2} M₁ _inst_9) x y)) (HAdd.hAdd.{u1, u1, u1} M₂ M₂ M₂ (instHAdd.{u1} M₂ (AddZeroClass.toAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ _inst_16))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u1} M₂ (f (Neg.neg.{u2} M₁ _inst_11 x)) (Neg.neg.{u1} M₂ (AddGroupWithOne.toNeg.{u1} M₂ _inst_16) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HSub.hSub.{u2, u2, u2} M₁ M₁ M₁ (instHSub.{u2} M₁ _inst_12) x y)) (HSub.hSub.{u1, u1, u1} M₂ M₂ M₂ (instHSub.{u1} M₂ (AddGroupWithOne.toSub.{u1} M₂ _inst_16)) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u1} M₂ (f (HSMul.hSMul.{0, u2, u2} Nat M₁ M₁ (instHSMul.{0, u2} Nat M₁ _inst_10) n x)) (HSMul.hSMul.{0, u1, u1} Nat M₂ M₂ (instHSMul.{0, u1} Nat M₂ (AddMonoid.SMul.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ _inst_16)))) n (f x))) -> (forall (x : M₁) (n : Int), Eq.{succ u1} M₂ (f (HSMul.hSMul.{0, u2, u2} Int M₁ M₁ (instHSMul.{0, u2} Int M₁ _inst_13) n x)) (HSMul.hSMul.{0, u1, u1} Int M₂ M₂ (instHSMul.{0, u1} Int M₂ (SubNegMonoid.SMulInt.{u1} M₂ (AddGroup.toSubNegMonoid.{u1} M₂ (AddGroupWithOne.toAddGroup.{u1} M₂ _inst_16)))) n (f x))) -> (forall (n : Nat), Eq.{succ u1} M₂ (f (Nat.cast.{u2} M₁ _inst_14 n)) (Nat.cast.{u1} M₂ (AddMonoidWithOne.toNatCast.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ _inst_16)) n)) -> (forall (n : Int), Eq.{succ u1} M₂ (f (Int.cast.{u2} M₁ _inst_15 n)) (Int.cast.{u1} M₂ (AddGroupWithOne.toIntCast.{u1} M₂ _inst_16) n)) -> (AddGroupWithOne.{u2} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.add_group_with_one Function.Injective.addGroupWithOneₓ'. -/
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

/- warning: function.injective.comm_group -> Function.Injective.commGroup is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Inv.{u1} M₁] [_inst_5 : Div.{u1} M₁] [_inst_6 : Pow.{u1, 0} M₁ Int] [_inst_7 : CommGroup.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ _inst_2)))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ (MulOneClass.toHasOne.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ (CommGroup.toGroup.{u2} M₂ _inst_7))))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toHasMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ (CommGroup.toGroup.{u2} M₂ _inst_7)))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ _inst_4 x)) (Inv.inv.{u2} M₂ (DivInvMonoid.toHasInv.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ (CommGroup.toGroup.{u2} M₂ _inst_7))) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ _inst_5) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ (DivInvMonoid.toHasDiv.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ (CommGroup.toGroup.{u2} M₂ _inst_7)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ (CommGroup.toGroup.{u2} M₂ _inst_7))))) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int _inst_6) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int (DivInvMonoid.Pow.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ (CommGroup.toGroup.{u2} M₂ _inst_7)))) (f x) n)) -> (CommGroup.{u1} M₁)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u1} M₁] [_inst_2 : One.{u1} M₁] [_inst_3 : Pow.{u1, 0} M₁ Nat] [_inst_4 : Inv.{u1} M₁] [_inst_5 : Div.{u1} M₁] [_inst_6 : Pow.{u1, 0} M₁ Int] [_inst_7 : CommGroup.{u2} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ _inst_2))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ (InvOneClass.toOne.{u2} M₂ (DivInvOneMonoid.toInvOneClass.{u2} M₂ (DivisionMonoid.toDivInvOneMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ (CommGroup.toDivisionCommMonoid.{u2} M₂ _inst_7)))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ (MulOneClass.toMul.{u2} M₂ (Monoid.toMulOneClass.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ (CommGroup.toGroup.{u2} M₂ _inst_7)))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ _inst_4 x)) (Inv.inv.{u2} M₂ (InvOneClass.toInv.{u2} M₂ (DivInvOneMonoid.toInvOneClass.{u2} M₂ (DivisionMonoid.toDivInvOneMonoid.{u2} M₂ (DivisionCommMonoid.toDivisionMonoid.{u2} M₂ (CommGroup.toDivisionCommMonoid.{u2} M₂ _inst_7))))) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ _inst_5) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ (DivInvMonoid.toDiv.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ (CommGroup.toGroup.{u2} M₂ _inst_7)))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat _inst_3) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat (Monoid.Pow.{u2} M₂ (DivInvMonoid.toMonoid.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ (CommGroup.toGroup.{u2} M₂ _inst_7))))) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int _inst_6) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int (DivInvMonoid.Pow.{u2} M₂ (Group.toDivInvMonoid.{u2} M₂ (CommGroup.toGroup.{u2} M₂ _inst_7)))) (f x) n)) -> (CommGroup.{u1} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.comm_group Function.Injective.commGroupₓ'. -/
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

/- warning: function.injective.add_comm_group_with_one -> Function.Injective.addCommGroupWithOne is a dubious translation:
lean 3 declaration is
  forall {M₂ : Type.{u1}} {M₁ : Type.{u2}} [_inst_7 : Zero.{u2} M₁] [_inst_8 : One.{u2} M₁] [_inst_9 : Add.{u2} M₁] [_inst_10 : SMul.{0, u2} Nat M₁] [_inst_11 : Neg.{u2} M₁] [_inst_12 : Sub.{u2} M₁] [_inst_13 : SMul.{0, u2} Int M₁] [_inst_14 : NatCast.{u2} M₁] [_inst_15 : IntCast.{u2} M₁] [_inst_16 : AddCommGroupWithOne.{u1} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u2, succ u1} M₁ M₂ f) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 0 (OfNat.mk.{u2} M₁ 0 (Zero.zero.{u2} M₁ _inst_7)))) (OfNat.ofNat.{u1} M₂ 0 (OfNat.mk.{u1} M₂ 0 (Zero.zero.{u1} M₂ (AddZeroClass.toHasZero.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16))))))))) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 1 (OfNat.mk.{u2} M₁ 1 (One.one.{u2} M₁ _inst_8)))) (OfNat.ofNat.{u1} M₂ 1 (OfNat.mk.{u1} M₂ 1 (One.one.{u1} M₂ (AddMonoidWithOne.toOne.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16))))))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HAdd.hAdd.{u2, u2, u2} M₁ M₁ M₁ (instHAdd.{u2} M₁ _inst_9) x y)) (HAdd.hAdd.{u1, u1, u1} M₂ M₂ M₂ (instHAdd.{u1} M₂ (AddZeroClass.toHasAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16)))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u1} M₂ (f (Neg.neg.{u2} M₁ _inst_11 x)) (Neg.neg.{u1} M₂ (SubNegMonoid.toHasNeg.{u1} M₂ (AddGroup.toSubNegMonoid.{u1} M₂ (AddGroupWithOne.toAddGroup.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16)))) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HSub.hSub.{u2, u2, u2} M₁ M₁ M₁ (instHSub.{u2} M₁ _inst_12) x y)) (HSub.hSub.{u1, u1, u1} M₂ M₂ M₂ (instHSub.{u1} M₂ (SubNegMonoid.toHasSub.{u1} M₂ (AddGroup.toSubNegMonoid.{u1} M₂ (AddGroupWithOne.toAddGroup.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16))))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u1} M₂ (f (SMul.smul.{0, u2} Nat M₁ _inst_10 n x)) (SMul.smul.{0, u1} Nat M₂ (AddMonoid.SMul.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16)))) n (f x))) -> (forall (x : M₁) (n : Int), Eq.{succ u1} M₂ (f (SMul.smul.{0, u2} Int M₁ _inst_13 n x)) (SMul.smul.{0, u1} Int M₂ (SubNegMonoid.SMulInt.{u1} M₂ (AddGroup.toSubNegMonoid.{u1} M₂ (AddGroupWithOne.toAddGroup.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16)))) n (f x))) -> (forall (n : Nat), Eq.{succ u1} M₂ (f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat M₁ (HasLiftT.mk.{1, succ u2} Nat M₁ (CoeTCₓ.coe.{1, succ u2} Nat M₁ (Nat.castCoe.{u2} M₁ _inst_14))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat M₂ (HasLiftT.mk.{1, succ u1} Nat M₂ (CoeTCₓ.coe.{1, succ u1} Nat M₂ (Nat.castCoe.{u1} M₂ (AddMonoidWithOne.toNatCast.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16)))))) n)) -> (forall (n : Int), Eq.{succ u1} M₂ (f ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int M₁ (HasLiftT.mk.{1, succ u2} Int M₁ (CoeTCₓ.coe.{1, succ u2} Int M₁ (Int.castCoe.{u2} M₁ _inst_15))) n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int M₂ (HasLiftT.mk.{1, succ u1} Int M₂ (CoeTCₓ.coe.{1, succ u1} Int M₂ (Int.castCoe.{u1} M₂ (AddGroupWithOne.toHasIntCast.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16))))) n)) -> (AddCommGroupWithOne.{u2} M₁)
but is expected to have type
  forall {M₂ : Type.{u1}} {M₁ : Type.{u2}} [_inst_7 : Zero.{u2} M₁] [_inst_8 : One.{u2} M₁] [_inst_9 : Add.{u2} M₁] [_inst_10 : SMul.{0, u2} Nat M₁] [_inst_11 : Neg.{u2} M₁] [_inst_12 : Sub.{u2} M₁] [_inst_13 : SMul.{0, u2} Int M₁] [_inst_14 : NatCast.{u2} M₁] [_inst_15 : IntCast.{u2} M₁] [_inst_16 : AddCommGroupWithOne.{u1} M₂] (f : M₁ -> M₂), (Function.Injective.{succ u2, succ u1} M₁ M₂ f) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 0 (Zero.toOfNat0.{u2} M₁ _inst_7))) (OfNat.ofNat.{u1} M₂ 0 (Zero.toOfNat0.{u1} M₂ (NegZeroClass.toZero.{u1} M₂ (SubNegZeroMonoid.toNegZeroClass.{u1} M₂ (SubtractionMonoid.toSubNegZeroMonoid.{u1} M₂ (SubtractionCommMonoid.toSubtractionMonoid.{u1} M₂ (AddCommGroup.toDivisionAddCommMonoid.{u1} M₂ (AddCommGroupWithOne.toAddCommGroup.{u1} M₂ _inst_16))))))))) -> (Eq.{succ u1} M₂ (f (OfNat.ofNat.{u2} M₁ 1 (One.toOfNat1.{u2} M₁ _inst_8))) (OfNat.ofNat.{u1} M₂ 1 (One.toOfNat1.{u1} M₂ (AddCommGroupWithOne.toOne.{u1} M₂ _inst_16)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HAdd.hAdd.{u2, u2, u2} M₁ M₁ M₁ (instHAdd.{u2} M₁ _inst_9) x y)) (HAdd.hAdd.{u1, u1, u1} M₂ M₂ M₂ (instHAdd.{u1} M₂ (AddZeroClass.toAdd.{u1} M₂ (AddMonoid.toAddZeroClass.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16)))))) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u1} M₂ (f (Neg.neg.{u2} M₁ _inst_11 x)) (Neg.neg.{u1} M₂ (AddGroupWithOne.toNeg.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16)) (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u1} M₂ (f (HSub.hSub.{u2, u2, u2} M₁ M₁ M₁ (instHSub.{u2} M₁ _inst_12) x y)) (HSub.hSub.{u1, u1, u1} M₂ M₂ M₂ (instHSub.{u1} M₂ (AddGroupWithOne.toSub.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16))) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u1} M₂ (f (HSMul.hSMul.{0, u2, u2} Nat M₁ M₁ (instHSMul.{0, u2} Nat M₁ _inst_10) n x)) (HSMul.hSMul.{0, u1, u1} Nat M₂ M₂ (instHSMul.{0, u1} Nat M₂ (AddMonoid.SMul.{u1} M₂ (AddMonoidWithOne.toAddMonoid.{u1} M₂ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16))))) n (f x))) -> (forall (x : M₁) (n : Int), Eq.{succ u1} M₂ (f (HSMul.hSMul.{0, u2, u2} Int M₁ M₁ (instHSMul.{0, u2} Int M₁ _inst_13) n x)) (HSMul.hSMul.{0, u1, u1} Int M₂ M₂ (instHSMul.{0, u1} Int M₂ (SubNegMonoid.SMulInt.{u1} M₂ (AddGroup.toSubNegMonoid.{u1} M₂ (AddGroupWithOne.toAddGroup.{u1} M₂ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₂ _inst_16))))) n (f x))) -> (forall (n : Nat), Eq.{succ u1} M₂ (f (Nat.cast.{u2} M₁ _inst_14 n)) (Nat.cast.{u1} M₂ (AddCommGroupWithOne.toNatCast.{u1} M₂ _inst_16) n)) -> (forall (n : Int), Eq.{succ u1} M₂ (f (Int.cast.{u2} M₁ _inst_15 n)) (Int.cast.{u1} M₂ (AddCommGroupWithOne.toIntCast.{u1} M₂ _inst_16) n)) -> (AddCommGroupWithOne.{u2} M₁)
Case conversion may be inaccurate. Consider using '#align function.injective.add_comm_group_with_one Function.Injective.addCommGroupWithOneₓ'. -/
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

end Injective

/-!
### Surjective
-/


namespace Surjective

variable {M₁ : Type _} {M₂ : Type _} [Mul M₂]

/- warning: function.surjective.semigroup -> Function.Surjective.semigroup is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : Semigroup.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (Semigroup.toHasMul.{u1} M₁ _inst_2)) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (Semigroup.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : Semigroup.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (Semigroup.toMul.{u1} M₁ _inst_2)) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (Semigroup.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.semigroup Function.Surjective.semigroupₓ'. -/
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

/- warning: function.surjective.comm_semigroup -> Function.Surjective.commSemigroup is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : CommSemigroup.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (Semigroup.toHasMul.{u1} M₁ (CommSemigroup.toSemigroup.{u1} M₁ _inst_2))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (CommSemigroup.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : CommSemigroup.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (Semigroup.toMul.{u1} M₁ (CommSemigroup.toSemigroup.{u1} M₁ _inst_2))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (CommSemigroup.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.comm_semigroup Function.Surjective.commSemigroupₓ'. -/
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

variable [One M₂]

/- warning: function.surjective.mul_one_class -> Function.Surjective.mulOneClass is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : MulOneClass.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (MulOneClass.toHasOne.{u1} M₁ _inst_3))))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_2)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ _inst_3)) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (MulOneClass.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : MulOneClass.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (MulOneClass.toOne.{u1} M₁ _inst_3)))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ _inst_2))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toMul.{u1} M₁ _inst_3)) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (MulOneClass.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.mul_one_class Function.Surjective.mulOneClassₓ'. -/
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

variable [Pow M₂ ℕ]

/- warning: function.surjective.monoid -> Function.Surjective.monoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : Pow.{u2, 0} M₂ Nat] [_inst_4 : Monoid.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (MulOneClass.toHasOne.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ _inst_4)))))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_2)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ _inst_4))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat (Monoid.Pow.{u1} M₁ _inst_4)) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat _inst_3) (f x) n)) -> (Monoid.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : Pow.{u2, 0} M₂ Nat] [_inst_4 : Monoid.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (Monoid.toOne.{u1} M₁ _inst_4)))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ _inst_2))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toMul.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ _inst_4))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat (Monoid.Pow.{u1} M₁ _inst_4)) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat _inst_3) (f x) n)) -> (Monoid.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.monoid Function.Surjective.monoidₓ'. -/
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

/- warning: function.surjective.add_monoid_with_one -> Function.Surjective.addMonoidWithOne is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_4 : Zero.{u2} M₂] [_inst_5 : One.{u2} M₂] [_inst_6 : Add.{u2} M₂] [_inst_7 : SMul.{0, u2} Nat M₂] [_inst_8 : NatCast.{u2} M₂] [_inst_9 : AddMonoidWithOne.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 0 (OfNat.mk.{u1} M₁ 0 (Zero.zero.{u1} M₁ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ _inst_9))))))) (OfNat.ofNat.{u2} M₂ 0 (OfNat.mk.{u2} M₂ 0 (Zero.zero.{u2} M₂ _inst_4)))) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (AddMonoidWithOne.toOne.{u1} M₁ _inst_9))))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_5)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HAdd.hAdd.{u1, u1, u1} M₁ M₁ M₁ (instHAdd.{u1} M₁ (AddZeroClass.toHasAdd.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ _inst_9)))) x y)) (HAdd.hAdd.{u2, u2, u2} M₂ M₂ M₂ (instHAdd.{u2} M₂ _inst_6) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (SMul.smul.{0, u1} Nat M₁ (AddMonoid.SMul.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ _inst_9)) n x)) (SMul.smul.{0, u2} Nat M₂ _inst_7 n (f x))) -> (forall (n : Nat), Eq.{succ u2} M₂ (f ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat M₁ (HasLiftT.mk.{1, succ u1} Nat M₁ (CoeTCₓ.coe.{1, succ u1} Nat M₁ (Nat.castCoe.{u1} M₁ (AddMonoidWithOne.toNatCast.{u1} M₁ _inst_9)))) n)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat M₂ (HasLiftT.mk.{1, succ u2} Nat M₂ (CoeTCₓ.coe.{1, succ u2} Nat M₂ (Nat.castCoe.{u2} M₂ _inst_8))) n)) -> (AddMonoidWithOne.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_4 : Zero.{u2} M₂] [_inst_5 : One.{u2} M₂] [_inst_6 : Add.{u2} M₂] [_inst_7 : SMul.{0, u2} Nat M₂] [_inst_8 : NatCast.{u2} M₂] [_inst_9 : AddMonoidWithOne.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 0 (Zero.toOfNat0.{u1} M₁ (AddMonoid.toZero.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ _inst_9))))) (OfNat.ofNat.{u2} M₂ 0 (Zero.toOfNat0.{u2} M₂ _inst_4))) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (AddMonoidWithOne.toOne.{u1} M₁ _inst_9)))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ _inst_5))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HAdd.hAdd.{u1, u1, u1} M₁ M₁ M₁ (instHAdd.{u1} M₁ (AddZeroClass.toAdd.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ _inst_9)))) x y)) (HAdd.hAdd.{u2, u2, u2} M₂ M₂ M₂ (instHAdd.{u2} M₂ _inst_6) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HSMul.hSMul.{0, u1, u1} Nat M₁ M₁ (instHSMul.{0, u1} Nat M₁ (AddMonoid.SMul.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ _inst_9))) n x)) (HSMul.hSMul.{0, u2, u2} Nat M₂ M₂ (instHSMul.{0, u2} Nat M₂ _inst_7) n (f x))) -> (forall (n : Nat), Eq.{succ u2} M₂ (f (Nat.cast.{u1} M₁ (AddMonoidWithOne.toNatCast.{u1} M₁ _inst_9) n)) (Nat.cast.{u2} M₂ _inst_8 n)) -> (AddMonoidWithOne.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.add_monoid_with_one Function.Surjective.addMonoidWithOneₓ'. -/
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
    natCast_zero := by
      rw [← nat_cast, Nat.cast_zero, zero]
      rfl
    natCast_succ := fun n =>
      by
      rw [← nat_cast, Nat.cast_succ, add, one, nat_cast]
      rfl
    one := 1 }
#align function.surjective.add_monoid_with_one Function.Surjective.addMonoidWithOne

/- warning: function.surjective.comm_monoid -> Function.Surjective.commMonoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : Pow.{u2, 0} M₂ Nat] [_inst_4 : CommMonoid.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (MulOneClass.toHasOne.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (CommMonoid.toMonoid.{u1} M₁ _inst_4))))))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_2)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (CommMonoid.toMonoid.{u1} M₁ _inst_4)))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat (Monoid.Pow.{u1} M₁ (CommMonoid.toMonoid.{u1} M₁ _inst_4))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat _inst_3) (f x) n)) -> (CommMonoid.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : Pow.{u2, 0} M₂ Nat] [_inst_4 : CommMonoid.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (Monoid.toOne.{u1} M₁ (CommMonoid.toMonoid.{u1} M₁ _inst_4))))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ _inst_2))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toMul.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (CommMonoid.toMonoid.{u1} M₁ _inst_4)))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat (Monoid.Pow.{u1} M₁ (CommMonoid.toMonoid.{u1} M₁ _inst_4))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat _inst_3) (f x) n)) -> (CommMonoid.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.comm_monoid Function.Surjective.commMonoidₓ'. -/
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

/- warning: function.surjective.add_comm_monoid_with_one -> Function.Surjective.addCommMonoidWithOne is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_4 : Zero.{u2} M₂] [_inst_5 : One.{u2} M₂] [_inst_6 : Add.{u2} M₂] [_inst_7 : SMul.{0, u2} Nat M₂] [_inst_8 : NatCast.{u2} M₂] [_inst_9 : AddCommMonoidWithOne.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 0 (OfNat.mk.{u1} M₁ 0 (Zero.zero.{u1} M₁ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₁ _inst_9)))))))) (OfNat.ofNat.{u2} M₂ 0 (OfNat.mk.{u2} M₂ 0 (Zero.zero.{u2} M₂ _inst_4)))) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (AddMonoidWithOne.toOne.{u1} M₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₁ _inst_9)))))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_5)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HAdd.hAdd.{u1, u1, u1} M₁ M₁ M₁ (instHAdd.{u1} M₁ (AddZeroClass.toHasAdd.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₁ _inst_9))))) x y)) (HAdd.hAdd.{u2, u2, u2} M₂ M₂ M₂ (instHAdd.{u2} M₂ _inst_6) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (SMul.smul.{0, u1} Nat M₁ (AddMonoid.SMul.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₁ _inst_9))) n x)) (SMul.smul.{0, u2} Nat M₂ _inst_7 n (f x))) -> (forall (n : Nat), Eq.{succ u2} M₂ (f ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat M₁ (HasLiftT.mk.{1, succ u1} Nat M₁ (CoeTCₓ.coe.{1, succ u1} Nat M₁ (Nat.castCoe.{u1} M₁ (AddMonoidWithOne.toNatCast.{u1} M₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₁ _inst_9))))) n)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat M₂ (HasLiftT.mk.{1, succ u2} Nat M₂ (CoeTCₓ.coe.{1, succ u2} Nat M₂ (Nat.castCoe.{u2} M₂ _inst_8))) n)) -> (AddCommMonoidWithOne.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_4 : Zero.{u2} M₂] [_inst_5 : One.{u2} M₂] [_inst_6 : Add.{u2} M₂] [_inst_7 : SMul.{0, u2} Nat M₂] [_inst_8 : NatCast.{u2} M₂] [_inst_9 : AddCommMonoidWithOne.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 0 (Zero.toOfNat0.{u1} M₁ (AddMonoid.toZero.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₁ _inst_9)))))) (OfNat.ofNat.{u2} M₂ 0 (Zero.toOfNat0.{u2} M₂ _inst_4))) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (AddMonoidWithOne.toOne.{u1} M₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₁ _inst_9))))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ _inst_5))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HAdd.hAdd.{u1, u1, u1} M₁ M₁ M₁ (instHAdd.{u1} M₁ (AddZeroClass.toAdd.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₁ _inst_9))))) x y)) (HAdd.hAdd.{u2, u2, u2} M₂ M₂ M₂ (instHAdd.{u2} M₂ _inst_6) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HSMul.hSMul.{0, u1, u1} Nat M₁ M₁ (instHSMul.{0, u1} Nat M₁ (AddMonoid.SMul.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₁ _inst_9)))) n x)) (HSMul.hSMul.{0, u2, u2} Nat M₂ M₂ (instHSMul.{0, u2} Nat M₂ _inst_7) n (f x))) -> (forall (n : Nat), Eq.{succ u2} M₂ (f (Nat.cast.{u1} M₁ (AddMonoidWithOne.toNatCast.{u1} M₁ (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} M₁ _inst_9)) n)) (Nat.cast.{u2} M₂ _inst_8 n)) -> (AddCommMonoidWithOne.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.add_comm_monoid_with_one Function.Surjective.addCommMonoidWithOneₓ'. -/
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

/- warning: function.surjective.has_involutive_inv -> Function.Surjective.involutiveInv is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_4 : Inv.{u2} M₂] [_inst_5 : InvolutiveInv.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ (InvolutiveInv.toHasInv.{u1} M₁ _inst_5) x)) (Inv.inv.{u2} M₂ _inst_4 (f x))) -> (InvolutiveInv.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_4 : Inv.{u2} M₂] [_inst_5 : InvolutiveInv.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ (InvolutiveInv.toInv.{u1} M₁ _inst_5) x)) (Inv.inv.{u2} M₂ _inst_4 (f x))) -> (InvolutiveInv.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.has_involutive_inv Function.Surjective.involutiveInvₓ'. -/
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

variable [Inv M₂] [Div M₂] [Pow M₂ ℤ]

/- warning: function.surjective.div_inv_monoid -> Function.Surjective.divInvMonoid is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : Pow.{u2, 0} M₂ Nat] [_inst_4 : Inv.{u2} M₂] [_inst_5 : Div.{u2} M₂] [_inst_6 : Pow.{u2, 0} M₂ Int] [_inst_7 : DivInvMonoid.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (MulOneClass.toHasOne.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ _inst_7))))))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_2)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ _inst_7)))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ (DivInvMonoid.toHasInv.{u1} M₁ _inst_7) x)) (Inv.inv.{u2} M₂ _inst_4 (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ (DivInvMonoid.toHasDiv.{u1} M₁ _inst_7)) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ _inst_5) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat (Monoid.Pow.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ _inst_7))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat _inst_3) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int (DivInvMonoid.Pow.{u1} M₁ _inst_7)) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int _inst_6) (f x) n)) -> (DivInvMonoid.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : Pow.{u2, 0} M₂ Nat] [_inst_4 : Inv.{u2} M₂] [_inst_5 : Div.{u2} M₂] [_inst_6 : Pow.{u2, 0} M₂ Int] [_inst_7 : DivInvMonoid.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (Monoid.toOne.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ _inst_7))))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ _inst_2))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toMul.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ _inst_7)))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ (DivInvMonoid.toInv.{u1} M₁ _inst_7) x)) (Inv.inv.{u2} M₂ _inst_4 (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ (DivInvMonoid.toDiv.{u1} M₁ _inst_7)) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ _inst_5) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat (Monoid.Pow.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ _inst_7))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat _inst_3) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int (DivInvMonoid.Pow.{u1} M₁ _inst_7)) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int _inst_6) (f x) n)) -> (DivInvMonoid.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.div_inv_monoid Function.Surjective.divInvMonoidₓ'. -/
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
    div_eq_mul_inv := hf.Forall₂.2 fun x y => by erw [← inv, ← mul, ← div, div_eq_mul_inv] }
#align function.surjective.div_inv_monoid Function.Surjective.divInvMonoid
#align function.surjective.sub_neg_monoid Function.Surjective.subNegMonoid

/- warning: function.surjective.group -> Function.Surjective.group is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : Pow.{u2, 0} M₂ Nat] [_inst_4 : Inv.{u2} M₂] [_inst_5 : Div.{u2} M₂] [_inst_6 : Pow.{u2, 0} M₂ Int] [_inst_7 : Group.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (MulOneClass.toHasOne.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ _inst_7)))))))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_2)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ _inst_7))))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ (DivInvMonoid.toHasInv.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ _inst_7)) x)) (Inv.inv.{u2} M₂ _inst_4 (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ (DivInvMonoid.toHasDiv.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ _inst_7))) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ _inst_5) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat (Monoid.Pow.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ _inst_7)))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat _inst_3) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int (DivInvMonoid.Pow.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ _inst_7))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int _inst_6) (f x) n)) -> (Group.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : Pow.{u2, 0} M₂ Nat] [_inst_4 : Inv.{u2} M₂] [_inst_5 : Div.{u2} M₂] [_inst_6 : Pow.{u2, 0} M₂ Int] [_inst_7 : Group.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (InvOneClass.toOne.{u1} M₁ (DivInvOneMonoid.toInvOneClass.{u1} M₁ (DivisionMonoid.toDivInvOneMonoid.{u1} M₁ (Group.toDivisionMonoid.{u1} M₁ _inst_7))))))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ _inst_2))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toMul.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ _inst_7))))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ (InvOneClass.toInv.{u1} M₁ (DivInvOneMonoid.toInvOneClass.{u1} M₁ (DivisionMonoid.toDivInvOneMonoid.{u1} M₁ (Group.toDivisionMonoid.{u1} M₁ _inst_7)))) x)) (Inv.inv.{u2} M₂ _inst_4 (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ (DivInvMonoid.toDiv.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ _inst_7))) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ _inst_5) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat (Monoid.Pow.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ _inst_7)))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat _inst_3) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int (DivInvMonoid.Pow.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ _inst_7))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int _inst_6) (f x) n)) -> (Group.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.group Function.Surjective.groupₓ'. -/
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
    mul_left_inv := hf.forall.2 fun x => by erw [← inv, ← mul, mul_left_inv, one] <;> rfl }
#align function.surjective.group Function.Surjective.group
#align function.surjective.add_group Function.Surjective.addGroup

/- warning: function.surjective.add_group_with_one -> Function.Surjective.addGroupWithOne is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_7 : Zero.{u2} M₂] [_inst_8 : One.{u2} M₂] [_inst_9 : Add.{u2} M₂] [_inst_10 : Neg.{u2} M₂] [_inst_11 : Sub.{u2} M₂] [_inst_12 : SMul.{0, u2} Nat M₂] [_inst_13 : SMul.{0, u2} Int M₂] [_inst_14 : NatCast.{u2} M₂] [_inst_15 : IntCast.{u2} M₂] [_inst_16 : AddGroupWithOne.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 0 (OfNat.mk.{u1} M₁ 0 (Zero.zero.{u1} M₁ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ _inst_16)))))))) (OfNat.ofNat.{u2} M₂ 0 (OfNat.mk.{u2} M₂ 0 (Zero.zero.{u2} M₂ _inst_7)))) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (AddMonoidWithOne.toOne.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ _inst_16)))))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_8)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HAdd.hAdd.{u1, u1, u1} M₁ M₁ M₁ (instHAdd.{u1} M₁ (AddZeroClass.toHasAdd.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ _inst_16))))) x y)) (HAdd.hAdd.{u2, u2, u2} M₂ M₂ M₂ (instHAdd.{u2} M₂ _inst_9) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Neg.neg.{u1} M₁ (SubNegMonoid.toHasNeg.{u1} M₁ (AddGroup.toSubNegMonoid.{u1} M₁ (AddGroupWithOne.toAddGroup.{u1} M₁ _inst_16))) x)) (Neg.neg.{u2} M₂ _inst_10 (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HSub.hSub.{u1, u1, u1} M₁ M₁ M₁ (instHSub.{u1} M₁ (SubNegMonoid.toHasSub.{u1} M₁ (AddGroup.toSubNegMonoid.{u1} M₁ (AddGroupWithOne.toAddGroup.{u1} M₁ _inst_16)))) x y)) (HSub.hSub.{u2, u2, u2} M₂ M₂ M₂ (instHSub.{u2} M₂ _inst_11) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (SMul.smul.{0, u1} Nat M₁ (AddMonoid.SMul.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ _inst_16))) n x)) (SMul.smul.{0, u2} Nat M₂ _inst_12 n (f x))) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (SMul.smul.{0, u1} Int M₁ (SubNegMonoid.SMulInt.{u1} M₁ (AddGroup.toSubNegMonoid.{u1} M₁ (AddGroupWithOne.toAddGroup.{u1} M₁ _inst_16))) n x)) (SMul.smul.{0, u2} Int M₂ _inst_13 n (f x))) -> (forall (n : Nat), Eq.{succ u2} M₂ (f ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat M₁ (HasLiftT.mk.{1, succ u1} Nat M₁ (CoeTCₓ.coe.{1, succ u1} Nat M₁ (Nat.castCoe.{u1} M₁ (AddMonoidWithOne.toNatCast.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ _inst_16))))) n)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat M₂ (HasLiftT.mk.{1, succ u2} Nat M₂ (CoeTCₓ.coe.{1, succ u2} Nat M₂ (Nat.castCoe.{u2} M₂ _inst_14))) n)) -> (forall (n : Int), Eq.{succ u2} M₂ (f ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int M₁ (HasLiftT.mk.{1, succ u1} Int M₁ (CoeTCₓ.coe.{1, succ u1} Int M₁ (Int.castCoe.{u1} M₁ (AddGroupWithOne.toHasIntCast.{u1} M₁ _inst_16)))) n)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int M₂ (HasLiftT.mk.{1, succ u2} Int M₂ (CoeTCₓ.coe.{1, succ u2} Int M₂ (Int.castCoe.{u2} M₂ _inst_15))) n)) -> (AddGroupWithOne.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_7 : Zero.{u2} M₂] [_inst_8 : One.{u2} M₂] [_inst_9 : Add.{u2} M₂] [_inst_10 : Neg.{u2} M₂] [_inst_11 : Sub.{u2} M₂] [_inst_12 : SMul.{0, u2} Nat M₂] [_inst_13 : SMul.{0, u2} Int M₂] [_inst_14 : NatCast.{u2} M₂] [_inst_15 : IntCast.{u2} M₂] [_inst_16 : AddGroupWithOne.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 0 (Zero.toOfNat0.{u1} M₁ (NegZeroClass.toZero.{u1} M₁ (SubNegZeroMonoid.toNegZeroClass.{u1} M₁ (SubtractionMonoid.toSubNegZeroMonoid.{u1} M₁ (AddGroup.toSubtractionMonoid.{u1} M₁ (AddGroupWithOne.toAddGroup.{u1} M₁ _inst_16)))))))) (OfNat.ofNat.{u2} M₂ 0 (Zero.toOfNat0.{u2} M₂ _inst_7))) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (AddMonoidWithOne.toOne.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ _inst_16))))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ _inst_8))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HAdd.hAdd.{u1, u1, u1} M₁ M₁ M₁ (instHAdd.{u1} M₁ (AddZeroClass.toAdd.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ _inst_16))))) x y)) (HAdd.hAdd.{u2, u2, u2} M₂ M₂ M₂ (instHAdd.{u2} M₂ _inst_9) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Neg.neg.{u1} M₁ (AddGroupWithOne.toNeg.{u1} M₁ _inst_16) x)) (Neg.neg.{u2} M₂ _inst_10 (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HSub.hSub.{u1, u1, u1} M₁ M₁ M₁ (instHSub.{u1} M₁ (AddGroupWithOne.toSub.{u1} M₁ _inst_16)) x y)) (HSub.hSub.{u2, u2, u2} M₂ M₂ M₂ (instHSub.{u2} M₂ _inst_11) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HSMul.hSMul.{0, u1, u1} Nat M₁ M₁ (instHSMul.{0, u1} Nat M₁ (AddMonoid.SMul.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ _inst_16)))) n x)) (HSMul.hSMul.{0, u2, u2} Nat M₂ M₂ (instHSMul.{0, u2} Nat M₂ _inst_12) n (f x))) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HSMul.hSMul.{0, u1, u1} Int M₁ M₁ (instHSMul.{0, u1} Int M₁ (SubNegMonoid.SMulInt.{u1} M₁ (AddGroup.toSubNegMonoid.{u1} M₁ (AddGroupWithOne.toAddGroup.{u1} M₁ _inst_16)))) n x)) (HSMul.hSMul.{0, u2, u2} Int M₂ M₂ (instHSMul.{0, u2} Int M₂ _inst_13) n (f x))) -> (forall (n : Nat), Eq.{succ u2} M₂ (f (Nat.cast.{u1} M₁ (AddMonoidWithOne.toNatCast.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ _inst_16)) n)) (Nat.cast.{u2} M₂ _inst_14 n)) -> (forall (n : Int), Eq.{succ u2} M₂ (f (Int.cast.{u1} M₁ (AddGroupWithOne.toIntCast.{u1} M₁ _inst_16) n)) (Int.cast.{u2} M₂ _inst_15 n)) -> (AddGroupWithOne.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.add_group_with_one Function.Surjective.addGroupWithOneₓ'. -/
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
    intCast_negSucc := fun n =>
      by
      rw [← int_cast, Int.cast_neg, Int.cast_ofNat, neg, nat_cast]
      rfl }
#align function.surjective.add_group_with_one Function.Surjective.addGroupWithOne

/- warning: function.surjective.comm_group -> Function.Surjective.commGroup is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : Pow.{u2, 0} M₂ Nat] [_inst_4 : Inv.{u2} M₂] [_inst_5 : Div.{u2} M₂] [_inst_6 : Pow.{u2, 0} M₂ Int] [_inst_7 : CommGroup.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (MulOneClass.toHasOne.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ (CommGroup.toGroup.{u1} M₁ _inst_7))))))))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_2)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toHasMul.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ (CommGroup.toGroup.{u1} M₁ _inst_7)))))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ (DivInvMonoid.toHasInv.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ (CommGroup.toGroup.{u1} M₁ _inst_7))) x)) (Inv.inv.{u2} M₂ _inst_4 (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ (DivInvMonoid.toHasDiv.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ (CommGroup.toGroup.{u1} M₁ _inst_7)))) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ _inst_5) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat (Monoid.Pow.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ (CommGroup.toGroup.{u1} M₁ _inst_7))))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat _inst_3) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int (DivInvMonoid.Pow.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ (CommGroup.toGroup.{u1} M₁ _inst_7)))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int _inst_6) (f x) n)) -> (CommGroup.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_1 : Mul.{u2} M₂] [_inst_2 : One.{u2} M₂] [_inst_3 : Pow.{u2, 0} M₂ Nat] [_inst_4 : Inv.{u2} M₂] [_inst_5 : Div.{u2} M₂] [_inst_6 : Pow.{u2, 0} M₂ Int] [_inst_7 : CommGroup.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (InvOneClass.toOne.{u1} M₁ (DivInvOneMonoid.toInvOneClass.{u1} M₁ (DivisionMonoid.toDivInvOneMonoid.{u1} M₁ (DivisionCommMonoid.toDivisionMonoid.{u1} M₁ (CommGroup.toDivisionCommMonoid.{u1} M₁ _inst_7)))))))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ _inst_2))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HMul.hMul.{u1, u1, u1} M₁ M₁ M₁ (instHMul.{u1} M₁ (MulOneClass.toMul.{u1} M₁ (Monoid.toMulOneClass.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ (CommGroup.toGroup.{u1} M₁ _inst_7)))))) x y)) (HMul.hMul.{u2, u2, u2} M₂ M₂ M₂ (instHMul.{u2} M₂ _inst_1) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Inv.inv.{u1} M₁ (InvOneClass.toInv.{u1} M₁ (DivInvOneMonoid.toInvOneClass.{u1} M₁ (DivisionMonoid.toDivInvOneMonoid.{u1} M₁ (DivisionCommMonoid.toDivisionMonoid.{u1} M₁ (CommGroup.toDivisionCommMonoid.{u1} M₁ _inst_7))))) x)) (Inv.inv.{u2} M₂ _inst_4 (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HDiv.hDiv.{u1, u1, u1} M₁ M₁ M₁ (instHDiv.{u1} M₁ (DivInvMonoid.toDiv.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ (CommGroup.toGroup.{u1} M₁ _inst_7)))) x y)) (HDiv.hDiv.{u2, u2, u2} M₂ M₂ M₂ (instHDiv.{u2} M₂ _inst_5) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Nat M₁ (instHPow.{u1, 0} M₁ Nat (Monoid.Pow.{u1} M₁ (DivInvMonoid.toMonoid.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ (CommGroup.toGroup.{u1} M₁ _inst_7))))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Nat M₂ (instHPow.{u2, 0} M₂ Nat _inst_3) (f x) n)) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HPow.hPow.{u1, 0, u1} M₁ Int M₁ (instHPow.{u1, 0} M₁ Int (DivInvMonoid.Pow.{u1} M₁ (Group.toDivInvMonoid.{u1} M₁ (CommGroup.toGroup.{u1} M₁ _inst_7)))) x n)) (HPow.hPow.{u2, 0, u2} M₂ Int M₂ (instHPow.{u2, 0} M₂ Int _inst_6) (f x) n)) -> (CommGroup.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.comm_group Function.Surjective.commGroupₓ'. -/
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

/- warning: function.surjective.add_comm_group_with_one -> Function.Surjective.addCommGroupWithOne is a dubious translation:
lean 3 declaration is
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_7 : Zero.{u2} M₂] [_inst_8 : One.{u2} M₂] [_inst_9 : Add.{u2} M₂] [_inst_10 : Neg.{u2} M₂] [_inst_11 : Sub.{u2} M₂] [_inst_12 : SMul.{0, u2} Nat M₂] [_inst_13 : SMul.{0, u2} Int M₂] [_inst_14 : NatCast.{u2} M₂] [_inst_15 : IntCast.{u2} M₂] [_inst_16 : AddCommGroupWithOne.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 0 (OfNat.mk.{u1} M₁ 0 (Zero.zero.{u1} M₁ (AddZeroClass.toHasZero.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16))))))))) (OfNat.ofNat.{u2} M₂ 0 (OfNat.mk.{u2} M₂ 0 (Zero.zero.{u2} M₂ _inst_7)))) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (OfNat.mk.{u1} M₁ 1 (One.one.{u1} M₁ (AddMonoidWithOne.toOne.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16))))))) (OfNat.ofNat.{u2} M₂ 1 (OfNat.mk.{u2} M₂ 1 (One.one.{u2} M₂ _inst_8)))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HAdd.hAdd.{u1, u1, u1} M₁ M₁ M₁ (instHAdd.{u1} M₁ (AddZeroClass.toHasAdd.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16)))))) x y)) (HAdd.hAdd.{u2, u2, u2} M₂ M₂ M₂ (instHAdd.{u2} M₂ _inst_9) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Neg.neg.{u1} M₁ (SubNegMonoid.toHasNeg.{u1} M₁ (AddGroup.toSubNegMonoid.{u1} M₁ (AddGroupWithOne.toAddGroup.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16)))) x)) (Neg.neg.{u2} M₂ _inst_10 (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HSub.hSub.{u1, u1, u1} M₁ M₁ M₁ (instHSub.{u1} M₁ (SubNegMonoid.toHasSub.{u1} M₁ (AddGroup.toSubNegMonoid.{u1} M₁ (AddGroupWithOne.toAddGroup.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16))))) x y)) (HSub.hSub.{u2, u2, u2} M₂ M₂ M₂ (instHSub.{u2} M₂ _inst_11) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (SMul.smul.{0, u1} Nat M₁ (AddMonoid.SMul.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16)))) n x)) (SMul.smul.{0, u2} Nat M₂ _inst_12 n (f x))) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (SMul.smul.{0, u1} Int M₁ (SubNegMonoid.SMulInt.{u1} M₁ (AddGroup.toSubNegMonoid.{u1} M₁ (AddGroupWithOne.toAddGroup.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16)))) n x)) (SMul.smul.{0, u2} Int M₂ _inst_13 n (f x))) -> (forall (n : Nat), Eq.{succ u2} M₂ (f ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat M₁ (HasLiftT.mk.{1, succ u1} Nat M₁ (CoeTCₓ.coe.{1, succ u1} Nat M₁ (Nat.castCoe.{u1} M₁ (AddMonoidWithOne.toNatCast.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16)))))) n)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat M₂ (HasLiftT.mk.{1, succ u2} Nat M₂ (CoeTCₓ.coe.{1, succ u2} Nat M₂ (Nat.castCoe.{u2} M₂ _inst_14))) n)) -> (forall (n : Int), Eq.{succ u2} M₂ (f ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int M₁ (HasLiftT.mk.{1, succ u1} Int M₁ (CoeTCₓ.coe.{1, succ u1} Int M₁ (Int.castCoe.{u1} M₁ (AddGroupWithOne.toHasIntCast.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16))))) n)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Int M₂ (HasLiftT.mk.{1, succ u2} Int M₂ (CoeTCₓ.coe.{1, succ u2} Int M₂ (Int.castCoe.{u2} M₂ _inst_15))) n)) -> (AddCommGroupWithOne.{u2} M₂)
but is expected to have type
  forall {M₁ : Type.{u1}} {M₂ : Type.{u2}} [_inst_7 : Zero.{u2} M₂] [_inst_8 : One.{u2} M₂] [_inst_9 : Add.{u2} M₂] [_inst_10 : Neg.{u2} M₂] [_inst_11 : Sub.{u2} M₂] [_inst_12 : SMul.{0, u2} Nat M₂] [_inst_13 : SMul.{0, u2} Int M₂] [_inst_14 : NatCast.{u2} M₂] [_inst_15 : IntCast.{u2} M₂] [_inst_16 : AddCommGroupWithOne.{u1} M₁] (f : M₁ -> M₂), (Function.Surjective.{succ u1, succ u2} M₁ M₂ f) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 0 (Zero.toOfNat0.{u1} M₁ (NegZeroClass.toZero.{u1} M₁ (SubNegZeroMonoid.toNegZeroClass.{u1} M₁ (SubtractionMonoid.toSubNegZeroMonoid.{u1} M₁ (SubtractionCommMonoid.toSubtractionMonoid.{u1} M₁ (AddCommGroup.toDivisionAddCommMonoid.{u1} M₁ (AddCommGroupWithOne.toAddCommGroup.{u1} M₁ _inst_16))))))))) (OfNat.ofNat.{u2} M₂ 0 (Zero.toOfNat0.{u2} M₂ _inst_7))) -> (Eq.{succ u2} M₂ (f (OfNat.ofNat.{u1} M₁ 1 (One.toOfNat1.{u1} M₁ (AddCommGroupWithOne.toOne.{u1} M₁ _inst_16)))) (OfNat.ofNat.{u2} M₂ 1 (One.toOfNat1.{u2} M₂ _inst_8))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HAdd.hAdd.{u1, u1, u1} M₁ M₁ M₁ (instHAdd.{u1} M₁ (AddZeroClass.toAdd.{u1} M₁ (AddMonoid.toAddZeroClass.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16)))))) x y)) (HAdd.hAdd.{u2, u2, u2} M₂ M₂ M₂ (instHAdd.{u2} M₂ _inst_9) (f x) (f y))) -> (forall (x : M₁), Eq.{succ u2} M₂ (f (Neg.neg.{u1} M₁ (AddGroupWithOne.toNeg.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16)) x)) (Neg.neg.{u2} M₂ _inst_10 (f x))) -> (forall (x : M₁) (y : M₁), Eq.{succ u2} M₂ (f (HSub.hSub.{u1, u1, u1} M₁ M₁ M₁ (instHSub.{u1} M₁ (AddGroupWithOne.toSub.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16))) x y)) (HSub.hSub.{u2, u2, u2} M₂ M₂ M₂ (instHSub.{u2} M₂ _inst_11) (f x) (f y))) -> (forall (x : M₁) (n : Nat), Eq.{succ u2} M₂ (f (HSMul.hSMul.{0, u1, u1} Nat M₁ M₁ (instHSMul.{0, u1} Nat M₁ (AddMonoid.SMul.{u1} M₁ (AddMonoidWithOne.toAddMonoid.{u1} M₁ (AddGroupWithOne.toAddMonoidWithOne.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16))))) n x)) (HSMul.hSMul.{0, u2, u2} Nat M₂ M₂ (instHSMul.{0, u2} Nat M₂ _inst_12) n (f x))) -> (forall (x : M₁) (n : Int), Eq.{succ u2} M₂ (f (HSMul.hSMul.{0, u1, u1} Int M₁ M₁ (instHSMul.{0, u1} Int M₁ (SubNegMonoid.SMulInt.{u1} M₁ (AddGroup.toSubNegMonoid.{u1} M₁ (AddGroupWithOne.toAddGroup.{u1} M₁ (AddCommGroupWithOne.toAddGroupWithOne.{u1} M₁ _inst_16))))) n x)) (HSMul.hSMul.{0, u2, u2} Int M₂ M₂ (instHSMul.{0, u2} Int M₂ _inst_13) n (f x))) -> (forall (n : Nat), Eq.{succ u2} M₂ (f (Nat.cast.{u1} M₁ (AddCommGroupWithOne.toNatCast.{u1} M₁ _inst_16) n)) (Nat.cast.{u2} M₂ _inst_14 n)) -> (forall (n : Int), Eq.{succ u2} M₂ (f (Int.cast.{u1} M₁ (AddCommGroupWithOne.toIntCast.{u1} M₁ _inst_16) n)) (Int.cast.{u2} M₂ _inst_15 n)) -> (AddCommGroupWithOne.{u2} M₂)
Case conversion may be inaccurate. Consider using '#align function.surjective.add_comm_group_with_one Function.Surjective.addCommGroupWithOneₓ'. -/
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

end Surjective

end Function


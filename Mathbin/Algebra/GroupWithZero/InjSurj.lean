/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.group_with_zero.inj_surj
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.InjSurj
import Mathbin.Algebra.GroupWithZero.Defs

/-!
# Lifting groups with zero along injective/surjective maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Function

variable {M₀ G₀ M₀' G₀' : Type _}

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

/- warning: function.injective.mul_zero_class -> Function.Injective.mulZeroClass is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : Zero.{u2} M₀'] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_3)))) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) -> (forall (a : M₀') (b : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) a b)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) (f a) (f b))) -> (MulZeroClass.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : Zero.{u2} M₀'] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_3))) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) -> (forall (a : M₀') (b : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) a b)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) (f a) (f b))) -> (MulZeroClass.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.injective.mul_zero_class Function.Injective.mulZeroClassₓ'. -/
/-- Pullback a `mul_zero_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀' → M₀) (hf : Injective f)
    (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroClass M₀'
    where
  mul := (· * ·)
  zero := 0
  zero_mul a := hf <| by simp only [mul, zero, zero_mul]
  mul_zero a := hf <| by simp only [mul, zero, mul_zero]
#align function.injective.mul_zero_class Function.Injective.mulZeroClass

/- warning: function.surjective.mul_zero_class -> Function.Surjective.mulZeroClass is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : Zero.{u2} M₀'] (f : M₀ -> M₀'), (Function.Surjective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_3)))) -> (forall (a : M₀) (b : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) (f a) (f b))) -> (MulZeroClass.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : MulZeroClass.{u1} M₀] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : Zero.{u2} M₀'] (f : M₀ -> M₀'), (Function.Surjective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_3))) -> (forall (a : M₀) (b : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) (f a) (f b))) -> (MulZeroClass.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.surjective.mul_zero_class Function.Surjective.mulZeroClassₓ'. -/
/-- Pushforward a `mul_zero_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroClass M₀'
    where
  mul := (· * ·)
  zero := 0
  mul_zero := hf.forall.2 fun x => by simp only [← zero, ← mul, mul_zero]
  zero_mul := hf.forall.2 fun x => by simp only [← zero, ← mul, zero_mul]
#align function.surjective.mul_zero_class Function.Surjective.mulZeroClass

end MulZeroClass

section NoZeroDivisors

/- warning: function.injective.no_zero_divisors -> Function.Injective.noZeroDivisors is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Mul.{u1} M₀] [_inst_2 : Zero.{u1} M₀] [_inst_3 : Mul.{u2} M₀'] [_inst_4 : Zero.{u2} M₀'] [_inst_5 : NoZeroDivisors.{u2} M₀' _inst_3 _inst_4] (f : M₀ -> M₀'), (Function.Injective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ _inst_2)))) (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_4)))) -> (forall (x : M₀) (y : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ _inst_1) x y)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_3) (f x) (f y))) -> (NoZeroDivisors.{u1} M₀ _inst_1 _inst_2)
but is expected to have type
  forall {M₀ : Type.{u2}} {M₀' : Type.{u1}} [_inst_1 : Mul.{u2} M₀] [_inst_2 : Zero.{u2} M₀] [_inst_3 : Mul.{u1} M₀'] [_inst_4 : Zero.{u1} M₀'] [_inst_5 : NoZeroDivisors.{u1} M₀' _inst_3 _inst_4] (f : M₀ -> M₀'), (Function.Injective.{succ u2, succ u1} M₀ M₀' f) -> (Eq.{succ u1} M₀' (f (OfNat.ofNat.{u2} M₀ 0 (Zero.toOfNat0.{u2} M₀ _inst_2))) (OfNat.ofNat.{u1} M₀' 0 (Zero.toOfNat0.{u1} M₀' _inst_4))) -> (forall (x : M₀) (y : M₀), Eq.{succ u1} M₀' (f (HMul.hMul.{u2, u2, u2} M₀ M₀ M₀ (instHMul.{u2} M₀ _inst_1) x y)) (HMul.hMul.{u1, u1, u1} M₀' M₀' M₀' (instHMul.{u1} M₀' _inst_3) (f x) (f y))) -> (NoZeroDivisors.{u2} M₀ _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align function.injective.no_zero_divisors Function.Injective.noZeroDivisorsₓ'. -/
/-- Pushforward a `no_zero_divisors` instance along an injective function. -/
protected theorem Function.Injective.noZeroDivisors [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
    [NoZeroDivisors M₀'] (f : M₀ → M₀') (hf : Injective f) (zero : f 0 = 0)
    (mul : ∀ x y, f (x * y) = f x * f y) : NoZeroDivisors M₀ :=
  {
    eq_zero_or_eq_zero_of_mul_eq_zero := fun x y H =>
      have : f x * f y = 0 := by rw [← mul, H, zero]
      (eq_zero_or_eq_zero_of_mul_eq_zero this).imp (fun H => hf <| by rwa [zero]) fun H =>
        hf <| by rwa [zero] }
#align function.injective.no_zero_divisors Function.Injective.noZeroDivisors

end NoZeroDivisors

section MulZeroOneClass

variable [MulZeroOneClass M₀]

/- warning: function.injective.mul_zero_one_class -> Function.Injective.mulZeroOneClass is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : Zero.{u2} M₀'] [_inst_4 : One.{u2} M₀'] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_3)))) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1)))))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (OfNat.mk.{u2} M₀' 1 (One.one.{u2} M₀' _inst_4)))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) -> (forall (a : M₀') (b : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) a b)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))) (f a) (f b))) -> (MulZeroOneClass.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : Zero.{u2} M₀'] [_inst_4 : One.{u2} M₀'] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_3))) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1)))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (One.toOfNat1.{u2} M₀' _inst_4))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) -> (forall (a : M₀') (b : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) a b)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))) (f a) (f b))) -> (MulZeroOneClass.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.injective.mul_zero_one_class Function.Injective.mulZeroOneClassₓ'. -/
/-- Pullback a `mul_zero_one_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroOneClass M₀' :=
  { hf.MulZeroClass f zero mul, hf.MulOneClass f one mul with }
#align function.injective.mul_zero_one_class Function.Injective.mulZeroOneClass

/- warning: function.surjective.mul_zero_one_class -> Function.Surjective.mulZeroOneClass is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : Zero.{u2} M₀'] [_inst_4 : One.{u2} M₀'] (f : M₀ -> M₀'), (Function.Surjective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1)))))) (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_3)))) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) (OfNat.ofNat.{u2} M₀' 1 (OfNat.mk.{u2} M₀' 1 (One.one.{u2} M₀' _inst_4)))) -> (forall (a : M₀) (b : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))) a b)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) (f a) (f b))) -> (MulZeroOneClass.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : Zero.{u2} M₀'] [_inst_4 : One.{u2} M₀'] (f : M₀ -> M₀'), (Function.Surjective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1)))) (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_3))) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) (OfNat.ofNat.{u2} M₀' 1 (One.toOfNat1.{u2} M₀' _inst_4))) -> (forall (a : M₀) (b : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))) a b)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) (f a) (f b))) -> (MulZeroOneClass.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.surjective.mul_zero_one_class Function.Surjective.mulZeroOneClassₓ'. -/
/-- Pushforward a `mul_zero_one_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroOneClass M₀' :=
  { hf.MulZeroClass f zero mul, hf.MulOneClass f one mul with }
#align function.surjective.mul_zero_one_class Function.Surjective.mulZeroOneClass

end MulZeroOneClass

section SemigroupWithZero

/- warning: function.injective.semigroup_with_zero -> Function.Injective.semigroupWithZero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Zero.{u2} M₀'] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : SemigroupWithZero.{u1} M₀] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_1)))) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (SemigroupWithZero.toMulZeroClass.{u1} M₀ _inst_3)))))) -> (forall (x : M₀') (y : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) x y)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (SemigroupWithZero.toMulZeroClass.{u1} M₀ _inst_3))) (f x) (f y))) -> (SemigroupWithZero.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Zero.{u2} M₀'] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : SemigroupWithZero.{u1} M₀] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_1))) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (SemigroupWithZero.toZero.{u1} M₀ _inst_3)))) -> (forall (x : M₀') (y : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) x y)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (SemigroupWithZero.toMulZeroClass.{u1} M₀ _inst_3))) (f x) (f y))) -> (SemigroupWithZero.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.injective.semigroup_with_zero Function.Injective.semigroupWithZeroₓ'. -/
/-- Pullback a `semigroup_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semigroupWithZero [Zero M₀'] [Mul M₀'] [SemigroupWithZero M₀]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
    SemigroupWithZero M₀' :=
  { hf.MulZeroClass f zero mul, ‹Zero M₀'›, hf.Semigroup f mul with }
#align function.injective.semigroup_with_zero Function.Injective.semigroupWithZero

/- warning: function.surjective.semigroup_with_zero -> Function.Surjective.semigroupWithZero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : SemigroupWithZero.{u1} M₀] [_inst_2 : Zero.{u2} M₀'] [_inst_3 : Mul.{u2} M₀'] (f : M₀ -> M₀'), (Function.Surjective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (SemigroupWithZero.toMulZeroClass.{u1} M₀ _inst_1)))))) (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_2)))) -> (forall (x : M₀) (y : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (SemigroupWithZero.toMulZeroClass.{u1} M₀ _inst_1))) x y)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_3) (f x) (f y))) -> (SemigroupWithZero.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : SemigroupWithZero.{u1} M₀] [_inst_2 : Zero.{u2} M₀'] [_inst_3 : Mul.{u2} M₀'] (f : M₀ -> M₀'), (Function.Surjective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (SemigroupWithZero.toZero.{u1} M₀ _inst_1)))) (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_2))) -> (forall (x : M₀) (y : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (SemigroupWithZero.toMulZeroClass.{u1} M₀ _inst_1))) x y)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_3) (f x) (f y))) -> (SemigroupWithZero.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.surjective.semigroup_with_zero Function.Surjective.semigroupWithZeroₓ'. -/
/-- Pushforward a `semigroup_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.semigroupWithZero [SemigroupWithZero M₀] [Zero M₀'] [Mul M₀']
    (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
    SemigroupWithZero M₀' :=
  { hf.MulZeroClass f zero mul, ‹Zero M₀'›, hf.Semigroup f mul with }
#align function.surjective.semigroup_with_zero Function.Surjective.semigroupWithZero

end SemigroupWithZero

section MonoidWithZero

/- warning: function.injective.monoid_with_zero -> Function.Injective.monoidWithZero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Zero.{u2} M₀'] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : One.{u2} M₀'] [_inst_4 : Pow.{u2, 0} M₀' Nat] [_inst_5 : MonoidWithZero.{u1} M₀] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_1)))) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_5))))))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (OfNat.mk.{u2} M₀' 1 (One.one.{u2} M₀' _inst_3)))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_5))))))) -> (forall (x : M₀') (y : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) x y)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_5)))) (f x) (f y))) -> (forall (x : M₀') (n : Nat), Eq.{succ u1} M₀ (f (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_5))) (f x) n)) -> (MonoidWithZero.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Zero.{u2} M₀'] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : One.{u2} M₀'] [_inst_4 : Pow.{u2, 0} M₀' Nat] [_inst_5 : MonoidWithZero.{u1} M₀] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_1))) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_5)))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (One.toOfNat1.{u2} M₀' _inst_3))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_5))))) -> (forall (x : M₀') (y : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) x y)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_5)))) (f x) (f y))) -> (forall (x : M₀') (n : Nat), Eq.{succ u1} M₀ (f (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_5))) (f x) n)) -> (MonoidWithZero.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.injective.monoid_with_zero Function.Injective.monoidWithZeroₓ'. -/
/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [MonoidWithZero M₀] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    MonoidWithZero M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with }
#align function.injective.monoid_with_zero Function.Injective.monoidWithZero

/- warning: function.surjective.monoid_with_zero -> Function.Surjective.monoidWithZero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Zero.{u2} M₀'] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : One.{u2} M₀'] [_inst_4 : Pow.{u2, 0} M₀' Nat] [_inst_5 : MonoidWithZero.{u1} M₀] (f : M₀ -> M₀'), (Function.Surjective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_5))))))) (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_1)))) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_5))))))) (OfNat.ofNat.{u2} M₀' 1 (OfNat.mk.{u2} M₀' 1 (One.one.{u2} M₀' _inst_3)))) -> (forall (x : M₀) (y : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_5)))) x y)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) (f x) (f y))) -> (forall (x : M₀) (n : Nat), Eq.{succ u2} M₀' (f (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_5))) x n)) (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_4) (f x) n)) -> (MonoidWithZero.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Zero.{u2} M₀'] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : One.{u2} M₀'] [_inst_4 : Pow.{u2, 0} M₀' Nat] [_inst_5 : MonoidWithZero.{u1} M₀] (f : M₀ -> M₀'), (Function.Surjective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_5)))) (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_1))) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_5))))) (OfNat.ofNat.{u2} M₀' 1 (One.toOfNat1.{u2} M₀' _inst_3))) -> (forall (x : M₀) (y : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_5)))) x y)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) (f x) (f y))) -> (forall (x : M₀) (n : Nat), Eq.{succ u2} M₀' (f (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_5))) x n)) (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_4) (f x) n)) -> (MonoidWithZero.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.surjective.monoid_with_zero Function.Surjective.monoidWithZeroₓ'. -/
/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [MonoidWithZero M₀] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    MonoidWithZero M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with }
#align function.surjective.monoid_with_zero Function.Surjective.monoidWithZero

/- warning: function.injective.comm_monoid_with_zero -> Function.Injective.commMonoidWithZero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Zero.{u2} M₀'] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : One.{u2} M₀'] [_inst_4 : Pow.{u2, 0} M₀' Nat] [_inst_5 : CommMonoidWithZero.{u1} M₀] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_1)))) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5)))))))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (OfNat.mk.{u2} M₀' 1 (One.one.{u2} M₀' _inst_3)))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5)))))))) -> (forall (x : M₀') (y : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) x y)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5))))) (f x) (f y))) -> (forall (x : M₀') (n : Nat), Eq.{succ u1} M₀ (f (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5)))) (f x) n)) -> (CommMonoidWithZero.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Zero.{u2} M₀'] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : One.{u2} M₀'] [_inst_4 : Pow.{u2, 0} M₀' Nat] [_inst_5 : CommMonoidWithZero.{u1} M₀] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_1))) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (CommMonoidWithZero.toZero.{u1} M₀ _inst_5)))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (One.toOfNat1.{u2} M₀' _inst_3))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5)))))) -> (forall (x : M₀') (y : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) x y)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5))))) (f x) (f y))) -> (forall (x : M₀') (n : Nat), Eq.{succ u1} M₀ (f (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_4) x n)) (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5)))) (f x) n)) -> (CommMonoidWithZero.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.injective.comm_monoid_with_zero Function.Injective.commMonoidWithZeroₓ'. -/
/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [CommMonoidWithZero M₀] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoidWithZero M₀' :=
  { hf.CommMonoid f one mul npow, hf.MulZeroClass f zero mul with }
#align function.injective.comm_monoid_with_zero Function.Injective.commMonoidWithZero

/- warning: function.surjective.comm_monoid_with_zero -> Function.Surjective.commMonoidWithZero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Zero.{u2} M₀'] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : One.{u2} M₀'] [_inst_4 : Pow.{u2, 0} M₀' Nat] [_inst_5 : CommMonoidWithZero.{u1} M₀] (f : M₀ -> M₀'), (Function.Surjective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5)))))))) (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_1)))) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5)))))))) (OfNat.ofNat.{u2} M₀' 1 (OfNat.mk.{u2} M₀' 1 (One.one.{u2} M₀' _inst_3)))) -> (forall (x : M₀) (y : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5))))) x y)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) (f x) (f y))) -> (forall (x : M₀) (n : Nat), Eq.{succ u2} M₀' (f (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5)))) x n)) (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_4) (f x) n)) -> (CommMonoidWithZero.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : Zero.{u2} M₀'] [_inst_2 : Mul.{u2} M₀'] [_inst_3 : One.{u2} M₀'] [_inst_4 : Pow.{u2, 0} M₀' Nat] [_inst_5 : CommMonoidWithZero.{u1} M₀] (f : M₀ -> M₀'), (Function.Surjective.{succ u1, succ u2} M₀ M₀' f) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (CommMonoidWithZero.toZero.{u1} M₀ _inst_5)))) (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_1))) -> (Eq.{succ u2} M₀' (f (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5)))))) (OfNat.ofNat.{u2} M₀' 1 (One.toOfNat1.{u2} M₀' _inst_3))) -> (forall (x : M₀) (y : M₀), Eq.{succ u2} M₀' (f (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5))))) x y)) (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_2) (f x) (f y))) -> (forall (x : M₀) (n : Nat), Eq.{succ u2} M₀' (f (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_5)))) x n)) (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_4) (f x) n)) -> (CommMonoidWithZero.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.surjective.comm_monoid_with_zero Function.Surjective.commMonoidWithZeroₓ'. -/
/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [CommMonoidWithZero M₀] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoidWithZero M₀' :=
  { hf.CommMonoid f one mul npow, hf.MulZeroClass f zero mul with }
#align function.surjective.comm_monoid_with_zero Function.Surjective.commMonoidWithZero

end MonoidWithZero

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

/- warning: function.injective.cancel_monoid_with_zero -> Function.Injective.cancelMonoidWithZero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] [_inst_2 : Zero.{u2} M₀'] [_inst_3 : Mul.{u2} M₀'] [_inst_4 : One.{u2} M₀'] [_inst_5 : Pow.{u2, 0} M₀' Nat] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_2)))) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (OfNat.mk.{u2} M₀' 1 (One.one.{u2} M₀' _inst_4)))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))) -> (forall (x : M₀') (y : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_3) x y)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) (f x) (f y))) -> (forall (x : M₀') (n : Nat), Eq.{succ u1} M₀ (f (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_5) x n)) (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))) (f x) n)) -> (CancelMonoidWithZero.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] [_inst_2 : Zero.{u2} M₀'] [_inst_3 : Mul.{u2} M₀'] [_inst_4 : One.{u2} M₀'] [_inst_5 : Pow.{u2, 0} M₀' Nat] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_2))) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (One.toOfNat1.{u2} M₀' _inst_4))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))) -> (forall (x : M₀') (y : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_3) x y)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) (f x) (f y))) -> (forall (x : M₀') (n : Nat), Eq.{succ u1} M₀ (f (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_5) x n)) (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))) (f x) n)) -> (CancelMonoidWithZero.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.injective.cancel_monoid_with_zero Function.Injective.cancelMonoidWithZeroₓ'. -/
/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.cancelMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CancelMonoidWithZero M₀' :=
  { hf.Monoid f one mul npow,
    hf.MulZeroClass f zero
      mul with
    mul_left_cancel_of_ne_zero := fun x y z hx H =>
      hf <| mul_left_cancel₀ ((hf.ne_iff' zero).2 hx) <| by erw [← mul, ← mul, H] <;> rfl
    mul_right_cancel_of_ne_zero := fun x y z hx H =>
      hf <| mul_right_cancel₀ ((hf.ne_iff' zero).2 hx) <| by erw [← mul, ← mul, H] <;> rfl }
#align function.injective.cancel_monoid_with_zero Function.Injective.cancelMonoidWithZero

end CancelMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero M₀] {a b c : M₀}

/- warning: function.injective.cancel_comm_monoid_with_zero -> Function.Injective.cancelCommMonoidWithZero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} M₀] [_inst_2 : Zero.{u2} M₀'] [_inst_3 : Mul.{u2} M₀'] [_inst_4 : One.{u2} M₀'] [_inst_5 : Pow.{u2, 0} M₀' Nat] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (OfNat.mk.{u2} M₀' 0 (Zero.zero.{u2} M₀' _inst_2)))) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M₀ _inst_1))))))))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (OfNat.mk.{u2} M₀' 1 (One.one.{u2} M₀' _inst_4)))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M₀ _inst_1))))))))) -> (forall (x : M₀') (y : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_3) x y)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M₀ _inst_1)))))) (f x) (f y))) -> (forall (x : M₀') (n : Nat), Eq.{succ u1} M₀ (f (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_5) x n)) (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M₀ _inst_1))))) (f x) n)) -> (CancelCommMonoidWithZero.{u2} M₀')
but is expected to have type
  forall {M₀ : Type.{u1}} {M₀' : Type.{u2}} [_inst_1 : CancelCommMonoidWithZero.{u1} M₀] [_inst_2 : Zero.{u2} M₀'] [_inst_3 : Mul.{u2} M₀'] [_inst_4 : One.{u2} M₀'] [_inst_5 : Pow.{u2, 0} M₀' Nat] (f : M₀' -> M₀), (Function.Injective.{succ u2, succ u1} M₀' M₀ f) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 0 (Zero.toOfNat0.{u2} M₀' _inst_2))) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (CommMonoidWithZero.toZero.{u1} M₀ (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M₀ _inst_1))))) -> (Eq.{succ u1} M₀ (f (OfNat.ofNat.{u2} M₀' 1 (One.toOfNat1.{u2} M₀' _inst_4))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M₀ _inst_1))))))) -> (forall (x : M₀') (y : M₀'), Eq.{succ u1} M₀ (f (HMul.hMul.{u2, u2, u2} M₀' M₀' M₀' (instHMul.{u2} M₀' _inst_3) x y)) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M₀ _inst_1)))))) (f x) (f y))) -> (forall (x : M₀') (n : Nat), Eq.{succ u1} M₀ (f (HPow.hPow.{u2, 0, u2} M₀' Nat M₀' (instHPow.{u2, 0} M₀' Nat _inst_5) x n)) (HPow.hPow.{u1, 0, u1} M₀ Nat M₀ (instHPow.{u1, 0} M₀ Nat (Monoid.Pow.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CommMonoidWithZero.toMonoidWithZero.{u1} M₀ (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M₀ _inst_1))))) (f x) n)) -> (CancelCommMonoidWithZero.{u2} M₀')
Case conversion may be inaccurate. Consider using '#align function.injective.cancel_comm_monoid_with_zero Function.Injective.cancelCommMonoidWithZeroₓ'. -/
/-- Pullback a `cancel_comm_monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.cancelCommMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CancelCommMonoidWithZero M₀' :=
  { hf.CommMonoidWithZero f zero one mul npow, hf.CancelMonoidWithZero f zero one mul npow with }
#align function.injective.cancel_comm_monoid_with_zero Function.Injective.cancelCommMonoidWithZero

end CancelCommMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c g h x : G₀}

/- warning: function.injective.group_with_zero -> Function.Injective.groupWithZero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} {G₀' : Type.{u2}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : Zero.{u2} G₀'] [_inst_3 : Mul.{u2} G₀'] [_inst_4 : One.{u2} G₀'] [_inst_5 : Inv.{u2} G₀'] [_inst_6 : Div.{u2} G₀'] [_inst_7 : Pow.{u2, 0} G₀' Nat] [_inst_8 : Pow.{u2, 0} G₀' Int] (f : G₀' -> G₀), (Function.Injective.{succ u2, succ u1} G₀' G₀ f) -> (Eq.{succ u1} G₀ (f (OfNat.ofNat.{u2} G₀' 0 (OfNat.mk.{u2} G₀' 0 (Zero.zero.{u2} G₀' _inst_2)))) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Eq.{succ u1} G₀ (f (OfNat.ofNat.{u2} G₀' 1 (OfNat.mk.{u2} G₀' 1 (One.one.{u2} G₀' _inst_4)))) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (x : G₀') (y : G₀'), Eq.{succ u1} G₀ (f (HMul.hMul.{u2, u2, u2} G₀' G₀' G₀' (instHMul.{u2} G₀' _inst_3) x y)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (f x) (f y))) -> (forall (x : G₀'), Eq.{succ u1} G₀ (f (Inv.inv.{u2} G₀' _inst_5 x)) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) (f x))) -> (forall (x : G₀') (y : G₀'), Eq.{succ u1} G₀ (f (HDiv.hDiv.{u2, u2, u2} G₀' G₀' G₀' (instHDiv.{u2} G₀' _inst_6) x y)) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) (f y))) -> (forall (x : G₀') (n : Nat), Eq.{succ u1} G₀ (f (HPow.hPow.{u2, 0, u2} G₀' Nat G₀' (instHPow.{u2, 0} G₀' Nat _inst_7) x n)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (f x) n)) -> (forall (x : G₀') (n : Int), Eq.{succ u1} G₀ (f (HPow.hPow.{u2, 0, u2} G₀' Int G₀' (instHPow.{u2, 0} G₀' Int _inst_8) x n)) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) n)) -> (GroupWithZero.{u2} G₀')
but is expected to have type
  forall {G₀ : Type.{u1}} {G₀' : Type.{u2}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : Zero.{u2} G₀'] [_inst_3 : Mul.{u2} G₀'] [_inst_4 : One.{u2} G₀'] [_inst_5 : Inv.{u2} G₀'] [_inst_6 : Div.{u2} G₀'] [_inst_7 : Pow.{u2, 0} G₀' Nat] [_inst_8 : Pow.{u2, 0} G₀' Int] (f : G₀' -> G₀), (Function.Injective.{succ u2, succ u1} G₀' G₀ f) -> (Eq.{succ u1} G₀ (f (OfNat.ofNat.{u2} G₀' 0 (Zero.toOfNat0.{u2} G₀' _inst_2))) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Eq.{succ u1} G₀ (f (OfNat.ofNat.{u2} G₀' 1 (One.toOfNat1.{u2} G₀' _inst_4))) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (Monoid.toOne.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))) -> (forall (x : G₀') (y : G₀'), Eq.{succ u1} G₀ (f (HMul.hMul.{u2, u2, u2} G₀' G₀' G₀' (instHMul.{u2} G₀' _inst_3) x y)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (f x) (f y))) -> (forall (x : G₀'), Eq.{succ u1} G₀ (f (Inv.inv.{u2} G₀' _inst_5 x)) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) (f x))) -> (forall (x : G₀') (y : G₀'), Eq.{succ u1} G₀ (f (HDiv.hDiv.{u2, u2, u2} G₀' G₀' G₀' (instHDiv.{u2} G₀' _inst_6) x y)) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) (f x) (f y))) -> (forall (x : G₀') (n : Nat), Eq.{succ u1} G₀ (f (HPow.hPow.{u2, 0, u2} G₀' Nat G₀' (instHPow.{u2, 0} G₀' Nat _inst_7) x n)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (f x) n)) -> (forall (x : G₀') (n : Int), Eq.{succ u1} G₀ (f (HPow.hPow.{u2, 0, u2} G₀' Int G₀' (instHPow.{u2, 0} G₀' Int _inst_8) x n)) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (f x) n)) -> (GroupWithZero.{u2} G₀')
Case conversion may be inaccurate. Consider using '#align function.injective.group_with_zero Function.Injective.groupWithZeroₓ'. -/
/-- Pullback a `group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀']
    [Pow G₀' ℕ] [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZero G₀' :=
  { hf.MonoidWithZero f zero one mul npow, hf.DivInvMonoid f one mul inv div npow zpow,
    pullback_nonzero f zero
      one with
    inv_zero := hf <| by erw [inv, zero, inv_zero]
    mul_inv_cancel := fun x hx =>
      hf <| by erw [one, mul, inv, mul_inv_cancel ((hf.ne_iff' zero).2 hx)] }
#align function.injective.group_with_zero Function.Injective.groupWithZero

/- warning: function.surjective.group_with_zero -> Function.Surjective.groupWithZero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} {G₀' : Type.{u2}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : Zero.{u2} G₀'] [_inst_3 : Mul.{u2} G₀'] [_inst_4 : One.{u2} G₀'] [_inst_5 : Inv.{u2} G₀'] [_inst_6 : Div.{u2} G₀'] [_inst_7 : Pow.{u2, 0} G₀' Nat] [_inst_8 : Pow.{u2, 0} G₀' Int], (Ne.{succ u2} G₀' (OfNat.ofNat.{u2} G₀' 0 (OfNat.mk.{u2} G₀' 0 (Zero.zero.{u2} G₀' _inst_2))) (OfNat.ofNat.{u2} G₀' 1 (OfNat.mk.{u2} G₀' 1 (One.one.{u2} G₀' _inst_4)))) -> (forall (f : G₀ -> G₀'), (Function.Surjective.{succ u1, succ u2} G₀ G₀' f) -> (Eq.{succ u2} G₀' (f (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (OfNat.ofNat.{u2} G₀' 0 (OfNat.mk.{u2} G₀' 0 (Zero.zero.{u2} G₀' _inst_2)))) -> (Eq.{succ u2} G₀' (f (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (OfNat.ofNat.{u2} G₀' 1 (OfNat.mk.{u2} G₀' 1 (One.one.{u2} G₀' _inst_4)))) -> (forall (x : G₀) (y : G₀), Eq.{succ u2} G₀' (f (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) x y)) (HMul.hMul.{u2, u2, u2} G₀' G₀' G₀' (instHMul.{u2} G₀' _inst_3) (f x) (f y))) -> (forall (x : G₀), Eq.{succ u2} G₀' (f (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) x)) (Inv.inv.{u2} G₀' _inst_5 (f x))) -> (forall (x : G₀) (y : G₀), Eq.{succ u2} G₀' (f (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x y)) (HDiv.hDiv.{u2, u2, u2} G₀' G₀' G₀' (instHDiv.{u2} G₀' _inst_6) (f x) (f y))) -> (forall (x : G₀) (n : Nat), Eq.{succ u2} G₀' (f (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) x n)) (HPow.hPow.{u2, 0, u2} G₀' Nat G₀' (instHPow.{u2, 0} G₀' Nat _inst_7) (f x) n)) -> (forall (x : G₀) (n : Int), Eq.{succ u2} G₀' (f (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x n)) (HPow.hPow.{u2, 0, u2} G₀' Int G₀' (instHPow.{u2, 0} G₀' Int _inst_8) (f x) n)) -> (GroupWithZero.{u2} G₀'))
but is expected to have type
  forall {G₀ : Type.{u1}} {G₀' : Type.{u2}} [_inst_1 : GroupWithZero.{u1} G₀] [_inst_2 : Zero.{u2} G₀'] [_inst_3 : Mul.{u2} G₀'] [_inst_4 : One.{u2} G₀'] [_inst_5 : Inv.{u2} G₀'] [_inst_6 : Div.{u2} G₀'] [_inst_7 : Pow.{u2, 0} G₀' Nat] [_inst_8 : Pow.{u2, 0} G₀' Int], (Ne.{succ u2} G₀' (OfNat.ofNat.{u2} G₀' 0 (Zero.toOfNat0.{u2} G₀' _inst_2)) (OfNat.ofNat.{u2} G₀' 1 (One.toOfNat1.{u2} G₀' _inst_4))) -> (forall (f : G₀ -> G₀'), (Function.Surjective.{succ u1, succ u2} G₀ G₀' f) -> (Eq.{succ u2} G₀' (f (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (OfNat.ofNat.{u2} G₀' 0 (Zero.toOfNat0.{u2} G₀' _inst_2))) -> (Eq.{succ u2} G₀' (f (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (Monoid.toOne.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))) (OfNat.ofNat.{u2} G₀' 1 (One.toOfNat1.{u2} G₀' _inst_4))) -> (forall (x : G₀) (y : G₀), Eq.{succ u2} G₀' (f (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) x y)) (HMul.hMul.{u2, u2, u2} G₀' G₀' G₀' (instHMul.{u2} G₀' _inst_3) (f x) (f y))) -> (forall (x : G₀), Eq.{succ u2} G₀' (f (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) x)) (Inv.inv.{u2} G₀' _inst_5 (f x))) -> (forall (x : G₀) (y : G₀), Eq.{succ u2} G₀' (f (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) x y)) (HDiv.hDiv.{u2, u2, u2} G₀' G₀' G₀' (instHDiv.{u2} G₀' _inst_6) (f x) (f y))) -> (forall (x : G₀) (n : Nat), Eq.{succ u2} G₀' (f (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) x n)) (HPow.hPow.{u2, 0, u2} G₀' Nat G₀' (instHPow.{u2, 0} G₀' Nat _inst_7) (f x) n)) -> (forall (x : G₀) (n : Int), Eq.{succ u2} G₀' (f (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) x n)) (HPow.hPow.{u2, 0, u2} G₀' Int G₀' (instHPow.{u2, 0} G₀' Int _inst_8) (f x) n)) -> (GroupWithZero.{u2} G₀'))
Case conversion may be inaccurate. Consider using '#align function.surjective.group_with_zero Function.Surjective.groupWithZeroₓ'. -/
/-- Pushforward a `group_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀']
    [Pow G₀' ℕ] [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) :
    GroupWithZero G₀' :=
  { hf.MonoidWithZero f zero one mul npow,
    hf.DivInvMonoid f one mul inv div npow
      zpow with
    inv_zero := by erw [← zero, ← inv, inv_zero]
    mul_inv_cancel :=
      hf.forall.2 fun x hx => by
        erw [← inv, ← mul, mul_inv_cancel (mt (congr_arg f) <| trans_rel_left Ne hx zero.symm)] <;>
          exact one
    exists_pair_ne := ⟨0, 1, h01⟩ }
#align function.surjective.group_with_zero Function.Surjective.groupWithZero

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀] {a b c d : G₀}

/- warning: function.injective.comm_group_with_zero -> Function.Injective.commGroupWithZero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} {G₀' : Type.{u2}} [_inst_1 : CommGroupWithZero.{u1} G₀] [_inst_2 : Zero.{u2} G₀'] [_inst_3 : Mul.{u2} G₀'] [_inst_4 : One.{u2} G₀'] [_inst_5 : Inv.{u2} G₀'] [_inst_6 : Div.{u2} G₀'] [_inst_7 : Pow.{u2, 0} G₀' Nat] [_inst_8 : Pow.{u2, 0} G₀' Int] (f : G₀' -> G₀), (Function.Injective.{succ u2, succ u1} G₀' G₀ f) -> (Eq.{succ u1} G₀ (f (OfNat.ofNat.{u2} G₀' 0 (OfNat.mk.{u2} G₀' 0 (Zero.zero.{u2} G₀' _inst_2)))) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))))))) -> (Eq.{succ u1} G₀ (f (OfNat.ofNat.{u2} G₀' 1 (OfNat.mk.{u2} G₀' 1 (One.one.{u2} G₀' _inst_4)))) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))))))) -> (forall (x : G₀') (y : G₀'), Eq.{succ u1} G₀ (f (HMul.hMul.{u2, u2, u2} G₀' G₀' G₀' (instHMul.{u2} G₀' _inst_3) x y)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) (f x) (f y))) -> (forall (x : G₀'), Eq.{succ u1} G₀ (f (Inv.inv.{u2} G₀' _inst_5 x)) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))) (f x))) -> (forall (x : G₀') (y : G₀'), Eq.{succ u1} G₀ (f (HDiv.hDiv.{u2, u2, u2} G₀' G₀' G₀' (instHDiv.{u2} G₀' _inst_6) x y)) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))) (f x) (f y))) -> (forall (x : G₀') (n : Nat), Eq.{succ u1} G₀ (f (HPow.hPow.{u2, 0, u2} G₀' Nat G₀' (instHPow.{u2, 0} G₀' Nat _inst_7) x n)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))) (f x) n)) -> (forall (x : G₀') (n : Int), Eq.{succ u1} G₀ (f (HPow.hPow.{u2, 0, u2} G₀' Int G₀' (instHPow.{u2, 0} G₀' Int _inst_8) x n)) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))) (f x) n)) -> (CommGroupWithZero.{u2} G₀')
but is expected to have type
  forall {G₀ : Type.{u1}} {G₀' : Type.{u2}} [_inst_1 : CommGroupWithZero.{u1} G₀] [_inst_2 : Zero.{u2} G₀'] [_inst_3 : Mul.{u2} G₀'] [_inst_4 : One.{u2} G₀'] [_inst_5 : Inv.{u2} G₀'] [_inst_6 : Div.{u2} G₀'] [_inst_7 : Pow.{u2, 0} G₀' Nat] [_inst_8 : Pow.{u2, 0} G₀' Int] (f : G₀' -> G₀), (Function.Injective.{succ u2, succ u1} G₀' G₀ f) -> (Eq.{succ u1} G₀ (f (OfNat.ofNat.{u2} G₀' 0 (Zero.toOfNat0.{u2} G₀' _inst_2))) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (CommMonoidWithZero.toZero.{u1} G₀ (CommGroupWithZero.toCommMonoidWithZero.{u1} G₀ _inst_1))))) -> (Eq.{succ u1} G₀ (f (OfNat.ofNat.{u2} G₀' 1 (One.toOfNat1.{u2} G₀' _inst_4))) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (Monoid.toOne.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))))) -> (forall (x : G₀') (y : G₀'), Eq.{succ u1} G₀ (f (HMul.hMul.{u2, u2, u2} G₀' G₀' G₀' (instHMul.{u2} G₀' _inst_3) x y)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) (f x) (f y))) -> (forall (x : G₀'), Eq.{succ u1} G₀ (f (Inv.inv.{u2} G₀' _inst_5 x)) (Inv.inv.{u1} G₀ (CommGroupWithZero.toInv.{u1} G₀ _inst_1) (f x))) -> (forall (x : G₀') (y : G₀'), Eq.{succ u1} G₀ (f (HDiv.hDiv.{u2, u2, u2} G₀' G₀' G₀' (instHDiv.{u2} G₀' _inst_6) x y)) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (CommGroupWithZero.toDiv.{u1} G₀ _inst_1)) (f x) (f y))) -> (forall (x : G₀') (n : Nat), Eq.{succ u1} G₀ (f (HPow.hPow.{u2, 0, u2} G₀' Nat G₀' (instHPow.{u2, 0} G₀' Nat _inst_7) x n)) (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))) (f x) n)) -> (forall (x : G₀') (n : Int), Eq.{succ u1} G₀ (f (HPow.hPow.{u2, 0, u2} G₀' Int G₀' (instHPow.{u2, 0} G₀' Int _inst_8) x n)) (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))) (f x) n)) -> (CommGroupWithZero.{u2} G₀')
Case conversion may be inaccurate. Consider using '#align function.injective.comm_group_with_zero Function.Injective.commGroupWithZeroₓ'. -/
/-- Pullback a `comm_group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' ℕ] [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.GroupWithZero f zero one mul inv div npow zpow, hf.CommSemigroup f mul with }
#align function.injective.comm_group_with_zero Function.Injective.commGroupWithZero

/- warning: function.surjective.comm_group_with_zero -> Function.Surjective.commGroupWithZero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} {G₀' : Type.{u2}} [_inst_1 : CommGroupWithZero.{u1} G₀] [_inst_2 : Zero.{u2} G₀'] [_inst_3 : Mul.{u2} G₀'] [_inst_4 : One.{u2} G₀'] [_inst_5 : Inv.{u2} G₀'] [_inst_6 : Div.{u2} G₀'] [_inst_7 : Pow.{u2, 0} G₀' Nat] [_inst_8 : Pow.{u2, 0} G₀' Int], (Ne.{succ u2} G₀' (OfNat.ofNat.{u2} G₀' 0 (OfNat.mk.{u2} G₀' 0 (Zero.zero.{u2} G₀' _inst_2))) (OfNat.ofNat.{u2} G₀' 1 (OfNat.mk.{u2} G₀' 1 (One.one.{u2} G₀' _inst_4)))) -> (forall (f : G₀ -> G₀'), (Function.Surjective.{succ u1, succ u2} G₀ G₀' f) -> (Eq.{succ u2} G₀' (f (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))))))) (OfNat.ofNat.{u2} G₀' 0 (OfNat.mk.{u2} G₀' 0 (Zero.zero.{u2} G₀' _inst_2)))) -> (Eq.{succ u2} G₀' (f (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))))))) (OfNat.ofNat.{u2} G₀' 1 (OfNat.mk.{u2} G₀' 1 (One.one.{u2} G₀' _inst_4)))) -> (forall (x : G₀) (y : G₀), Eq.{succ u2} G₀' (f (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) x y)) (HMul.hMul.{u2, u2, u2} G₀' G₀' G₀' (instHMul.{u2} G₀' _inst_3) (f x) (f y))) -> (forall (x : G₀), Eq.{succ u2} G₀' (f (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))) x)) (Inv.inv.{u2} G₀' _inst_5 (f x))) -> (forall (x : G₀) (y : G₀), Eq.{succ u2} G₀' (f (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))) x y)) (HDiv.hDiv.{u2, u2, u2} G₀' G₀' G₀' (instHDiv.{u2} G₀' _inst_6) (f x) (f y))) -> (forall (x : G₀) (n : Nat), Eq.{succ u2} G₀' (f (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))) x n)) (HPow.hPow.{u2, 0, u2} G₀' Nat G₀' (instHPow.{u2, 0} G₀' Nat _inst_7) (f x) n)) -> (forall (x : G₀) (n : Int), Eq.{succ u2} G₀' (f (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))) x n)) (HPow.hPow.{u2, 0, u2} G₀' Int G₀' (instHPow.{u2, 0} G₀' Int _inst_8) (f x) n)) -> (CommGroupWithZero.{u2} G₀'))
but is expected to have type
  forall {G₀ : Type.{u1}} {G₀' : Type.{u2}} [_inst_1 : CommGroupWithZero.{u1} G₀] [_inst_2 : Zero.{u2} G₀'] [_inst_3 : Mul.{u2} G₀'] [_inst_4 : One.{u2} G₀'] [_inst_5 : Inv.{u2} G₀'] [_inst_6 : Div.{u2} G₀'] [_inst_7 : Pow.{u2, 0} G₀' Nat] [_inst_8 : Pow.{u2, 0} G₀' Int], (Ne.{succ u2} G₀' (OfNat.ofNat.{u2} G₀' 0 (Zero.toOfNat0.{u2} G₀' _inst_2)) (OfNat.ofNat.{u2} G₀' 1 (One.toOfNat1.{u2} G₀' _inst_4))) -> (forall (f : G₀ -> G₀'), (Function.Surjective.{succ u1, succ u2} G₀ G₀' f) -> (Eq.{succ u2} G₀' (f (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (CommMonoidWithZero.toZero.{u1} G₀ (CommGroupWithZero.toCommMonoidWithZero.{u1} G₀ _inst_1))))) (OfNat.ofNat.{u2} G₀' 0 (Zero.toOfNat0.{u2} G₀' _inst_2))) -> (Eq.{succ u2} G₀' (f (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (Monoid.toOne.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))))) (OfNat.ofNat.{u2} G₀' 1 (One.toOfNat1.{u2} G₀' _inst_4))) -> (forall (x : G₀) (y : G₀), Eq.{succ u2} G₀' (f (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) x y)) (HMul.hMul.{u2, u2, u2} G₀' G₀' G₀' (instHMul.{u2} G₀' _inst_3) (f x) (f y))) -> (forall (x : G₀), Eq.{succ u2} G₀' (f (Inv.inv.{u1} G₀ (CommGroupWithZero.toInv.{u1} G₀ _inst_1) x)) (Inv.inv.{u2} G₀' _inst_5 (f x))) -> (forall (x : G₀) (y : G₀), Eq.{succ u2} G₀' (f (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (CommGroupWithZero.toDiv.{u1} G₀ _inst_1)) x y)) (HDiv.hDiv.{u2, u2, u2} G₀' G₀' G₀' (instHDiv.{u2} G₀' _inst_6) (f x) (f y))) -> (forall (x : G₀) (n : Nat), Eq.{succ u2} G₀' (f (HPow.hPow.{u1, 0, u1} G₀ Nat G₀ (instHPow.{u1, 0} G₀ Nat (Monoid.Pow.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1))))) x n)) (HPow.hPow.{u2, 0, u2} G₀' Nat G₀' (instHPow.{u2, 0} G₀' Nat _inst_7) (f x) n)) -> (forall (x : G₀) (n : Int), Eq.{succ u2} G₀' (f (HPow.hPow.{u1, 0, u1} G₀ Int G₀ (instHPow.{u1, 0} G₀ Int (DivInvMonoid.Pow.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))) x n)) (HPow.hPow.{u2, 0, u2} G₀' Int G₀' (instHPow.{u2, 0} G₀' Int _inst_8) (f x) n)) -> (CommGroupWithZero.{u2} G₀'))
Case conversion may be inaccurate. Consider using '#align function.surjective.comm_group_with_zero Function.Surjective.commGroupWithZeroₓ'. -/
/-- Pushforward a `comm_group_with_zero` class along a surjective function. -/
protected def Function.Surjective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' ℕ] [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) :
    CommGroupWithZero G₀' :=
  { hf.GroupWithZero h01 f zero one mul inv div npow zpow, hf.CommSemigroup f mul with }
#align function.surjective.comm_group_with_zero Function.Surjective.commGroupWithZero

end CommGroupWithZero


/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.group_with_zero.basic
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Basic
import Mathbin.Algebra.GroupWithZero.Defs
import Mathbin.Algebra.Group.OrderSynonym

/-!
# Groups with an adjoined zero element

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `group_with_zero` and `comm_group_with_zero`.
To reduce import dependencies, the type-classes themselves are in
`algebra.group_with_zero.defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/


open Classical

open Function

variable {α M₀ G₀ M₀' G₀' F F' : Type _}

section

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

/- warning: left_ne_zero_of_mul -> left_ne_zero_of_mul is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] {a : M₀} {b : M₀}, (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) -> (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] {a : M₀} {b : M₀}, (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) -> (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align left_ne_zero_of_mul left_ne_zero_of_mulₓ'. -/
theorem left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 :=
  mt fun h => mul_eq_zero_of_left h b
#align left_ne_zero_of_mul left_ne_zero_of_mul

/- warning: right_ne_zero_of_mul -> right_ne_zero_of_mul is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] {a : M₀} {b : M₀}, (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) -> (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] {a : M₀} {b : M₀}, (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) -> (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align right_ne_zero_of_mul right_ne_zero_of_mulₓ'. -/
theorem right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 :=
  mt (mul_eq_zero_of_right a)
#align right_ne_zero_of_mul right_ne_zero_of_mul

/- warning: ne_zero_and_ne_zero_of_mul -> ne_zero_and_ne_zero_of_mul is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] {a : M₀} {b : M₀}, (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) -> (And (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] {a : M₀} {b : M₀}, (Ne.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) -> (And (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ne_zero_and_ne_zero_of_mul ne_zero_and_ne_zero_of_mulₓ'. -/
theorem ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩
#align ne_zero_and_ne_zero_of_mul ne_zero_and_ne_zero_of_mul

/- warning: mul_eq_zero_of_ne_zero_imp_eq_zero -> mul_eq_zero_of_ne_zero_imp_eq_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] {a : M₀} {b : M₀}, ((Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) -> (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀] {a : M₀} {b : M₀}, ((Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) -> (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_eq_zero_of_ne_zero_imp_eq_zero mul_eq_zero_of_ne_zero_imp_eq_zeroₓ'. -/
theorem mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) : a * b = 0 :=
  if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]
#align mul_eq_zero_of_ne_zero_imp_eq_zero mul_eq_zero_of_ne_zero_imp_eq_zero

/- warning: zero_mul_eq_const -> zero_mul_eq_const is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀], Eq.{succ u1} (M₀ -> M₀) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Function.const.{succ u1, succ u1} M₀ M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀], Eq.{succ u1} (M₀ -> M₀) ((fun (x._@.Mathlib.Algebra.GroupWithZero.Basic._hyg.282 : M₀) (x._@.Mathlib.Algebra.GroupWithZero.Basic._hyg.284 : M₀) => HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) x._@.Mathlib.Algebra.GroupWithZero.Basic._hyg.282 x._@.Mathlib.Algebra.GroupWithZero.Basic._hyg.284) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Function.const.{succ u1, succ u1} M₀ M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align zero_mul_eq_const zero_mul_eq_constₓ'. -/
/-- To match `one_mul_eq_id`. -/
theorem zero_mul_eq_const : (· * ·) (0 : M₀) = Function.const _ 0 :=
  funext zero_mul
#align zero_mul_eq_const zero_mul_eq_const

/- warning: mul_zero_eq_const -> mul_zero_eq_const is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀], Eq.{succ u1} (M₀ -> M₀) (fun (_x : M₀) => HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ _inst_1)) _x (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1))))) (Function.const.{succ u1, succ u1} M₀ M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ _inst_1)))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroClass.{u1} M₀], Eq.{succ u1} (M₀ -> M₀) (fun (_x : M₀) => HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ _inst_1)) _x (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1)))) (Function.const.{succ u1, succ u1} M₀ M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_zero_eq_const mul_zero_eq_constₓ'. -/
/-- To match `mul_one_eq_id`. -/
theorem mul_zero_eq_const : (· * (0 : M₀)) = Function.const _ 0 :=
  funext mul_zero
#align mul_zero_eq_const mul_zero_eq_const

end MulZeroClass

section Mul

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

#print eq_zero_of_mul_self_eq_zero /-
theorem eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0 :=
  (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id
#align eq_zero_of_mul_self_eq_zero eq_zero_of_mul_self_eq_zero
-/

#print mul_ne_zero /-
@[field_simps]
theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  mt eq_zero_or_eq_zero_of_mul_eq_zero <| not_or.mpr ⟨ha, hb⟩
#align mul_ne_zero mul_ne_zero
-/

end Mul

namespace NeZero

#print NeZero.mul /-
instance mul [Zero M₀] [Mul M₀] [NoZeroDivisors M₀] {x y : M₀} [NeZero x] [NeZero y] :
    NeZero (x * y) :=
  ⟨mul_ne_zero out out⟩
#align ne_zero.mul NeZero.mul
-/

end NeZero

end

section

variable [MulZeroOneClass M₀]

/- warning: eq_zero_of_zero_eq_one -> eq_zero_of_zero_eq_one is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) -> (forall (a : M₀), Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) -> (forall (a : M₀), Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align eq_zero_of_zero_eq_one eq_zero_of_zero_eq_oneₓ'. -/
/-- In a monoid with zero, if zero equals one, then zero is the only element. -/
theorem eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 := by
  rw [← mul_one a, ← h, mul_zero]
#align eq_zero_of_zero_eq_one eq_zero_of_zero_eq_one

/- warning: unique_of_zero_eq_one -> uniqueOfZeroEqOne is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) -> (Unique.{succ u1} M₀)
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) -> (Unique.{succ u1} M₀)
Case conversion may be inaccurate. Consider using '#align unique_of_zero_eq_one uniqueOfZeroEqOneₓ'. -/
/-- In a monoid with zero, if zero equals one, then zero is the unique element.

Somewhat arbitrarily, we define the default element to be `0`.
All other elements will be provably equal to it, but not necessarily definitionally equal. -/
def uniqueOfZeroEqOne (h : (0 : M₀) = 1) : Unique M₀
    where
  default := 0
  uniq := eq_zero_of_zero_eq_one h
#align unique_of_zero_eq_one uniqueOfZeroEqOne

/- warning: subsingleton_iff_zero_eq_one -> subsingleton_iff_zero_eq_one is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], Iff (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) (Subsingleton.{succ u1} M₀)
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], Iff (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) (Subsingleton.{succ u1} M₀)
Case conversion may be inaccurate. Consider using '#align subsingleton_iff_zero_eq_one subsingleton_iff_zero_eq_oneₓ'. -/
/-- In a monoid with zero, zero equals one if and only if all elements of that semiring
are equal. -/
theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ Subsingleton M₀ :=
  ⟨fun h => @Unique.subsingleton _ (uniqueOfZeroEqOne h), fun h => @Subsingleton.elim _ h _ _⟩
#align subsingleton_iff_zero_eq_one subsingleton_iff_zero_eq_one

/- warning: subsingleton_of_zero_eq_one -> subsingleton_of_zero_eq_one is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) -> (Subsingleton.{succ u1} M₀)
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) -> (Subsingleton.{succ u1} M₀)
Case conversion may be inaccurate. Consider using '#align subsingleton_of_zero_eq_one subsingleton_of_zero_eq_oneₓ'. -/
alias subsingleton_iff_zero_eq_one ↔ subsingleton_of_zero_eq_one _
#align subsingleton_of_zero_eq_one subsingleton_of_zero_eq_one

/- warning: eq_of_zero_eq_one -> eq_of_zero_eq_one is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) -> (forall (a : M₀) (b : M₀), Eq.{succ u1} M₀ a b)
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) -> (forall (a : M₀) (b : M₀), Eq.{succ u1} M₀ a b)
Case conversion may be inaccurate. Consider using '#align eq_of_zero_eq_one eq_of_zero_eq_oneₓ'. -/
theorem eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b :=
  @Subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b
#align eq_of_zero_eq_one eq_of_zero_eq_one

/- warning: zero_ne_one_or_forall_eq_0 -> zero_ne_one_or_forall_eq_0 is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], Or (Ne.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) (forall (a : M₀), Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀], Or (Ne.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) (forall (a : M₀), Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align zero_ne_one_or_forall_eq_0 zero_ne_one_or_forall_eq_0ₓ'. -/
/-- In a monoid with zero, either zero and one are nonequal, or zero is the only element. -/
theorem zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ ∀ a : M₀, a = 0 :=
  not_or_of_imp eq_zero_of_zero_eq_one
#align zero_ne_one_or_forall_eq_0 zero_ne_one_or_forall_eq_0

end

section

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

/- warning: left_ne_zero_of_mul_eq_one -> left_ne_zero_of_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] {a : M₀} {b : M₀}, (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))) a b) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) -> (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] {a : M₀} {b : M₀}, (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))) a b) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) -> (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align left_ne_zero_of_mul_eq_one left_ne_zero_of_mul_eq_oneₓ'. -/
theorem left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 :=
  left_ne_zero_of_mul <| neZero_of_eq_one h
#align left_ne_zero_of_mul_eq_one left_ne_zero_of_mul_eq_one

/- warning: right_ne_zero_of_mul_eq_one -> right_ne_zero_of_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] {a : M₀} {b : M₀}, (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))) a b) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1)))))) -> (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MulZeroOneClass.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] {a : M₀} {b : M₀}, (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ _inst_1))) a b) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (MulOneClass.toOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ _inst_1))))) -> (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MulZeroOneClass.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align right_ne_zero_of_mul_eq_one right_ne_zero_of_mul_eq_oneₓ'. -/
theorem right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 :=
  right_ne_zero_of_mul <| neZero_of_eq_one h
#align right_ne_zero_of_mul_eq_one right_ne_zero_of_mul_eq_one

end

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

/- warning: cancel_monoid_with_zero.to_no_zero_divisors -> CancelMonoidWithZero.to_noZeroDivisors is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀], NoZeroDivisors.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))) (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀], NoZeroDivisors.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))) (MonoidWithZero.toZero.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))
Case conversion may be inaccurate. Consider using '#align cancel_monoid_with_zero.to_no_zero_divisors CancelMonoidWithZero.to_noZeroDivisorsₓ'. -/
-- see Note [lower instance priority]
instance (priority := 10) CancelMonoidWithZero.to_noZeroDivisors : NoZeroDivisors M₀ :=
  ⟨fun a b ab0 => by
    by_cases a = 0
    · left
      exact h
    right
    apply CancelMonoidWithZero.mul_left_cancel_of_ne_zero h
    rw [ab0, mul_zero]⟩
#align cancel_monoid_with_zero.to_no_zero_divisors CancelMonoidWithZero.to_noZeroDivisors

/- warning: mul_left_inj' -> mul_left_inj' is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀} {c : M₀}, (Ne.{succ u1} M₀ c (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))) -> (Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a c) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) b c)) (Eq.{succ u1} M₀ a b))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀} {c : M₀}, (Ne.{succ u1} M₀ c (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) -> (Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a c) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) b c)) (Eq.{succ u1} M₀ a b))
Case conversion may be inaccurate. Consider using '#align mul_left_inj' mul_left_inj'ₓ'. -/
theorem mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b :=
  (mul_left_injective₀ hc).eq_iff
#align mul_left_inj' mul_left_inj'

/- warning: mul_right_inj' -> mul_right_inj' is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀} {c : M₀}, (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))) -> (Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a c)) (Eq.{succ u1} M₀ b c))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀} {c : M₀}, (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) -> (Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a c)) (Eq.{succ u1} M₀ b c))
Case conversion may be inaccurate. Consider using '#align mul_right_inj' mul_right_inj'ₓ'. -/
theorem mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  (mul_right_injective₀ ha).eq_iff
#align mul_right_inj' mul_right_inj'

/- warning: mul_eq_mul_right_iff -> mul_eq_mul_right_iff is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀} {c : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a c) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) b c)) (Or (Eq.{succ u1} M₀ a b) (Eq.{succ u1} M₀ c (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀} {c : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a c) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) b c)) (Or (Eq.{succ u1} M₀ a b) (Eq.{succ u1} M₀ c (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))))
Case conversion may be inaccurate. Consider using '#align mul_eq_mul_right_iff mul_eq_mul_right_iffₓ'. -/
@[simp]
theorem mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 := by
  by_cases hc : c = 0 <;> [simp [hc], simp [mul_left_inj', hc]]
#align mul_eq_mul_right_iff mul_eq_mul_right_iff

/- warning: mul_eq_mul_left_iff -> mul_eq_mul_left_iff is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀} {c : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a c)) (Or (Eq.{succ u1} M₀ b c) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀} {c : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a b) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a c)) (Or (Eq.{succ u1} M₀ b c) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))))
Case conversion may be inaccurate. Consider using '#align mul_eq_mul_left_iff mul_eq_mul_left_iffₓ'. -/
@[simp]
theorem mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 := by
  by_cases ha : a = 0 <;> [simp [ha], simp [mul_right_inj', ha]]
#align mul_eq_mul_left_iff mul_eq_mul_left_iff

/- warning: mul_right_eq_self₀ -> mul_right_eq_self₀ is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a b) a) (Or (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a b) a) (Or (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))))
Case conversion may be inaccurate. Consider using '#align mul_right_eq_self₀ mul_right_eq_self₀ₓ'. -/
theorem mul_right_eq_self₀ : a * b = a ↔ b = 1 ∨ a = 0 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff
    
#align mul_right_eq_self₀ mul_right_eq_self₀

/- warning: mul_left_eq_self₀ -> mul_left_eq_self₀ is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a b) b) (Or (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))) (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a b) b) (Or (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))) (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))))
Case conversion may be inaccurate. Consider using '#align mul_left_eq_self₀ mul_left_eq_self₀ₓ'. -/
theorem mul_left_eq_self₀ : a * b = b ↔ a = 1 ∨ b = 0 :=
  calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff
    
#align mul_left_eq_self₀ mul_left_eq_self₀

/- warning: eq_zero_of_mul_eq_self_right -> eq_zero_of_mul_eq_self_right is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a b) a) -> (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) a b) a) -> (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align eq_zero_of_mul_eq_self_right eq_zero_of_mul_eq_self_rightₓ'. -/
/-- An element of a `cancel_monoid_with_zero` fixed by right multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_right (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  by_contradiction fun ha => h₁ <| mul_left_cancel₀ ha <| h₂.symm ▸ (mul_one a).symm
#align eq_zero_of_mul_eq_self_right eq_zero_of_mul_eq_self_right

/- warning: eq_zero_of_mul_eq_self_left -> eq_zero_of_mul_eq_self_left is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))))) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) b a) a) -> (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : CancelMonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, (Ne.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1))))) b a) a) -> (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ (CancelMonoidWithZero.toMonoidWithZero.{u1} M₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align eq_zero_of_mul_eq_self_left eq_zero_of_mul_eq_self_leftₓ'. -/
/-- An element of a `cancel_monoid_with_zero` fixed by left multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_left (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  by_contradiction fun ha => h₁ <| mul_right_cancel₀ ha <| h₂.symm ▸ (one_mul a).symm
#align eq_zero_of_mul_eq_self_left eq_zero_of_mul_eq_self_left

end CancelMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c g h x : G₀}

/- warning: mul_inv_cancel_right₀ -> mul_inv_cancel_right₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {b : G₀}, (Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a b) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) b)) a)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {b : G₀}, (Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (forall (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a b) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) b)) a)
Case conversion may be inaccurate. Consider using '#align mul_inv_cancel_right₀ mul_inv_cancel_right₀ₓ'. -/
@[simp]
theorem mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]
    
#align mul_inv_cancel_right₀ mul_inv_cancel_right₀

/- warning: mul_inv_cancel_left₀ -> mul_inv_cancel_left₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (b : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a) b)) b)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (forall (b : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a) b)) b)
Case conversion may be inaccurate. Consider using '#align mul_inv_cancel_left₀ mul_inv_cancel_left₀ₓ'. -/
@[simp]
theorem mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]
    
#align mul_inv_cancel_left₀ mul_inv_cancel_left₀

/- warning: inv_ne_zero -> inv_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Ne.{succ u1} G₀ (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Ne.{succ u1} G₀ (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align inv_ne_zero inv_ne_zeroₓ'. -/
theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by simpa [a_eq_0] using mul_inv_cancel h
#align inv_ne_zero inv_ne_zero

/- warning: inv_mul_cancel -> inv_mul_cancel is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a) a) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a) a) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (Monoid.toOne.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))
Case conversion may be inaccurate. Consider using '#align inv_mul_cancel inv_mul_cancelₓ'. -/
@[simp]
theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]
    
#align inv_mul_cancel inv_mul_cancel

/- warning: group_with_zero.mul_left_injective -> GroupWithZero.mul_left_injective is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {x : G₀}, (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Function.Injective.{succ u1, succ u1} G₀ G₀ (fun (y : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) x y))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {x : G₀}, (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Function.Injective.{succ u1, succ u1} G₀ G₀ (fun (y : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) x y))
Case conversion may be inaccurate. Consider using '#align group_with_zero.mul_left_injective GroupWithZero.mul_left_injectiveₓ'. -/
theorem GroupWithZero.mul_left_injective (h : x ≠ 0) : Function.Injective fun y => x * y :=
  fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel h, one_mul] using congr_arg (fun y => x⁻¹ * y) w
#align group_with_zero.mul_left_injective GroupWithZero.mul_left_injective

/- warning: group_with_zero.mul_right_injective -> GroupWithZero.mul_right_injective is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {x : G₀}, (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Function.Injective.{succ u1, succ u1} G₀ G₀ (fun (y : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) y x))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {x : G₀}, (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Function.Injective.{succ u1, succ u1} G₀ G₀ (fun (y : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) y x))
Case conversion may be inaccurate. Consider using '#align group_with_zero.mul_right_injective GroupWithZero.mul_right_injectiveₓ'. -/
theorem GroupWithZero.mul_right_injective (h : x ≠ 0) : Function.Injective fun y => y * x :=
  fun y y' w => by
  simpa only [mul_assoc, mul_inv_cancel h, mul_one] using congr_arg (fun y => y * x⁻¹) w
#align group_with_zero.mul_right_injective GroupWithZero.mul_right_injective

/- warning: inv_mul_cancel_right₀ -> inv_mul_cancel_right₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {b : G₀}, (Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) b)) b) a)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {b : G₀}, (Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (forall (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) b)) b) a)
Case conversion may be inaccurate. Consider using '#align inv_mul_cancel_right₀ inv_mul_cancel_right₀ₓ'. -/
@[simp]
theorem inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b⁻¹ * b = a :=
  calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]
    
#align inv_mul_cancel_right₀ inv_mul_cancel_right₀

/- warning: inv_mul_cancel_left₀ -> inv_mul_cancel_left₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (forall (b : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a b)) b)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (forall (b : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a b)) b)
Case conversion may be inaccurate. Consider using '#align inv_mul_cancel_left₀ inv_mul_cancel_left₀ₓ'. -/
@[simp]
theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]
    
#align inv_mul_cancel_left₀ inv_mul_cancel_left₀

private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]
#align inv_eq_of_mul inv_eq_of_mul

#print GroupWithZero.toDivisionMonoid /-
-- See note [lower instance priority]
instance (priority := 100) GroupWithZero.toDivisionMonoid : DivisionMonoid G₀ :=
  { ‹GroupWithZero G₀› with
    inv := Inv.inv
    inv_inv := fun a => by
      by_cases h : a = 0
      · simp [h]
      · exact left_inv_eq_right_inv (inv_mul_cancel <| inv_ne_zero h) (inv_mul_cancel h)
    mul_inv_rev := fun a b => by
      by_cases ha : a = 0; · simp [ha]
      by_cases hb : b = 0; · simp [hb]
      refine' inv_eq_of_mul _
      simp [mul_assoc, ha, hb]
    inv_eq_of_mul := fun a b => inv_eq_of_mul }
#align group_with_zero.to_division_monoid GroupWithZero.toDivisionMonoid
-/

end GroupWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c : G₀}

/- warning: zero_div -> zero_div is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))) a) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align zero_div zero_divₓ'. -/
@[simp]
theorem zero_div (a : G₀) : 0 / a = 0 := by rw [div_eq_mul_inv, zero_mul]
#align zero_div zero_div

/- warning: div_zero -> div_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align div_zero div_zeroₓ'. -/
@[simp]
theorem div_zero (a : G₀) : a / 0 = 0 := by rw [div_eq_mul_inv, inv_zero, mul_zero]
#align div_zero div_zero

/- warning: mul_self_mul_inv -> mul_self_mul_inv is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a a) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a)) a
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a a) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a)) a
Case conversion may be inaccurate. Consider using '#align mul_self_mul_inv mul_self_mul_invₓ'. -/
/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a :=
  by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_assoc, mul_inv_cancel h, mul_one]
#align mul_self_mul_inv mul_self_mul_inv

/- warning: mul_inv_mul_self -> mul_inv_mul_self is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a)) a) a
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a)) a) a
Case conversion may be inaccurate. Consider using '#align mul_inv_mul_self mul_inv_mul_selfₓ'. -/
/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_inv_mul_self (a : G₀) : a * a⁻¹ * a = a :=
  by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [mul_inv_cancel h, one_mul]
#align mul_inv_mul_self mul_inv_mul_self

/- warning: inv_mul_mul_self -> inv_mul_mul_self is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a) a) a) a
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a) a) a) a
Case conversion may be inaccurate. Consider using '#align inv_mul_mul_self inv_mul_mul_selfₓ'. -/
/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp]
theorem inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a :=
  by
  by_cases h : a = 0
  · rw [h, inv_zero, mul_zero]
  · rw [inv_mul_cancel h, one_mul]
#align inv_mul_mul_self inv_mul_mul_self

/- warning: mul_self_div_self -> mul_self_div_self is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a a) a) a
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a a) a) a
Case conversion may be inaccurate. Consider using '#align mul_self_div_self mul_self_div_selfₓ'. -/
/-- Multiplying `a` by itself and then dividing by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem mul_self_div_self (a : G₀) : a * a / a = a := by rw [div_eq_mul_inv, mul_self_mul_inv a]
#align mul_self_div_self mul_self_div_self

/- warning: div_self_mul_self -> div_self_mul_self is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a a) a) a
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) a a) a) a
Case conversion may be inaccurate. Consider using '#align div_self_mul_self div_self_mul_selfₓ'. -/
/-- Dividing `a` by itself and then multiplying by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem div_self_mul_self (a : G₀) : a / a * a = a := by rw [div_eq_mul_inv, mul_inv_mul_self a]
#align div_self_mul_self div_self_mul_self

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

/- warning: div_self_mul_self' -> div_self_mul_self' is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a a)) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) a (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a a)) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a)
Case conversion may be inaccurate. Consider using '#align div_self_mul_self' div_self_mul_self'ₓ'. -/
@[simp]
theorem div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ :=
  calc
    a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ := by simp [mul_inv_rev]
    _ = a⁻¹ := inv_mul_mul_self _
    
#align div_self_mul_self' div_self_mul_self'

/- warning: one_div_ne_zero -> one_div_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Ne.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))) a) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Ne.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (InvOneClass.toOne.{u1} G₀ (DivInvOneMonoid.toInvOneClass.{u1} G₀ (DivisionMonoid.toDivInvOneMonoid.{u1} G₀ (GroupWithZero.toDivisionMonoid.{u1} G₀ _inst_1)))))) a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align one_div_ne_zero one_div_ne_zeroₓ'. -/
theorem one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 := by
  simpa only [one_div] using inv_ne_zero h
#align one_div_ne_zero one_div_ne_zero

/- warning: inv_eq_zero -> inv_eq_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, Iff (Eq.{succ u1} G₀ (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) (Eq.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, Iff (Eq.{succ u1} G₀ (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) (Eq.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align inv_eq_zero inv_eq_zeroₓ'. -/
@[simp]
theorem inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 := by rw [inv_eq_iff_inv_eq, inv_zero, eq_comm]
#align inv_eq_zero inv_eq_zero

/- warning: zero_eq_inv -> zero_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, Iff (Eq.{succ u1} G₀ (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1)) a)) (Eq.{succ u1} G₀ (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))) a)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, Iff (Eq.{succ u1} G₀ (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_1) a)) (Eq.{succ u1} G₀ (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align zero_eq_inv zero_eq_invₓ'. -/
@[simp]
theorem zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a :=
  eq_comm.trans <| inv_eq_zero.trans eq_comm
#align zero_eq_inv zero_eq_inv

/- warning: div_div_self -> div_div_self is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) a a)) a
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) a (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) a a)) a
Case conversion may be inaccurate. Consider using '#align div_div_self div_div_selfₓ'. -/
/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp]
theorem div_div_self (a : G₀) : a / (a / a) = a :=
  by
  rw [div_div_eq_mul_div]
  exact mul_self_div_self a
#align div_div_self div_div_self

/- warning: ne_zero_of_one_div_ne_zero -> ne_zero_of_one_div_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))) a) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (InvOneClass.toOne.{u1} G₀ (DivInvOneMonoid.toInvOneClass.{u1} G₀ (DivisionMonoid.toDivInvOneMonoid.{u1} G₀ (GroupWithZero.toDivisionMonoid.{u1} G₀ _inst_1)))))) a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ne_zero_of_one_div_ne_zero ne_zero_of_one_div_ne_zeroₓ'. -/
theorem ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 := fun ha : a = 0 => by
  rw [ha, div_zero] at h; contradiction
#align ne_zero_of_one_div_ne_zero ne_zero_of_one_div_ne_zero

/- warning: eq_zero_of_one_div_eq_zero -> eq_zero_of_one_div_eq_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_1))) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))) a) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Eq.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_1)) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (InvOneClass.toOne.{u1} G₀ (DivInvOneMonoid.toInvOneClass.{u1} G₀ (DivisionMonoid.toDivInvOneMonoid.{u1} G₀ (GroupWithZero.toDivisionMonoid.{u1} G₀ _inst_1)))))) a) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Eq.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align eq_zero_of_one_div_eq_zero eq_zero_of_one_div_eq_zeroₓ'. -/
theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
  by_cases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim
#align eq_zero_of_one_div_eq_zero eq_zero_of_one_div_eq_zero

/- warning: mul_left_surjective₀ -> mul_left_surjective₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Function.Surjective.{succ u1, succ u1} G₀ G₀ (fun (g : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a g))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Function.Surjective.{succ u1, succ u1} G₀ G₀ (fun (g : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) a g))
Case conversion may be inaccurate. Consider using '#align mul_left_surjective₀ mul_left_surjective₀ₓ'. -/
theorem mul_left_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => a * g := fun g =>
  ⟨a⁻¹ * g, by simp [← mul_assoc, mul_inv_cancel h]⟩
#align mul_left_surjective₀ mul_left_surjective₀

/- warning: mul_right_surjective₀ -> mul_right_surjective₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1)))))))) -> (Function.Surjective.{succ u1, succ u1} G₀ G₀ (fun (g : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) g a))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G₀] {a : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) -> (Function.Surjective.{succ u1, succ u1} G₀ G₀ (fun (g : G₀) => HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_1))))) g a))
Case conversion may be inaccurate. Consider using '#align mul_right_surjective₀ mul_right_surjective₀ₓ'. -/
theorem mul_right_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => g * a := fun g =>
  ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel h]⟩
#align mul_right_surjective₀ mul_right_surjective₀

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀] {a b c d : G₀}

/- warning: div_mul_eq_mul_div₀ -> div_mul_eq_mul_div₀ is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_1 : CommGroupWithZero.{u1} G₀] (a : G₀) (b : G₀) (c : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))) a c) b) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) a b) c)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_1 : CommGroupWithZero.{u1} G₀] (a : G₀) (b : G₀) (c : G₀), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (CommGroupWithZero.toDiv.{u1} G₀ _inst_1)) a c) b) (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (CommGroupWithZero.toDiv.{u1} G₀ _inst_1)) (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ (CommGroupWithZero.toGroupWithZero.{u1} G₀ _inst_1)))))) a b) c)
Case conversion may be inaccurate. Consider using '#align div_mul_eq_mul_div₀ div_mul_eq_mul_div₀ₓ'. -/
theorem div_mul_eq_mul_div₀ (a b c : G₀) : a / c * b = a * b / c := by
  simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]
#align div_mul_eq_mul_div₀ div_mul_eq_mul_div₀

end CommGroupWithZero

/-! ### Order dual -/


open OrderDual

instance [h : MulZeroClass α] : MulZeroClass αᵒᵈ :=
  h

instance [h : MulZeroOneClass α] : MulZeroOneClass αᵒᵈ :=
  h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors αᵒᵈ :=
  h

instance [h : SemigroupWithZero α] : SemigroupWithZero αᵒᵈ :=
  h

instance [h : MonoidWithZero α] : MonoidWithZero αᵒᵈ :=
  h

instance [h : CancelMonoidWithZero α] : CancelMonoidWithZero αᵒᵈ :=
  h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ :=
  h

instance [h : CancelCommMonoidWithZero α] : CancelCommMonoidWithZero αᵒᵈ :=
  h

instance [h : GroupWithZero α] : GroupWithZero αᵒᵈ :=
  h

instance [h : CommGroupWithZero α] : CommGroupWithZero αᵒᵈ :=
  h

/-! ### Lexicographic order -/


instance [h : MulZeroClass α] : MulZeroClass (Lex α) :=
  h

instance [h : MulZeroOneClass α] : MulZeroOneClass (Lex α) :=
  h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors (Lex α) :=
  h

instance [h : SemigroupWithZero α] : SemigroupWithZero (Lex α) :=
  h

instance [h : MonoidWithZero α] : MonoidWithZero (Lex α) :=
  h

instance [h : CancelMonoidWithZero α] : CancelMonoidWithZero (Lex α) :=
  h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero (Lex α) :=
  h

instance [h : CancelCommMonoidWithZero α] : CancelCommMonoidWithZero (Lex α) :=
  h

instance [h : GroupWithZero α] : GroupWithZero (Lex α) :=
  h

instance [h : CommGroupWithZero α] : CommGroupWithZero (Lex α) :=
  h


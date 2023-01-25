/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.hom.equiv.units.group_with_zero
! leanprover-community/mathlib commit e3d9ab8faa9dea8f78155c6c27d62a621f4c152d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Equiv.Units.Basic
import Mathbin.Algebra.GroupWithZero.Units.Basic

/-!
# Multiplication by a nonzero element in a `group_with_zero` is a permutation.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {G : Type _}

namespace Equiv

section GroupWithZero

variable [GroupWithZero G]

/- warning: equiv.mul_left₀ -> Equiv.mulLeft₀ is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G] (a : G), (Ne.{succ u1} G a (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (MulZeroClass.toHasZero.{u1} G (MulZeroOneClass.toMulZeroClass.{u1} G (MonoidWithZero.toMulZeroOneClass.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1)))))))) -> (Equiv.Perm.{succ u1} G)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G] (a : G), (Ne.{succ u1} G a (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (MonoidWithZero.toZero.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1))))) -> (Equiv.Perm.{succ u1} G)
Case conversion may be inaccurate. Consider using '#align equiv.mul_left₀ Equiv.mulLeft₀ₓ'. -/
/-- Left multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := false })]
protected def mulLeft₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mulLeft
#align equiv.mul_left₀ Equiv.mulLeft₀

/- warning: mul_left_bijective₀ -> Equiv.mulLeft_bijective₀ is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G] (a : G), (Ne.{succ u1} G a (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (MulZeroClass.toHasZero.{u1} G (MulZeroOneClass.toMulZeroClass.{u1} G (MonoidWithZero.toMulZeroOneClass.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1)))))))) -> (Function.Bijective.{succ u1, succ u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulZeroClass.toHasMul.{u1} G (MulZeroOneClass.toMulZeroClass.{u1} G (MonoidWithZero.toMulZeroOneClass.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1))))) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G] (a : G), (Ne.{succ u1} G a (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (MonoidWithZero.toZero.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1))))) -> (Function.Bijective.{succ u1, succ u1} G G ((fun (x._@.Mathlib.Algebra.Hom.Equiv.Units.GroupWithZero._hyg.76 : G) (x._@.Mathlib.Algebra.Hom.Equiv.Units.GroupWithZero._hyg.78 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulZeroClass.toMul.{u1} G (MulZeroOneClass.toMulZeroClass.{u1} G (MonoidWithZero.toMulZeroOneClass.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1))))) x._@.Mathlib.Algebra.Hom.Equiv.Units.GroupWithZero._hyg.76 x._@.Mathlib.Algebra.Hom.Equiv.Units.GroupWithZero._hyg.78) a))
Case conversion may be inaccurate. Consider using '#align mul_left_bijective₀ Equiv.mulLeft_bijective₀ₓ'. -/
theorem Equiv.mulLeft_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * ·) a : G → G) :=
  (Equiv.mulLeft₀ a ha).Bijective
#align mul_left_bijective₀ Equiv.mulLeft_bijective₀

/- warning: equiv.mul_right₀ -> Equiv.mulRight₀ is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G] (a : G), (Ne.{succ u1} G a (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (MulZeroClass.toHasZero.{u1} G (MulZeroOneClass.toMulZeroClass.{u1} G (MonoidWithZero.toMulZeroOneClass.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1)))))))) -> (Equiv.Perm.{succ u1} G)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G] (a : G), (Ne.{succ u1} G a (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (MonoidWithZero.toZero.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1))))) -> (Equiv.Perm.{succ u1} G)
Case conversion may be inaccurate. Consider using '#align equiv.mul_right₀ Equiv.mulRight₀ₓ'. -/
/-- Right multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := false })]
protected def mulRight₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mulRight
#align equiv.mul_right₀ Equiv.mulRight₀

/- warning: mul_right_bijective₀ -> Equiv.mulRight_bijective₀ is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G] (a : G), (Ne.{succ u1} G a (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (MulZeroClass.toHasZero.{u1} G (MulZeroOneClass.toMulZeroClass.{u1} G (MonoidWithZero.toMulZeroOneClass.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1)))))))) -> (Function.Bijective.{succ u1, succ u1} G G (fun (_x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulZeroClass.toHasMul.{u1} G (MulZeroOneClass.toMulZeroClass.{u1} G (MonoidWithZero.toMulZeroOneClass.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1))))) _x a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : GroupWithZero.{u1} G] (a : G), (Ne.{succ u1} G a (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (MonoidWithZero.toZero.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1))))) -> (Function.Bijective.{succ u1, succ u1} G G (fun (_x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulZeroClass.toMul.{u1} G (MulZeroOneClass.toMulZeroClass.{u1} G (MonoidWithZero.toMulZeroOneClass.{u1} G (GroupWithZero.toMonoidWithZero.{u1} G _inst_1))))) _x a))
Case conversion may be inaccurate. Consider using '#align mul_right_bijective₀ Equiv.mulRight_bijective₀ₓ'. -/
theorem Equiv.mulRight_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * a) : G → G) :=
  (Equiv.mulRight₀ a ha).Bijective
#align mul_right_bijective₀ Equiv.mulRight_bijective₀

end GroupWithZero

end Equiv


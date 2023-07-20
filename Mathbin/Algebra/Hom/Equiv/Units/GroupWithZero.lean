/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathbin.Algebra.Hom.Equiv.Units.Basic
import Mathbin.Algebra.GroupWithZero.Units.Basic

#align_import algebra.hom.equiv.units.group_with_zero from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Multiplication by a nonzero element in a `group_with_zero` is a permutation.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {G : Type _}

namespace Equiv

section GroupWithZero

variable [GroupWithZero G]

#print Equiv.mulLeft₀ /-
/-- Left multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := false })]
protected def mulLeft₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mulLeft
#align equiv.mul_left₀ Equiv.mulLeft₀
-/

#print mulLeft_bijective₀ /-
theorem mulLeft_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * ·) a : G → G) :=
  (Equiv.mulLeft₀ a ha).Bijective
#align mul_left_bijective₀ mulLeft_bijective₀
-/

#print Equiv.mulRight₀ /-
/-- Right multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := false })]
protected def mulRight₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mulRight
#align equiv.mul_right₀ Equiv.mulRight₀
-/

#print mulRight_bijective₀ /-
theorem mulRight_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * a) : G → G) :=
  (Equiv.mulRight₀ a ha).Bijective
#align mul_right_bijective₀ mulRight_bijective₀
-/

end GroupWithZero

end Equiv


/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathbin.Algebra.Hom.Equiv.Units.Basic
import Mathbin.Algebra.GroupWithZero.Units.Basic

/-!
# Multiplication by a nonzero element in a `group_with_zero` is a permutation.
-/


variable {G : Type _}

namespace Equiv

section GroupWithZero

variable [GroupWithZero G]

/-- Left multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := false })]
protected def mulLeft₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mulLeft
#align equiv.mul_left₀ Equiv.mulLeft₀

theorem _root_.mul_left_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * ·) a : G → G) :=
  (Equiv.mulLeft₀ a ha).Bijective
#align equiv._root_.mul_left_bijective₀ equiv._root_.mul_left_bijective₀

/-- Right multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := false })]
protected def mulRight₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mulRight
#align equiv.mul_right₀ Equiv.mulRight₀

theorem _root_.mul_right_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * a) : G → G) :=
  (Equiv.mulRight₀ a ha).Bijective
#align equiv._root_.mul_right_bijective₀ equiv._root_.mul_right_bijective₀

end GroupWithZero

end Equiv


/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.GroupWithZero.Semiconj
import Mathbin.Algebra.Group.Commute
import Mathbin.Tactic.Nontriviality

#align_import algebra.group_with_zero.commute from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Lemmas about commuting elements in a `monoid_with_zero` or a `group_with_zero`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α M₀ G₀ M₀' G₀' F F' : Type _}

variable [MonoidWithZero M₀]

namespace Ring

open scoped Classical

#print Ring.mul_inverse_rev' /-
theorem mul_inverse_rev' {a b : M₀} (h : Commute a b) : inverse (a * b) = inverse b * inverse a :=
  by
  by_cases hab : IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.is_unit_mul_iff.mp hab
    rw [← Units.val_mul, inverse_unit, inverse_unit, inverse_unit, ← Units.val_mul, mul_inv_rev]
  obtain ha | hb := not_and_distrib.mp (mt h.is_unit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, MulZeroClass.mul_zero]
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, MulZeroClass.zero_mul]
#align ring.mul_inverse_rev' Ring.mul_inverse_rev'
-/

#print Ring.mul_inverse_rev /-
theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) :
    Ring.inverse (a * b) = inverse b * inverse a :=
  mul_inverse_rev' (Commute.all _ _)
#align ring.mul_inverse_rev Ring.mul_inverse_rev
-/

end Ring

#print Commute.ring_inverse_ring_inverse /-
theorem Commute.ring_inverse_ring_inverse {a b : M₀} (h : Commute a b) :
    Commute (Ring.inverse a) (Ring.inverse b) :=
  (Ring.mul_inverse_rev' h.symm).symm.trans <|
    (congr_arg _ h.symm.Eq).trans <| Ring.mul_inverse_rev' h
#align commute.ring_inverse_ring_inverse Commute.ring_inverse_ring_inverse
-/

namespace Commute

#print Commute.zero_right /-
@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a
#align commute.zero_right Commute.zero_right
-/

#print Commute.zero_left /-
@[simp]
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a
#align commute.zero_left Commute.zero_left
-/

variable [GroupWithZero G₀] {a b c : G₀}

#print Commute.inv_left_iff₀ /-
@[simp]
theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff₀
#align commute.inv_left_iff₀ Commute.inv_left_iff₀
-/

#print Commute.inv_left₀ /-
theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b :=
  inv_left_iff₀.2 h
#align commute.inv_left₀ Commute.inv_left₀
-/

#print Commute.inv_right_iff₀ /-
@[simp]
theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff₀
#align commute.inv_right_iff₀ Commute.inv_right_iff₀
-/

#print Commute.inv_right₀ /-
theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ :=
  inv_right_iff₀.2 h
#align commute.inv_right₀ Commute.inv_right₀
-/

#print Commute.div_right /-
@[simp]
theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  hab.div_right hac
#align commute.div_right Commute.div_right
-/

#print Commute.div_left /-
@[simp]
theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by
  rw [div_eq_mul_inv]; exact hac.mul_left hbc.inv_left₀
#align commute.div_left Commute.div_left
-/

end Commute


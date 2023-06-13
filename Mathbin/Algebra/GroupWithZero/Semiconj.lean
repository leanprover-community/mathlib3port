/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.group_with_zero.semiconj
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupWithZero.Units.Basic
import Mathbin.Algebra.Group.Semiconj

/-!
# Lemmas about semiconjugate elements in a `group_with_zero`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α M₀ G₀ M₀' G₀' F F' : Type _}

namespace SemiconjBy

#print SemiconjBy.zero_right /-
@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by
  simp only [SemiconjBy, MulZeroClass.mul_zero, MulZeroClass.zero_mul]
#align semiconj_by.zero_right SemiconjBy.zero_right
-/

#print SemiconjBy.zero_left /-
@[simp]
theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by
  simp only [SemiconjBy, MulZeroClass.mul_zero, MulZeroClass.zero_mul]
#align semiconj_by.zero_left SemiconjBy.zero_left
-/

variable [GroupWithZero G₀] {a x y x' y' : G₀}

#print SemiconjBy.inv_symm_left_iff₀ /-
@[simp]
theorem inv_symm_left_iff₀ : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x :=
  by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _
#align semiconj_by.inv_symm_left_iff₀ SemiconjBy.inv_symm_left_iff₀
-/

#print SemiconjBy.inv_symm_left₀ /-
theorem inv_symm_left₀ (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x :=
  SemiconjBy.inv_symm_left_iff₀.2 h
#align semiconj_by.inv_symm_left₀ SemiconjBy.inv_symm_left₀
-/

#print SemiconjBy.inv_right₀ /-
theorem inv_right₀ (h : SemiconjBy a x y) : SemiconjBy a x⁻¹ y⁻¹ :=
  by
  by_cases ha : a = 0
  · simp only [ha, zero_left]
  by_cases hx : x = 0
  · subst x
    simp only [SemiconjBy, MulZeroClass.mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h 
    simp [h.resolve_right ha]
  · have := mul_ne_zero ha hx
    rw [h.eq, mul_ne_zero_iff] at this 
    exact @units_inv_right _ _ _ (Units.mk0 x hx) (Units.mk0 y this.1) h
#align semiconj_by.inv_right₀ SemiconjBy.inv_right₀
-/

#print SemiconjBy.inv_right_iff₀ /-
@[simp]
theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  ⟨fun h => inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩
#align semiconj_by.inv_right_iff₀ SemiconjBy.inv_right_iff₀
-/

#print SemiconjBy.div_right /-
theorem div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x / x') (y / y') := by rw [div_eq_mul_inv, div_eq_mul_inv];
  exact h.mul_right h'.inv_right₀
#align semiconj_by.div_right SemiconjBy.div_right
-/

end SemiconjBy


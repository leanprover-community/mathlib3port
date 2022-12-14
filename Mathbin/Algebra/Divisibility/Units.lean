/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson

! This file was ported from Lean 3 source module algebra.divisibility.units
! leanprover-community/mathlib commit 198161d833f2c01498c39c266b0b3dbe2c7a8c07
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Divisibility.Basic
import Mathbin.Algebra.Group.Units

/-!
# Lemmas about divisibility and units

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/848
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

namespace Units

section Monoid

variable [Monoid α] {a b : α} {u : αˣ}

/-- Elements of the unit group of a monoid represented as elements of the monoid
    divide any element of the monoid. -/
theorem coe_dvd : ↑u ∣ a :=
  ⟨↑u⁻¹ * a, by simp⟩
#align units.coe_dvd Units.coe_dvd

/-- In a monoid, an element `a` divides an element `b` iff `a` divides all
    associates of `b`. -/
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
  Iff.intro (fun ⟨c, Eq⟩ => ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← Eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨c, Eq⟩ => Eq.symm ▸ (dvd_mul_right _ _).mul_right _
#align units.dvd_mul_right Units.dvd_mul_right

/-- In a monoid, an element `a` divides an element `b` iff all associates of `a` divide `b`. -/
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
  Iff.intro (fun ⟨c, Eq⟩ => ⟨↑u * c, Eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans (Dvd.intro (↑u⁻¹) (by rw [mul_assoc, u.mul_inv, mul_one])) h
#align units.mul_right_dvd Units.mul_right_dvd

end Monoid

section CommMonoid

variable [CommMonoid α] {a b : α} {u : αˣ}

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by
  rw [mul_comm]
  apply dvd_mul_right
#align units.dvd_mul_left Units.dvd_mul_left

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
theorem mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b := by
  rw [mul_comm]
  apply mul_right_dvd
#align units.mul_left_dvd Units.mul_left_dvd

end CommMonoid

end Units

namespace IsUnit

section Monoid

variable [Monoid α] {a b u : α} (hu : IsUnit u)

include hu

/-- Units of a monoid divide any element of the monoid. -/
@[simp]
theorem dvd : u ∣ a := by 
  rcases hu with ⟨u, rfl⟩
  apply Units.coe_dvd
#align is_unit.dvd IsUnit.dvd

@[simp]
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_right
#align is_unit.dvd_mul_right IsUnit.dvd_mul_right

/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`.-/
@[simp]
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_right_dvd
#align is_unit.mul_right_dvd IsUnit.mul_right_dvd

end Monoid

section CommMonoid

variable [CommMonoid α] (a b u : α) (hu : IsUnit u)

include hu

/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
@[simp]
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_left
#align is_unit.dvd_mul_left IsUnit.dvd_mul_left

/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
@[simp]
theorem mul_left_dvd : u * a ∣ b ↔ a ∣ b := by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_left_dvd
#align is_unit.mul_left_dvd IsUnit.mul_left_dvd

end CommMonoid

end IsUnit

section CommMonoid

variable [CommMonoid α]

theorem is_unit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1 :=
  ⟨IsUnit.dvd, fun ⟨y, h⟩ => ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩
#align is_unit_iff_dvd_one is_unit_iff_dvd_one

theorem is_unit_iff_forall_dvd {x : α} : IsUnit x ↔ ∀ y, x ∣ y :=
  is_unit_iff_dvd_one.trans ⟨fun h y => h.trans (one_dvd _), fun h => h _⟩
#align is_unit_iff_forall_dvd is_unit_iff_forall_dvd

theorem is_unit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUnit y) : IsUnit x :=
  is_unit_iff_dvd_one.2 <| xy.trans <| is_unit_iff_dvd_one.1 hu
#align is_unit_of_dvd_unit is_unit_of_dvd_unit

/- ./././Mathport/Syntax/Translate/Basic.lean:631:2: warning: expanding binder collection (a «expr ∣ » 1) -/
theorem is_unit_of_dvd_one : ∀ (a) (_ : a ∣ 1), IsUnit (a : α)
  | a, ⟨b, Eq⟩ => ⟨Units.mkOfMulEqOne a b Eq.symm, rfl⟩
#align is_unit_of_dvd_one is_unit_of_dvd_one

theorem not_is_unit_of_not_is_unit_dvd {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b :=
  mt (is_unit_of_dvd_unit hb) ha
#align not_is_unit_of_not_is_unit_dvd not_is_unit_of_not_is_unit_dvd

end CommMonoid


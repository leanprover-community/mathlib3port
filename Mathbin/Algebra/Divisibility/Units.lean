/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson
-/
import Algebra.Divisibility.Basic
import Algebra.Group.Units

#align_import algebra.divisibility.units from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Lemmas about divisibility and units

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

namespace Units

section Monoid

variable [Monoid α] {a b : α} {u : αˣ}

#print Units.coe_dvd /-
/-- Elements of the unit group of a monoid represented as elements of the monoid
    divide any element of the monoid. -/
theorem coe_dvd : ↑u ∣ a :=
  ⟨↑u⁻¹ * a, by simp⟩
#align units.coe_dvd Units.coe_dvd
-/

#print Units.dvd_mul_right /-
/-- In a monoid, an element `a` divides an element `b` iff `a` divides all
    associates of `b`. -/
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
  Iff.intro (fun ⟨c, Eq⟩ => ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← Eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨c, Eq⟩ => Eq.symm ▸ (dvd_mul_right _ _).hMul_right _
#align units.dvd_mul_right Units.dvd_mul_right
-/

#print Units.mul_right_dvd /-
/-- In a monoid, an element `a` divides an element `b` iff all associates of `a` divide `b`. -/
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
  Iff.intro (fun ⟨c, Eq⟩ => ⟨↑u * c, Eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans (Dvd.intro (↑u⁻¹) (by rw [mul_assoc, u.mul_inv, mul_one])) h
#align units.mul_right_dvd Units.mul_right_dvd
-/

end Monoid

section CommMonoid

variable [CommMonoid α] {a b : α} {u : αˣ}

#print Units.dvd_mul_left /-
/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by rw [mul_comm]; apply dvd_mul_right
#align units.dvd_mul_left Units.dvd_mul_left
-/

#print Units.mul_left_dvd /-
/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
theorem mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b := by rw [mul_comm]; apply mul_right_dvd
#align units.mul_left_dvd Units.mul_left_dvd
-/

end CommMonoid

end Units

namespace IsUnit

section Monoid

variable [Monoid α] {a b u : α} (hu : IsUnit u)

#print IsUnit.dvd /-
/-- Units of a monoid divide any element of the monoid. -/
@[simp]
theorem dvd : u ∣ a := by rcases hu with ⟨u, rfl⟩; apply Units.coe_dvd
#align is_unit.dvd IsUnit.dvd
-/

#print IsUnit.dvd_mul_right /-
@[simp]
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b := by rcases hu with ⟨u, rfl⟩; apply Units.dvd_mul_right
#align is_unit.dvd_mul_right IsUnit.dvd_mul_right
-/

#print IsUnit.mul_right_dvd /-
/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`.-/
@[simp]
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b := by rcases hu with ⟨u, rfl⟩; apply Units.mul_right_dvd
#align is_unit.mul_right_dvd IsUnit.mul_right_dvd
-/

end Monoid

section CommMonoid

variable [CommMonoid α] (a b u : α) (hu : IsUnit u)

#print IsUnit.dvd_mul_left /-
/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
@[simp]
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by rcases hu with ⟨u, rfl⟩; apply Units.dvd_mul_left
#align is_unit.dvd_mul_left IsUnit.dvd_mul_left
-/

#print IsUnit.mul_left_dvd /-
/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
@[simp]
theorem mul_left_dvd : u * a ∣ b ↔ a ∣ b := by rcases hu with ⟨u, rfl⟩; apply Units.mul_left_dvd
#align is_unit.mul_left_dvd IsUnit.mul_left_dvd
-/

end CommMonoid

end IsUnit

section CommMonoid

variable [CommMonoid α]

#print isUnit_iff_dvd_one /-
theorem isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1 :=
  ⟨IsUnit.dvd, fun ⟨y, h⟩ => ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩
#align is_unit_iff_dvd_one isUnit_iff_dvd_one
-/

#print isUnit_iff_forall_dvd /-
theorem isUnit_iff_forall_dvd {x : α} : IsUnit x ↔ ∀ y, x ∣ y :=
  isUnit_iff_dvd_one.trans ⟨fun h y => h.trans (one_dvd _), fun h => h _⟩
#align is_unit_iff_forall_dvd isUnit_iff_forall_dvd
-/

#print isUnit_of_dvd_unit /-
theorem isUnit_of_dvd_unit {x y : α} (xy : x ∣ y) (hu : IsUnit y) : IsUnit x :=
  isUnit_iff_dvd_one.2 <| xy.trans <| isUnit_iff_dvd_one.1 hu
#align is_unit_of_dvd_unit isUnit_of_dvd_unit
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (a «expr ∣ » 1) -/
#print isUnit_of_dvd_one /-
theorem isUnit_of_dvd_one : ∀ (a) (_ : a ∣ 1), IsUnit (a : α)
  | a, ⟨b, Eq⟩ => ⟨Units.mkOfMulEqOne a b Eq.symm, rfl⟩
#align is_unit_of_dvd_one isUnit_of_dvd_one
-/

#print not_isUnit_of_not_isUnit_dvd /-
theorem not_isUnit_of_not_isUnit_dvd {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b :=
  mt (isUnit_of_dvd_unit hb) ha
#align not_is_unit_of_not_is_unit_dvd not_isUnit_of_not_isUnit_dvd
-/

end CommMonoid


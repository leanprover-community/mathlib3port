/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland, Aaron Anderson

! This file was ported from Lean 3 source module algebra.divisibility.units
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Divisibility.Basic
import Mathbin.Algebra.Group.Units

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

/- warning: units.dvd_mul_right -> Units.dvd_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} {u : Units.{u1} α _inst_1}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) u))) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} {u : Units.{u1} α _inst_1}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b (Units.val.{u1} α _inst_1 u))) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align units.dvd_mul_right Units.dvd_mul_rightₓ'. -/
/-- In a monoid, an element `a` divides an element `b` iff `a` divides all
    associates of `b`. -/
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
  Iff.intro (fun ⟨c, Eq⟩ => ⟨c * ↑u⁻¹, by rw [← mul_assoc, ← Eq, Units.mul_inv_cancel_right]⟩)
    fun ⟨c, Eq⟩ => Eq.symm ▸ (dvd_mul_right _ _).mul_right _
#align units.dvd_mul_right Units.dvd_mul_right

/- warning: units.mul_right_dvd -> Units.mul_right_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} {u : Units.{u1} α _inst_1}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α _inst_1) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α _inst_1) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α _inst_1) α (coeBase.{succ u1, succ u1} (Units.{u1} α _inst_1) α (Units.hasCoe.{u1} α _inst_1)))) u)) b) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} {u : Units.{u1} α _inst_1}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a (Units.val.{u1} α _inst_1 u)) b) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a b)
Case conversion may be inaccurate. Consider using '#align units.mul_right_dvd Units.mul_right_dvdₓ'. -/
/-- In a monoid, an element `a` divides an element `b` iff all associates of `a` divide `b`. -/
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
  Iff.intro (fun ⟨c, Eq⟩ => ⟨↑u * c, Eq.trans (mul_assoc _ _ _)⟩) fun h =>
    dvd_trans (Dvd.intro (↑u⁻¹) (by rw [mul_assoc, u.mul_inv, mul_one])) h
#align units.mul_right_dvd Units.mul_right_dvd

end Monoid

section CommMonoid

variable [CommMonoid α] {a b : α} {u : αˣ}

/- warning: units.dvd_mul_left -> Units.dvd_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α} {u : Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (coeBase.{succ u1, succ u1} (Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Units.hasCoe.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) u) b)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α} {u : Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Units.val.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) u) b)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align units.dvd_mul_left Units.dvd_mul_leftₓ'. -/
/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b :=
  by
  rw [mul_comm]
  apply dvd_mul_right
#align units.dvd_mul_left Units.dvd_mul_left

/- warning: units.mul_left_dvd -> Units.mul_left_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α} {u : Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (coeBase.{succ u1, succ u1} (Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) α (Units.hasCoe.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) u) a) b) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α} {b : α} {u : Units.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) (Units.val.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) u) a) b) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b)
Case conversion may be inaccurate. Consider using '#align units.mul_left_dvd Units.mul_left_dvdₓ'. -/
/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
theorem mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b :=
  by
  rw [mul_comm]
  apply mul_right_dvd
#align units.mul_left_dvd Units.mul_left_dvd

end CommMonoid

end Units

namespace IsUnit

section Monoid

variable [Monoid α] {a b u : α} (hu : IsUnit u)

include hu

#print IsUnit.dvd /-
/-- Units of a monoid divide any element of the monoid. -/
@[simp]
theorem dvd : u ∣ a := by
  rcases hu with ⟨u, rfl⟩
  apply Units.coe_dvd
#align is_unit.dvd IsUnit.dvd
-/

/- warning: is_unit.dvd_mul_right -> IsUnit.dvd_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} {u : α}, (IsUnit.{u1} α _inst_1 u) -> (Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b u)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} {u : α}, (IsUnit.{u1} α _inst_1 u) -> (Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) b u)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align is_unit.dvd_mul_right IsUnit.dvd_mul_rightₓ'. -/
@[simp]
theorem dvd_mul_right : a ∣ b * u ↔ a ∣ b :=
  by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_right
#align is_unit.dvd_mul_right IsUnit.dvd_mul_right

/- warning: is_unit.mul_right_dvd -> IsUnit.mul_right_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} {u : α}, (IsUnit.{u1} α _inst_1 u) -> (Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a u) b) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Monoid.{u1} α] {a : α} {b : α} {u : α}, (IsUnit.{u1} α _inst_1 u) -> (Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α _inst_1))) a u) b) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α _inst_1)) a b))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_right_dvd IsUnit.mul_right_dvdₓ'. -/
/-- In a monoid, an element a divides an element b iff all associates of `a` divide `b`.-/
@[simp]
theorem mul_right_dvd : a * u ∣ b ↔ a ∣ b :=
  by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_right_dvd
#align is_unit.mul_right_dvd IsUnit.mul_right_dvd

end Monoid

section CommMonoid

variable [CommMonoid α] (a b u : α) (hu : IsUnit u)

include hu

/- warning: is_unit.dvd_mul_left -> IsUnit.dvd_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) (b : α) (u : α), (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) u) -> (Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) u b)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) (b : α) (u : α), (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) u) -> (Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) u b)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align is_unit.dvd_mul_left IsUnit.dvd_mul_leftₓ'. -/
/-- In a commutative monoid, an element `a` divides an element `b` iff `a` divides all left
    associates of `b`. -/
@[simp]
theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b :=
  by
  rcases hu with ⟨u, rfl⟩
  apply Units.dvd_mul_left
#align is_unit.dvd_mul_left IsUnit.dvd_mul_left

/- warning: is_unit.mul_left_dvd -> IsUnit.mul_left_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) (b : α) (u : α), (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) u) -> (Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) u a) b) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α) (b : α) (u : α), (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) u) -> (Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))) u a) b) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a b))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_left_dvd IsUnit.mul_left_dvdₓ'. -/
/-- In a commutative monoid, an element `a` divides an element `b` iff all
  left associates of `a` divide `b`.-/
@[simp]
theorem mul_left_dvd : u * a ∣ b ↔ a ∣ b :=
  by
  rcases hu with ⟨u, rfl⟩
  apply Units.mul_left_dvd
#align is_unit.mul_left_dvd IsUnit.mul_left_dvd

end CommMonoid

end IsUnit

section CommMonoid

variable [CommMonoid α]

/- warning: is_unit_iff_dvd_one -> isUnit_iff_dvd_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {x : α}, Iff (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) x) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) x (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {x : α}, Iff (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) x) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) x (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align is_unit_iff_dvd_one isUnit_iff_dvd_oneₓ'. -/
theorem isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1 :=
  ⟨IsUnit.dvd, fun ⟨y, h⟩ => ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩
#align is_unit_iff_dvd_one isUnit_iff_dvd_one

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

/- warning: is_unit_of_dvd_one -> isUnit_of_dvd_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] (a : α), (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))) -> (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {a : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (Monoid.toSemigroup.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) -> (IsUnit.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) a)
Case conversion may be inaccurate. Consider using '#align is_unit_of_dvd_one isUnit_of_dvd_oneₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a «expr ∣ » 1) -/
theorem isUnit_of_dvd_one : ∀ (a) (_ : a ∣ 1), IsUnit (a : α)
  | a, ⟨b, Eq⟩ => ⟨Units.mkOfMulEqOne a b Eq.symm, rfl⟩
#align is_unit_of_dvd_one isUnit_of_dvd_one

#print not_isUnit_of_not_isUnit_dvd /-
theorem not_isUnit_of_not_isUnit_dvd {a b : α} (ha : ¬IsUnit a) (hb : a ∣ b) : ¬IsUnit b :=
  mt (isUnit_of_dvd_unit hb) ha
#align not_is_unit_of_not_is_unit_dvd not_isUnit_of_not_isUnit_dvd
-/

end CommMonoid


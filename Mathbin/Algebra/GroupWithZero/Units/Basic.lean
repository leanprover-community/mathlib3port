/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module algebra.group_with_zero.units.basic
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupWithZero.Basic
import Mathbin.Algebra.Group.Units
import Mathbin.Tactic.Nontriviality
import Mathbin.Tactic.AssertExists

/-!
# Lemmas about units in a `monoid_with_zero` or a `group_with_zero`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/735
> Any changes to this file require a corresponding PR to mathlib4.

We also define `ring.inverse`, a globally defined function on any ring
(in fact any `monoid_with_zero`), which inverts units and sends non-units to zero.
-/


variable {α M₀ G₀ M₀' G₀' F F' : Type _}

variable [MonoidWithZero M₀]

namespace Units

/- warning: units.ne_zero -> Units.ne_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] (u : Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)), Ne.{succ u1} M₀ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (coeBase.{succ u1, succ u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (Units.hasCoe.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1))))) u) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] (u : Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)), Ne.{succ u1} M₀ (Units.val.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) u) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))
Case conversion may be inaccurate. Consider using '#align units.ne_zero Units.ne_zeroₓ'. -/
/-- An element of the unit group of a nonzero monoid with zero represented as an element
    of the monoid is nonzero. -/
@[simp]
theorem ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) ≠ 0 :=
  left_ne_zero_of_mul_eq_one u.mul_inv
#align units.ne_zero Units.ne_zero

/- warning: units.mul_left_eq_zero -> Units.mul_left_eq_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (u : Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) {a : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (coeBase.{succ u1, succ u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (Units.hasCoe.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1))))) u)) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (u : Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) {a : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) a (Units.val.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) u)) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align units.mul_left_eq_zero Units.mul_left_eq_zeroₓ'. -/
-- We can't use `mul_eq_zero` + `units.ne_zero` in the next two lemmas because we don't assume
-- `nonzero M₀`.
@[simp]
theorem mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩
#align units.mul_left_eq_zero Units.mul_left_eq_zero

/- warning: units.mul_right_eq_zero -> Units.mul_right_eq_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (u : Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) {a : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (coeBase.{succ u1, succ u1} (Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) M₀ (Units.hasCoe.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1))))) u) a) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (u : Units.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)) {a : M₀}, Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (Units.val.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) u) a) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align units.mul_right_eq_zero Units.mul_right_eq_zeroₓ'. -/
@[simp]
theorem mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right u⟩
#align units.mul_right_eq_zero Units.mul_right_eq_zero

end Units

namespace IsUnit

/- warning: is_unit.ne_zero -> IsUnit.ne_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] {a : M₀}, (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) a) -> (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀] {a : M₀}, (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) a) -> (Ne.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align is_unit.ne_zero IsUnit.ne_zeroₓ'. -/
theorem ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a ≠ 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.NeZero
#align is_unit.ne_zero IsUnit.ne_zero

/- warning: is_unit.mul_right_eq_zero -> IsUnit.mul_right_eq_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) a) -> (Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))) (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) a) -> (Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))) (Eq.{succ u1} M₀ b (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_right_eq_zero IsUnit.mul_right_eq_zeroₓ'. -/
theorem mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.mul_right_eq_zero
#align is_unit.mul_right_eq_zero IsUnit.mul_right_eq_zero

/- warning: is_unit.mul_left_eq_zero -> IsUnit.mul_left_eq_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) b) -> (Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) a b) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] {a : M₀} {b : M₀}, (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) b) -> (Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) a b) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))) (Eq.{succ u1} M₀ a (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_left_eq_zero IsUnit.mul_left_eq_zeroₓ'. -/
theorem mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0 :=
  let ⟨u, hu⟩ := hb
  hu ▸ u.mul_left_eq_zero
#align is_unit.mul_left_eq_zero IsUnit.mul_left_eq_zero

end IsUnit

/- warning: is_unit_zero_iff -> isUnit_zero_iff is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀], Iff (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))) (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀], Iff (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))) (Eq.{succ u1} M₀ (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align is_unit_zero_iff isUnit_zero_iffₓ'. -/
@[simp]
theorem isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1 :=
  ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @isUnit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩
#align is_unit_zero_iff isUnit_zero_iff

/- warning: not_is_unit_zero -> not_isUnit_zero is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀], Not (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] [_inst_2 : Nontrivial.{u1} M₀], Not (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align not_is_unit_zero not_isUnit_zeroₓ'. -/
@[simp]
theorem not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀) :=
  mt isUnit_zero_iff.1 zero_ne_one
#align not_is_unit_zero not_isUnit_zero

namespace Ring

open Classical

#print Ring.inverse /-
/-- Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather
than partially) defined inverse function for some purposes, including for calculus.

Note that while this is in the `ring` namespace for brevity, it requires the weaker assumption
`monoid_with_zero M₀` instead of `ring M₀`. -/
noncomputable def inverse : M₀ → M₀ := fun x => if h : IsUnit x then ((h.Unit⁻¹ : M₀ˣ) : M₀) else 0
#align ring.inverse Ring.inverse
-/

#print Ring.inverse_unit /-
/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
@[simp]
theorem inverse_unit (u : M₀ˣ) : inverse (u : M₀) = (u⁻¹ : M₀ˣ) :=
  by
  simp only [Units.isUnit, inverse, dif_pos]
  exact Units.inv_unique rfl
#align ring.inverse_unit Ring.inverse_unit
-/

/- warning: ring.inverse_non_unit -> Ring.inverse_non_unit is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀), (Not (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x)) -> (Eq.{succ u1} M₀ (Ring.inverse.{u1} M₀ _inst_1 x) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀), (Not (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x)) -> (Eq.{succ u1} M₀ (Ring.inverse.{u1} M₀ _inst_1 x) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align ring.inverse_non_unit Ring.inverse_non_unitₓ'. -/
/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp]
theorem inverse_non_unit (x : M₀) (h : ¬IsUnit x) : inverse x = 0 :=
  dif_neg h
#align ring.inverse_non_unit Ring.inverse_non_unit

/- warning: ring.mul_inverse_cancel -> Ring.mul_inverse_cancel is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) x (Ring.inverse.{u1} M₀ _inst_1 x)) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) x (Ring.inverse.{u1} M₀ _inst_1 x)) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ring.mul_inverse_cancel Ring.mul_inverse_cancelₓ'. -/
theorem mul_inverse_cancel (x : M₀) (h : IsUnit x) : x * inverse x = 1 :=
  by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.mul_inv]
#align ring.mul_inverse_cancel Ring.mul_inverse_cancel

/- warning: ring.inverse_mul_cancel -> Ring.inverse_mul_cancel is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (Ring.inverse.{u1} M₀ _inst_1 x) x) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))))))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (Ring.inverse.{u1} M₀ _inst_1 x) x) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ring.inverse_mul_cancel Ring.inverse_mul_cancelₓ'. -/
theorem inverse_mul_cancel (x : M₀) (h : IsUnit x) : inverse x * x = 1 :=
  by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.inv_mul]
#align ring.inverse_mul_cancel Ring.inverse_mul_cancel

/- warning: ring.mul_inverse_cancel_right -> Ring.mul_inverse_cancel_right is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) y x) (Ring.inverse.{u1} M₀ _inst_1 x)) y)
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) y x) (Ring.inverse.{u1} M₀ _inst_1 x)) y)
Case conversion may be inaccurate. Consider using '#align ring.mul_inverse_cancel_right Ring.mul_inverse_cancel_rightₓ'. -/
theorem mul_inverse_cancel_right (x y : M₀) (h : IsUnit x) : y * x * inverse x = y := by
  rw [mul_assoc, mul_inverse_cancel x h, mul_one]
#align ring.mul_inverse_cancel_right Ring.mul_inverse_cancel_right

/- warning: ring.inverse_mul_cancel_right -> Ring.inverse_mul_cancel_right is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) y (Ring.inverse.{u1} M₀ _inst_1 x)) x) y)
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) y (Ring.inverse.{u1} M₀ _inst_1 x)) x) y)
Case conversion may be inaccurate. Consider using '#align ring.inverse_mul_cancel_right Ring.inverse_mul_cancel_rightₓ'. -/
theorem inverse_mul_cancel_right (x y : M₀) (h : IsUnit x) : y * inverse x * x = y := by
  rw [mul_assoc, inverse_mul_cancel x h, mul_one]
#align ring.inverse_mul_cancel_right Ring.inverse_mul_cancel_right

/- warning: ring.mul_inverse_cancel_left -> Ring.mul_inverse_cancel_left is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) x (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (Ring.inverse.{u1} M₀ _inst_1 x) y)) y)
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) x (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (Ring.inverse.{u1} M₀ _inst_1 x) y)) y)
Case conversion may be inaccurate. Consider using '#align ring.mul_inverse_cancel_left Ring.mul_inverse_cancel_leftₓ'. -/
theorem mul_inverse_cancel_left (x y : M₀) (h : IsUnit x) : x * (inverse x * y) = y := by
  rw [← mul_assoc, mul_inverse_cancel x h, one_mul]
#align ring.mul_inverse_cancel_left Ring.mul_inverse_cancel_left

/- warning: ring.inverse_mul_cancel_left -> Ring.inverse_mul_cancel_left is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (Ring.inverse.{u1} M₀ _inst_1 x) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) x y)) y)
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (Ring.inverse.{u1} M₀ _inst_1 x) (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) x y)) y)
Case conversion may be inaccurate. Consider using '#align ring.inverse_mul_cancel_left Ring.inverse_mul_cancel_leftₓ'. -/
theorem inverse_mul_cancel_left (x y : M₀) (h : IsUnit x) : inverse x * (x * y) = y := by
  rw [← mul_assoc, inverse_mul_cancel x h, one_mul]
#align ring.inverse_mul_cancel_left Ring.inverse_mul_cancel_left

/- warning: ring.inverse_mul_eq_iff_eq_mul -> Ring.inverse_mul_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀) (z : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (Ring.inverse.{u1} M₀ _inst_1 x) y) z) (Eq.{succ u1} M₀ y (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) x z)))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀) (z : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) x) -> (Iff (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) (Ring.inverse.{u1} M₀ _inst_1 x) y) z) (Eq.{succ u1} M₀ y (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) x z)))
Case conversion may be inaccurate. Consider using '#align ring.inverse_mul_eq_iff_eq_mul Ring.inverse_mul_eq_iff_eq_mulₓ'. -/
theorem inverse_mul_eq_iff_eq_mul (x y z : M₀) (h : IsUnit x) : inverse x * y = z ↔ y = x * z :=
  ⟨fun h1 => by rw [← h1, mul_inverse_cancel_left _ _ h], fun h1 => by
    rw [h1, inverse_mul_cancel_left _ _ h]⟩
#align ring.inverse_mul_eq_iff_eq_mul Ring.inverse_mul_eq_iff_eq_mul

/- warning: ring.eq_mul_inverse_iff_mul_eq -> Ring.eq_mul_inverse_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀) (z : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) z) -> (Iff (Eq.{succ u1} M₀ x (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) y (Ring.inverse.{u1} M₀ _inst_1 z))) (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toHasMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) x z) y))
but is expected to have type
  forall {M₀ : Type.{u1}} [_inst_1 : MonoidWithZero.{u1} M₀] (x : M₀) (y : M₀) (z : M₀), (IsUnit.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1) z) -> (Iff (Eq.{succ u1} M₀ x (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) y (Ring.inverse.{u1} M₀ _inst_1 z))) (Eq.{succ u1} M₀ (HMul.hMul.{u1, u1, u1} M₀ M₀ M₀ (instHMul.{u1} M₀ (MulZeroClass.toMul.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1)))) x z) y))
Case conversion may be inaccurate. Consider using '#align ring.eq_mul_inverse_iff_mul_eq Ring.eq_mul_inverse_iff_mul_eqₓ'. -/
theorem eq_mul_inverse_iff_mul_eq (x y z : M₀) (h : IsUnit z) : x = y * inverse z ↔ x * z = y :=
  ⟨fun h1 => by rw [h1, inverse_mul_cancel_right _ _ h], fun h1 => by
    rw [← h1, mul_inverse_cancel_right _ _ h]⟩
#align ring.eq_mul_inverse_iff_mul_eq Ring.eq_mul_inverse_iff_mul_eq

variable (M₀)

/- warning: ring.inverse_one -> Ring.inverse_one is a dubious translation:
lean 3 declaration is
  forall (M₀ : Type.{u1}) [_inst_1 : MonoidWithZero.{u1} M₀], Eq.{succ u1} M₀ (Ring.inverse.{u1} M₀ _inst_1 (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))) (OfNat.ofNat.{u1} M₀ 1 (OfNat.mk.{u1} M₀ 1 (One.one.{u1} M₀ (MulOneClass.toHasOne.{u1} M₀ (MulZeroOneClass.toMulOneClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))
but is expected to have type
  forall (M₀ : Type.{u1}) [_inst_1 : MonoidWithZero.{u1} M₀], Eq.{succ u1} M₀ (Ring.inverse.{u1} M₀ _inst_1 (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1))))) (OfNat.ofNat.{u1} M₀ 1 (One.toOfNat1.{u1} M₀ (Monoid.toOne.{u1} M₀ (MonoidWithZero.toMonoid.{u1} M₀ _inst_1))))
Case conversion may be inaccurate. Consider using '#align ring.inverse_one Ring.inverse_oneₓ'. -/
@[simp]
theorem inverse_one : inverse (1 : M₀) = 1 :=
  inverse_unit 1
#align ring.inverse_one Ring.inverse_one

/- warning: ring.inverse_zero -> Ring.inverse_zero is a dubious translation:
lean 3 declaration is
  forall (M₀ : Type.{u1}) [_inst_1 : MonoidWithZero.{u1} M₀], Eq.{succ u1} M₀ (Ring.inverse.{u1} M₀ _inst_1 (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))) (OfNat.ofNat.{u1} M₀ 0 (OfNat.mk.{u1} M₀ 0 (Zero.zero.{u1} M₀ (MulZeroClass.toHasZero.{u1} M₀ (MulZeroOneClass.toMulZeroClass.{u1} M₀ (MonoidWithZero.toMulZeroOneClass.{u1} M₀ _inst_1))))))
but is expected to have type
  forall (M₀ : Type.{u1}) [_inst_1 : MonoidWithZero.{u1} M₀], Eq.{succ u1} M₀ (Ring.inverse.{u1} M₀ _inst_1 (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))) (OfNat.ofNat.{u1} M₀ 0 (Zero.toOfNat0.{u1} M₀ (MonoidWithZero.toZero.{u1} M₀ _inst_1)))
Case conversion may be inaccurate. Consider using '#align ring.inverse_zero Ring.inverse_zeroₓ'. -/
@[simp]
theorem inverse_zero : inverse (0 : M₀) = 0 :=
  by
  nontriviality
  exact inverse_non_unit _ not_isUnit_zero
#align ring.inverse_zero Ring.inverse_zero

variable {M₀}

end Ring

#print IsUnit.ring_inverse /-
theorem IsUnit.ring_inverse {a : M₀} : IsUnit a → IsUnit (Ring.inverse a)
  | ⟨u, hu⟩ => hu ▸ ⟨u⁻¹, (Ring.inverse_unit u).symm⟩
#align is_unit.ring_inverse IsUnit.ring_inverse
-/

#print isUnit_ring_inverse /-
@[simp]
theorem isUnit_ring_inverse {a : M₀} : IsUnit (Ring.inverse a) ↔ IsUnit a :=
  ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert h
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_isUnit_zero, IsUnit.ring_inverse⟩
#align is_unit_ring_inverse isUnit_ring_inverse
-/

namespace Units

variable [GroupWithZero G₀]

variable {a b : G₀}

/- warning: units.mk0 -> Units.mk0 is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (a : G₀), (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) -> (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (a : G₀), (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) -> (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))
Case conversion may be inaccurate. Consider using '#align units.mk0 Units.mk0ₓ'. -/
/-- Embed a non-zero element of a `group_with_zero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : G₀) (ha : a ≠ 0) : G₀ˣ :=
  ⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩
#align units.mk0 Units.mk0

/- warning: units.mk0_one -> Units.mk0_one is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (h : optParam.{0} (Ne.{succ u1} G₀ (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (one_ne_zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))) (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))) (NeZero.one.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) (GroupWithZero.to_nontrivial.{u1} G₀ _inst_2)))), Eq.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.mk0.{u1} G₀ _inst_2 (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))) h) (OfNat.ofNat.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) 1 (OfNat.mk.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) 1 (One.one.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (MulOneClass.toHasOne.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.mulOneClass.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (h : optParam.{0} (Ne.{succ u1} G₀ (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (InvOneClass.toOne.{u1} G₀ (DivInvOneMonoid.toInvOneClass.{u1} G₀ (DivisionMonoid.toDivInvOneMonoid.{u1} G₀ (GroupWithZero.toDivisionMonoid.{u1} G₀ _inst_2)))))) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (one_ne_zero.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) (InvOneClass.toOne.{u1} G₀ (DivInvOneMonoid.toInvOneClass.{u1} G₀ (DivisionMonoid.toDivInvOneMonoid.{u1} G₀ (GroupWithZero.toDivisionMonoid.{u1} G₀ _inst_2)))) (NeZero.one.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) (GroupWithZero.toNontrivial.{u1} G₀ _inst_2)))), Eq.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.mk0.{u1} G₀ _inst_2 (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (InvOneClass.toOne.{u1} G₀ (DivInvOneMonoid.toInvOneClass.{u1} G₀ (DivisionMonoid.toDivInvOneMonoid.{u1} G₀ (GroupWithZero.toDivisionMonoid.{u1} G₀ _inst_2)))))) h) (OfNat.ofNat.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) 1 (One.toOfNat1.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (InvOneClass.toOne.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (DivInvOneMonoid.toInvOneClass.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (DivisionMonoid.toDivInvOneMonoid.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Group.toDivisionMonoid.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.instGroupUnits.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))))
Case conversion may be inaccurate. Consider using '#align units.mk0_one Units.mk0_oneₓ'. -/
@[simp]
theorem mk0_one (h := one_ne_zero) : mk0 (1 : G₀) h = 1 :=
  by
  ext
  rfl
#align units.mk0_one Units.mk0_one

/- warning: units.coe_mk0 -> Units.val_mk0 is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀} (h : Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))), Eq.{succ u1} G₀ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (coeBase.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (Units.hasCoe.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))) (Units.mk0.{u1} G₀ _inst_2 a h)) a
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀} (h : Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))), Eq.{succ u1} G₀ (Units.val.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) (Units.mk0.{u1} G₀ _inst_2 a h)) a
Case conversion may be inaccurate. Consider using '#align units.coe_mk0 Units.val_mk0ₓ'. -/
@[simp]
theorem val_mk0 {a : G₀} (h : a ≠ 0) : (mk0 a h : G₀) = a :=
  rfl
#align units.coe_mk0 Units.val_mk0

/- warning: units.mk0_coe -> Units.mk0_val is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (u : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (h : Ne.{succ u1} G₀ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (coeBase.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (Units.hasCoe.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))) u) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))), Eq.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.mk0.{u1} G₀ _inst_2 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (coeBase.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (Units.hasCoe.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))) u) h) u
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (u : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (h : Ne.{succ u1} G₀ (Units.val.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) u) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))), Eq.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.mk0.{u1} G₀ _inst_2 (Units.val.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) u) h) u
Case conversion may be inaccurate. Consider using '#align units.mk0_coe Units.mk0_valₓ'. -/
@[simp]
theorem mk0_val (u : G₀ˣ) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
  Units.ext rfl
#align units.mk0_coe Units.mk0_val

/- warning: units.mul_inv' -> Units.mul_inv' is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (u : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (coeBase.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (Units.hasCoe.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))) u) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_2)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (coeBase.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (Units.hasCoe.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))) u))) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (u : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (Units.val.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) u) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_2) (Units.val.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) u))) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (InvOneClass.toOne.{u1} G₀ (DivInvOneMonoid.toInvOneClass.{u1} G₀ (DivisionMonoid.toDivInvOneMonoid.{u1} G₀ (GroupWithZero.toDivisionMonoid.{u1} G₀ _inst_2))))))
Case conversion may be inaccurate. Consider using '#align units.mul_inv' Units.mul_inv'ₓ'. -/
@[simp]
theorem mul_inv' (u : G₀ˣ) : (u : G₀) * u⁻¹ = 1 :=
  mul_inv_cancel u.NeZero
#align units.mul_inv' Units.mul_inv'

/- warning: units.inv_mul' -> Units.inv_mul' is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (u : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_2)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (coeBase.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (Units.hasCoe.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))) u)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (coeBase.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (Units.hasCoe.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))) u)) (OfNat.ofNat.{u1} G₀ 1 (OfNat.mk.{u1} G₀ 1 (One.one.{u1} G₀ (MulOneClass.toHasOne.{u1} G₀ (MulZeroOneClass.toMulOneClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (u : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))), Eq.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_2) (Units.val.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) u)) (Units.val.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) u)) (OfNat.ofNat.{u1} G₀ 1 (One.toOfNat1.{u1} G₀ (InvOneClass.toOne.{u1} G₀ (DivInvOneMonoid.toInvOneClass.{u1} G₀ (DivisionMonoid.toDivInvOneMonoid.{u1} G₀ (GroupWithZero.toDivisionMonoid.{u1} G₀ _inst_2))))))
Case conversion may be inaccurate. Consider using '#align units.inv_mul' Units.inv_mul'ₓ'. -/
@[simp]
theorem inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 :=
  inv_mul_cancel u.NeZero
#align units.inv_mul' Units.inv_mul'

/- warning: units.mk0_inj -> Units.mk0_inj is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀} (ha : Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (hb : Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))), Iff (Eq.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.mk0.{u1} G₀ _inst_2 a ha) (Units.mk0.{u1} G₀ _inst_2 b hb)) (Eq.{succ u1} G₀ a b)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀} (ha : Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (hb : Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))), Iff (Eq.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.mk0.{u1} G₀ _inst_2 a ha) (Units.mk0.{u1} G₀ _inst_2 b hb)) (Eq.{succ u1} G₀ a b)
Case conversion may be inaccurate. Consider using '#align units.mk0_inj Units.mk0_injₓ'. -/
@[simp]
theorem mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) : Units.mk0 a ha = Units.mk0 b hb ↔ a = b :=
  ⟨fun h => by injection h, fun h => Units.ext h⟩
#align units.mk0_inj Units.mk0_inj

/- warning: units.exists0 -> Units.exists0 is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {p : (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) -> Prop}, Iff (Exists.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (fun (g : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) => p g)) (Exists.{succ u1} G₀ (fun (g : G₀) => Exists.{0} (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (fun (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) => p (Units.mk0.{u1} G₀ _inst_2 g hg))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {p : (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) -> Prop}, Iff (Exists.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (fun (g : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) => p g)) (Exists.{succ u1} G₀ (fun (g : G₀) => Exists.{0} (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (fun (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) => p (Units.mk0.{u1} G₀ _inst_2 g hg))))
Case conversion may be inaccurate. Consider using '#align units.exists0 Units.exists0ₓ'. -/
/-- In a group with zero, an existential over a unit can be rewritten in terms of `units.mk0`. -/
theorem exists0 {p : G₀ˣ → Prop} : (∃ g : G₀ˣ, p g) ↔ ∃ (g : G₀)(hg : g ≠ 0), p (Units.mk0 g hg) :=
  ⟨fun ⟨g, pg⟩ => ⟨g, g.NeZero, (g.mk0_coe g.NeZero).symm ▸ pg⟩, fun ⟨g, hg, pg⟩ =>
    ⟨Units.mk0 g hg, pg⟩⟩
#align units.exists0 Units.exists0

/- warning: units.exists0' -> Units.exists0' is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {p : forall (g : G₀), (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) -> Prop}, Iff (Exists.{succ u1} G₀ (fun (g : G₀) => Exists.{0} (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (fun (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) => p g hg))) (Exists.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (fun (g : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) => p ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (coeBase.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (Units.hasCoe.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))) g) (Units.ne_zero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2) (GroupWithZero.to_nontrivial.{u1} G₀ _inst_2) g)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {p : forall (g : G₀), (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) -> Prop}, Iff (Exists.{succ u1} G₀ (fun (g : G₀) => Exists.{0} (Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (fun (hg : Ne.{succ u1} G₀ g (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) => p g hg))) (Exists.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (fun (g : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) => p (Units.val.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) g) (Units.ne_zero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2) (GroupWithZero.toNontrivial.{u1} G₀ _inst_2) g)))
Case conversion may be inaccurate. Consider using '#align units.exists0' Units.exists0'ₓ'. -/
/-- An alternative version of `units.exists0`. This one is useful if Lean cannot
figure out `p` when using `units.exists0` from right to left. -/
theorem exists0' {p : ∀ g : G₀, g ≠ 0 → Prop} :
    (∃ (g : G₀)(hg : g ≠ 0), p g hg) ↔ ∃ g : G₀ˣ, p g g.NeZero :=
  Iff.trans (by simp_rw [coe_mk0]) exists0.symm
#align units.exists0' Units.exists0'

/- warning: units.exists_iff_ne_zero -> Units.exists_iff_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {x : G₀}, Iff (Exists.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (fun (u : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) => Eq.{succ u1} G₀ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (coeBase.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (Units.hasCoe.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))) u) x)) (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {x : G₀}, Iff (Exists.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (fun (u : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) => Eq.{succ u1} G₀ (Units.val.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) u) x)) (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))
Case conversion may be inaccurate. Consider using '#align units.exists_iff_ne_zero Units.exists_iff_ne_zeroₓ'. -/
@[simp]
theorem exists_iff_ne_zero {x : G₀} : (∃ u : G₀ˣ, ↑u = x) ↔ x ≠ 0 := by simp [exists0]
#align units.exists_iff_ne_zero Units.exists_iff_ne_zero

/- warning: group_with_zero.eq_zero_or_unit -> GroupWithZero.eq_zero_or_unit is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (a : G₀), Or (Eq.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (Exists.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (fun (u : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) => Eq.{succ u1} G₀ a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (coeBase.{succ u1, succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) G₀ (Units.hasCoe.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))) u)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (a : G₀), Or (Eq.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (Exists.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (fun (u : Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) => Eq.{succ u1} G₀ a (Units.val.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) u)))
Case conversion may be inaccurate. Consider using '#align group_with_zero.eq_zero_or_unit GroupWithZero.eq_zero_or_unitₓ'. -/
theorem GroupWithZero.eq_zero_or_unit (a : G₀) : a = 0 ∨ ∃ u : G₀ˣ, a = u :=
  by
  by_cases h : a = 0
  · left
    exact h
  · right
    simpa only [eq_comm] using units.exists_iff_ne_zero.mpr h
#align group_with_zero.eq_zero_or_unit GroupWithZero.eq_zero_or_unit

end Units

section GroupWithZero

variable [GroupWithZero G₀] {a b c : G₀}

/- warning: is_unit.mk0 -> IsUnit.mk0 is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (x : G₀), (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) -> (IsUnit.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) x)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (x : G₀), (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) -> (IsUnit.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) x)
Case conversion may be inaccurate. Consider using '#align is_unit.mk0 IsUnit.mk0ₓ'. -/
theorem IsUnit.mk0 (x : G₀) (hx : x ≠ 0) : IsUnit x :=
  (Units.mk0 x hx).IsUnit
#align is_unit.mk0 IsUnit.mk0

/- warning: is_unit_iff_ne_zero -> isUnit_iff_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀}, Iff (IsUnit.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) a) (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀}, Iff (IsUnit.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) a) (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))
Case conversion may be inaccurate. Consider using '#align is_unit_iff_ne_zero isUnit_iff_ne_zeroₓ'. -/
theorem isUnit_iff_ne_zero : IsUnit a ↔ a ≠ 0 :=
  Units.exists_iff_ne_zero
#align is_unit_iff_ne_zero isUnit_iff_ne_zero

alias isUnit_iff_ne_zero ↔ _ Ne.isUnit

attribute [protected] Ne.isUnit

/- warning: group_with_zero.no_zero_divisors -> GroupWithZero.noZeroDivisors is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀], NoZeroDivisors.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))) (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀], NoZeroDivisors.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))) (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))
Case conversion may be inaccurate. Consider using '#align group_with_zero.no_zero_divisors GroupWithZero.noZeroDivisorsₓ'. -/
-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.noZeroDivisors : NoZeroDivisors G₀ :=
  { (‹_› : GroupWithZero G₀) with
    eq_zero_or_eq_zero_of_mul_eq_zero := fun a b h =>
      by
      contrapose! h
      exact (Units.mk0 a h.1 * Units.mk0 b h.2).NeZero }
#align group_with_zero.no_zero_divisors GroupWithZero.noZeroDivisors

#print GroupWithZero.cancelMonoidWithZero /-
-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.cancelMonoidWithZero : CancelMonoidWithZero G₀ :=
  {
    (‹_› :
      GroupWithZero
        G₀) with
    mul_left_cancel_of_ne_zero := fun x y z hx h => by
      rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z]
    mul_right_cancel_of_ne_zero := fun x y z hy h => by
      rw [← mul_inv_cancel_right₀ hy x, h, mul_inv_cancel_right₀ hy z] }
#align group_with_zero.cancel_monoid_with_zero GroupWithZero.cancelMonoidWithZero
-/

/- warning: units.mk0_mul -> Units.mk0_mul is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (x : G₀) (y : G₀) (hxy : Ne.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) x y) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))), Eq.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.mk0.{u1} G₀ _inst_2 (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) x y) hxy) (HMul.hMul.{u1, u1, u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (instHMul.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (MulOneClass.toHasMul.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.mulOneClass.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (Units.mk0.{u1} G₀ _inst_2 x (And.left (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (Ne.{succ u1} G₀ y (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (Iff.mp (Ne.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) x y) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (And (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (Ne.{succ u1} G₀ y (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))))) (mul_ne_zero_iff.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (GroupWithZero.noZeroDivisors.{u1} G₀ _inst_2) x y) hxy))) (Units.mk0.{u1} G₀ _inst_2 y (And.right (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (Ne.{succ u1} G₀ y (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (Iff.mp (Ne.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toHasMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) x y) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (And (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (Ne.{succ u1} G₀ y (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))))) (mul_ne_zero_iff.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (GroupWithZero.noZeroDivisors.{u1} G₀ _inst_2) x y) hxy))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (x : G₀) (y : G₀) (hxy : Ne.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) x y) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))), Eq.{succ u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.mk0.{u1} G₀ _inst_2 (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) x y) hxy) (HMul.hMul.{u1, u1, u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (instHMul.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (MulOneClass.toMul.{u1} (Units.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (Units.instMulOneClassUnits.{u1} G₀ (MonoidWithZero.toMonoid.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (Units.mk0.{u1} G₀ _inst_2 x (And.left (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MulZeroClass.toZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))) (Ne.{succ u1} G₀ y (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MulZeroClass.toZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))) (Iff.mp (Ne.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) x y) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MulZeroClass.toZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))) (And (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MulZeroClass.toZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))) (Ne.{succ u1} G₀ y (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MulZeroClass.toZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (mul_ne_zero_iff.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (GroupWithZero.noZeroDivisors.{u1} G₀ _inst_2) x y) hxy))) (Units.mk0.{u1} G₀ _inst_2 y (And.right (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MulZeroClass.toZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))) (Ne.{succ u1} G₀ y (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MulZeroClass.toZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))) (Iff.mp (Ne.{succ u1} G₀ (HMul.hMul.{u1, u1, u1} G₀ G₀ G₀ (instHMul.{u1} G₀ (MulZeroClass.toMul.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) x y) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MulZeroClass.toZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))) (And (Ne.{succ u1} G₀ x (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MulZeroClass.toZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))) (Ne.{succ u1} G₀ y (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MulZeroClass.toZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (mul_ne_zero_iff.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))) (GroupWithZero.noZeroDivisors.{u1} G₀ _inst_2) x y) hxy))))
Case conversion may be inaccurate. Consider using '#align units.mk0_mul Units.mk0_mulₓ'. -/
-- Can't be put next to the other `mk0` lemmas because it depends on the
-- `no_zero_divisors` instance, which depends on `mk0`.
@[simp]
theorem Units.mk0_mul (x y : G₀) (hxy) :
    Units.mk0 (x * y) hxy =
      Units.mk0 x (mul_ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2 :=
  by
  ext
  rfl
#align units.mk0_mul Units.mk0_mul

/- warning: div_ne_zero -> div_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) -> (Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) -> (Ne.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_2))) a b) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) -> (Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) -> (Ne.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_2)) a b) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))
Case conversion may be inaccurate. Consider using '#align div_ne_zero div_ne_zeroₓ'. -/
theorem div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 :=
  by
  rw [div_eq_mul_inv]
  exact mul_ne_zero ha (inv_ne_zero hb)
#align div_ne_zero div_ne_zero

/- warning: div_eq_zero_iff -> div_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, Iff (Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_2))) a b) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (Or (Eq.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (Eq.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, Iff (Eq.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_2)) a b) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (Or (Eq.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (Eq.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))
Case conversion may be inaccurate. Consider using '#align div_eq_zero_iff div_eq_zero_iffₓ'. -/
@[simp]
theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0 := by simp [div_eq_mul_inv]
#align div_eq_zero_iff div_eq_zero_iff

/- warning: div_ne_zero_iff -> div_ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, Iff (Ne.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (DivInvMonoid.toHasDiv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_2))) a b) (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (And (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))) (Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (OfNat.mk.{u1} G₀ 0 (Zero.zero.{u1} G₀ (MulZeroClass.toHasZero.{u1} G₀ (MulZeroOneClass.toMulZeroClass.{u1} G₀ (MonoidWithZero.toMulZeroOneClass.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)))))))))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] {a : G₀} {b : G₀}, Iff (Ne.{succ u1} G₀ (HDiv.hDiv.{u1, u1, u1} G₀ G₀ G₀ (instHDiv.{u1} G₀ (GroupWithZero.toDiv.{u1} G₀ _inst_2)) a b) (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (And (Ne.{succ u1} G₀ a (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))) (Ne.{succ u1} G₀ b (OfNat.ofNat.{u1} G₀ 0 (Zero.toOfNat0.{u1} G₀ (MonoidWithZero.toZero.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2))))))
Case conversion may be inaccurate. Consider using '#align div_ne_zero_iff div_ne_zero_iffₓ'. -/
theorem div_ne_zero_iff : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  div_eq_zero_iff.Not.trans not_or
#align div_ne_zero_iff div_ne_zero_iff

/- warning: ring.inverse_eq_inv -> Ring.inverse_eq_inv is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (Ring.inverse.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2) a) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_2)) a)
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀] (a : G₀), Eq.{succ u1} G₀ (Ring.inverse.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2) a) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_2) a)
Case conversion may be inaccurate. Consider using '#align ring.inverse_eq_inv Ring.inverse_eq_invₓ'. -/
theorem Ring.inverse_eq_inv (a : G₀) : Ring.inverse a = a⁻¹ :=
  by
  obtain rfl | ha := eq_or_ne a 0
  · simp
  · exact Ring.inverse_unit (Units.mk0 a ha)
#align ring.inverse_eq_inv Ring.inverse_eq_inv

/- warning: ring.inverse_eq_inv' -> Ring.inverse_eq_inv' is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀], Eq.{succ u1} (G₀ -> G₀) (Ring.inverse.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) (Inv.inv.{u1} G₀ (DivInvMonoid.toHasInv.{u1} G₀ (GroupWithZero.toDivInvMonoid.{u1} G₀ _inst_2)))
but is expected to have type
  forall {G₀ : Type.{u1}} [_inst_2 : GroupWithZero.{u1} G₀], Eq.{succ u1} (G₀ -> G₀) (Ring.inverse.{u1} G₀ (GroupWithZero.toMonoidWithZero.{u1} G₀ _inst_2)) (Inv.inv.{u1} G₀ (GroupWithZero.toInv.{u1} G₀ _inst_2))
Case conversion may be inaccurate. Consider using '#align ring.inverse_eq_inv' Ring.inverse_eq_inv'ₓ'. -/
@[simp]
theorem Ring.inverse_eq_inv' : (Ring.inverse : G₀ → G₀) = Inv.inv :=
  funext Ring.inverse_eq_inv
#align ring.inverse_eq_inv' Ring.inverse_eq_inv'

end GroupWithZero

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

#print CommGroupWithZero.cancelCommMonoidWithZero /-
-- see Note [lower instance priority]
instance (priority := 10) CommGroupWithZero.cancelCommMonoidWithZero :
    CancelCommMonoidWithZero G₀ :=
  { GroupWithZero.cancelMonoidWithZero, CommGroupWithZero.toCommMonoidWithZero G₀ with }
#align comm_group_with_zero.cancel_comm_monoid_with_zero CommGroupWithZero.cancelCommMonoidWithZero
-/

#print CommGroupWithZero.toDivisionCommMonoid /-
-- See note [lower instance priority]
instance (priority := 100) CommGroupWithZero.toDivisionCommMonoid : DivisionCommMonoid G₀ :=
  { ‹CommGroupWithZero G₀›, GroupWithZero.toDivisionMonoid with }
#align comm_group_with_zero.to_division_comm_monoid CommGroupWithZero.toDivisionCommMonoid
-/

end CommGroupWithZero

section NoncomputableDefs

open Classical

variable {M : Type _} [Nontrivial M]

/- warning: group_with_zero_of_is_unit_or_eq_zero -> groupWithZeroOfIsUnitOrEqZero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : Nontrivial.{u1} M] [hM : MonoidWithZero.{u1} M], (forall (a : M), Or (IsUnit.{u1} M (MonoidWithZero.toMonoid.{u1} M hM) a) (Eq.{succ u1} M a (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M hM)))))))) -> (GroupWithZero.{u1} M)
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : Nontrivial.{u1} M] [hM : MonoidWithZero.{u1} M], (forall (a : M), Or (IsUnit.{u1} M (MonoidWithZero.toMonoid.{u1} M hM) a) (Eq.{succ u1} M a (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (MonoidWithZero.toZero.{u1} M hM))))) -> (GroupWithZero.{u1} M)
Case conversion may be inaccurate. Consider using '#align group_with_zero_of_is_unit_or_eq_zero groupWithZeroOfIsUnitOrEqZeroₓ'. -/
/-- Constructs a `group_with_zero` structure on a `monoid_with_zero`
  consisting only of units and 0. -/
noncomputable def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : GroupWithZero M :=
  { hM with
    inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).Unit⁻¹
    inv_zero := dif_pos rfl
    mul_inv_cancel := fun a h0 =>
      by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).Unit⁻¹) = 1
      rw [dif_neg h0, Units.mul_inv_eq_iff_eq_mul, one_mul, IsUnit.unit_spec]
    exists_pair_ne := Nontrivial.exists_pair_ne }
#align group_with_zero_of_is_unit_or_eq_zero groupWithZeroOfIsUnitOrEqZero

/- warning: comm_group_with_zero_of_is_unit_or_eq_zero -> commGroupWithZeroOfIsUnitOrEqZero is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : Nontrivial.{u1} M] [hM : CommMonoidWithZero.{u1} M], (forall (a : M), Or (IsUnit.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M hM)) a) (Eq.{succ u1} M a (OfNat.ofNat.{u1} M 0 (OfNat.mk.{u1} M 0 (Zero.zero.{u1} M (MulZeroClass.toHasZero.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M hM))))))))) -> (CommGroupWithZero.{u1} M)
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : Nontrivial.{u1} M] [hM : CommMonoidWithZero.{u1} M], (forall (a : M), Or (IsUnit.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M hM)) a) (Eq.{succ u1} M a (OfNat.ofNat.{u1} M 0 (Zero.toOfNat0.{u1} M (CommMonoidWithZero.toZero.{u1} M hM))))) -> (CommGroupWithZero.{u1} M)
Case conversion may be inaccurate. Consider using '#align comm_group_with_zero_of_is_unit_or_eq_zero commGroupWithZeroOfIsUnitOrEqZeroₓ'. -/
/-- Constructs a `comm_group_with_zero` structure on a `comm_monoid_with_zero`
  consisting only of units and 0. -/
noncomputable def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }
#align comm_group_with_zero_of_is_unit_or_eq_zero commGroupWithZeroOfIsUnitOrEqZero

end NoncomputableDefs

-- Guard against import creep
assert_not_exists Multiplicative

